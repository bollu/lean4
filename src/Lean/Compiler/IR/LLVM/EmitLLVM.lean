/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat
-/

import Lean.Data.HashMap
import Lean.Runtime
import Lean.Compiler.NameMangling
import Lean.Compiler.ExportAttr
import Lean.Compiler.InitAttr
import Lean.Compiler.IR.CompilerM
import Lean.Compiler.IR.EmitUtil
import Lean.Compiler.IR.NormIds
import Lean.Compiler.IR.SimpCase
import Lean.Compiler.IR.Boxing
import Lean.Compiler.IR.ResetReuse
import Lean.Compiler.IR.LLVM.LLVMBindings
import Lean.Compiler.IR.LLVM.CodeGeneratedBy

open Lean.IR.ExplicitBoxing (isBoxedName)

namespace Lean.IR

def leanMainFn := "_lean_main"

namespace LLVM
-- TODO(bollu): instantiate target triple and find out what size_t is.
def size_tType (llvmctx : LLVM.Context) : IO (LLVM.LLVMType llvmctx) :=
  LLVM.i64Type llvmctx
end LLVM

namespace EmitLLVM

structure Context (llvmctx : LLVM.Context) where
  env        : Environment
  options    : Options
  modName    : Name
  jpMap      : JPParamsMap := {}
  mainFn     : FunId := default
  mainParams : Array Param := #[]
  llvmmodule : LLVM.Module llvmctx
  builder    : LLVM.Builder llvmctx

structure State (llvmctx : LLVM.Context) where
  var2val : HashMap VarId (LLVM.LLVMType llvmctx × LLVM.Value llvmctx)
  jp2bb   : HashMap JoinPointId (LLVM.BasicBlock llvmctx)

abbrev Error := String

abbrev M (llvmctx : LLVM.Context) :=
  StateRefT (State llvmctx) (ReaderT (Context llvmctx) (ExceptT Error IO))

instance : Inhabited (M llvmctx α) where
  default := throw "Error: inhabitant"

def addVartoState (x : VarId) (v : LLVM.Value llvmctx) (ty : LLVM.LLVMType llvmctx) : M llvmctx Unit := do
  modify (fun s => { s with var2val := s.var2val.insert x (ty, v) }) -- add new variable

def addJpTostate (jp : JoinPointId) (bb : LLVM.BasicBlock llvmctx) : M llvmctx Unit :=
  modify (fun s => { s with jp2bb := s.jp2bb.insert jp bb })

def emitJp (jp : JoinPointId) : M llvmctx (LLVM.BasicBlock llvmctx) := do
  let state ← get
  match state.jp2bb.find? jp with
  | .some bb => return bb
  | .none => throw s!"unable to find join point {jp}"

def getLLVMModule : M llvmctx (LLVM.Module llvmctx) := Context.llvmmodule <$> read

def getEnv : M llvmctx Environment := Context.env <$> read

instance : MonadOptions (M llvmctx) where
  getOptions := Context.options <$> read

def getModName : M llvmctx  Name := Context.modName <$> read

def getDecl (n : Name) : M llvmctx Decl := do
  let env ← getEnv
  match findEnvDecl env n with
  | some d => pure d
  | none   => throw s!"unknown declaration {n}"

def getBuilder : M llvmctx (LLVM.Builder llvmctx) := Context.builder <$> read

def constIntUnsigned (n : Nat) : M llvmctx (LLVM.Value llvmctx) :=  do
    LLVM.constIntUnsigned llvmctx (UInt64.ofNat n)

def getOrCreateFunctionPrototype (mod : LLVM.Module llvmctx)
    (retty : LLVM.LLVMType llvmctx) (name : String) (args : Array (LLVM.LLVMType llvmctx)) : M llvmctx  (LLVM.Value llvmctx) := do
  LLVM.getOrAddFunction mod name $ ← LLVM.functionType retty args (isVarArg := false)

def callLeanBox (arg : LLVM.Value llvmctx) (name : String := "") : M llvmctx (LLVM.Value llvmctx) := do
  let fnName :=  "lean_box"
  let retty ← LLVM.voidPtrType llvmctx
  let argtys := #[ ← LLVM.size_tType llvmctx ]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  LLVM.buildCall2 (← getBuilder) fnty fn  #[arg] name

def callLeanMarkPersistentFn (arg : LLVM.Value llvmctx) : M llvmctx  Unit := do
  let fnName :=  "lean_mark_persistent"
  let retty ← LLVM.voidType llvmctx
  let argtys := #[ ← LLVM.voidPtrType llvmctx ]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  let _ ← LLVM.buildCall2 (← getBuilder) fnty fn  #[arg]

-- `lean_{inc, dec}_{ref?}_{1,n}`
inductive RefcountKind where
  | inc | dec

instance : ToString RefcountKind where
  toString
    | .inc => "inc"
    | .dec => "dec"

def callLeanRefcountFn (kind : RefcountKind) (checkRef? : Bool) (arg : LLVM.Value llvmctx)
    (delta : Option (LLVM.Value llvmctx) := Option.none) : M llvmctx Unit := do
  let fnName :=  s!"lean_{kind}{if checkRef? then "" else "_ref"}{if delta.isNone then "" else "_n"}"
  let retty ← LLVM.voidType llvmctx
  let argtys := if delta.isNone then #[← LLVM.voidPtrType llvmctx] else #[← LLVM.voidPtrType llvmctx, ← LLVM.size_tType llvmctx]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  match delta with
  | .none => do
    -- since refcount δ is 1, we only supply the pointer.
    let _ ← LLVM.buildCall2 (← getBuilder) fnty fn #[arg]
  | .some n => do
    let _ ← LLVM.buildCall2 (← getBuilder) fnty fn #[arg, n]

-- `decRef1`
-- Do NOT attempt to merge this code with callLeanRefcountFn, because of the uber confusing
-- semantics of 'ref?'. If 'ref?' is true, it calls the version that is lean_dec
def callLeanDecRef (res : LLVM.Value llvmctx) : M llvmctx Unit := do
  let fnName :=  "lean_dec_ref"
  let retty ← LLVM.voidType llvmctx
  let argtys := #[ ← LLVM.i8PtrType llvmctx ]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  let _ ← LLVM.buildCall2 (← getBuilder) fnty fn  #[res]

def callLeanUnsignedToNatFn (n : Nat) (name : String := "") : M llvmctx (LLVM.Value llvmctx) := do
  let mod ← getLLVMModule
  let argtys := #[← LLVM.i32Type llvmctx]
  let retty ← LLVM.voidPtrType llvmctx
  let f ←   getOrCreateFunctionPrototype mod retty "lean_unsigned_to_nat"  argtys
  let fnty ← LLVM.functionType retty argtys
  let nv ← LLVM.constInt32 llvmctx (UInt64.ofNat n)
  LLVM.buildCall2 (← getBuilder) fnty f #[nv] name

def callLeanMkStringFromBytesFn (strPtr nBytes : LLVM.Value llvmctx) (name : String) : M llvmctx (LLVM.Value llvmctx) := do
  let fnName :=  "lean_mk_string_from_bytes"
  let retty ← LLVM.voidPtrType llvmctx
  let argtys :=  #[← LLVM.voidPtrType llvmctx, ← LLVM.i64Type llvmctx]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  LLVM.buildCall2 (← getBuilder) fnty fn #[strPtr, nBytes] name

def callLeanMkString (strPtr : LLVM.Value llvmctx) (name : String) : M llvmctx (LLVM.Value llvmctx) := do
  let retty ← LLVM.voidPtrType llvmctx
  let argtys :=  #[← LLVM.voidPtrType llvmctx]
  let fn ←  getOrCreateFunctionPrototype (← getLLVMModule) retty "lean_mk_string" argtys
  let fnty ← LLVM.functionType retty argtys
  LLVM.buildCall2 (← getBuilder) fnty fn #[strPtr] name

def callLeanCStrToNatFn (n : Nat) (name : String := "") : M llvmctx (LLVM.Value llvmctx) := do
  let fnName :=  "lean_cstr_to_nat"
  let retty ← LLVM.voidPtrType llvmctx
  let argtys :=  #[← LLVM.voidPtrType llvmctx]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  let s ← LLVM.buildGlobalString (← getBuilder) (value := toString n)
  LLVM.buildCall2 (← getBuilder) fnty fn #[s] name

def callLeanIOMkWorld : M llvmctx (LLVM.Value llvmctx) := do
  let fnName :=  "lean_io_mk_world"
  let retty ← LLVM.voidPtrType llvmctx
  let argtys :=  #[]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  LLVM.buildCall2 (← getBuilder) fnty fn #[] "mk_io_out"

def callLeanIOResultIsError (arg : LLVM.Value llvmctx) (name : String := "") : M llvmctx (LLVM.Value llvmctx) := do
  let fnName :=  "lean_io_result_is_error"
  let retty ← LLVM.i1Type llvmctx
  let argtys :=  #[← LLVM.voidPtrType llvmctx]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  LLVM.buildCall2 (← getBuilder) fnty fn #[arg] name

def callLeanAllocCtor (tag num_objs scalar_sz : Nat) (name : String := "") : M llvmctx (LLVM.Value llvmctx) := do
  let fnName :=  "lean_alloc_ctor"
  let retty ← LLVM.voidPtrType llvmctx
  let i32 ← LLVM.i32Type llvmctx
  let argtys :=  #[i32, i32, i32]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys

  let tag ← LLVM.constInt32 llvmctx (UInt64.ofNat tag)
  let num_objs ← LLVM.constInt32 llvmctx (UInt64.ofNat num_objs)
  let scalar_sz ← LLVM.constInt32 llvmctx (UInt64.ofNat scalar_sz)
  LLVM.buildCall2 (← getBuilder) fnty fn #[tag, num_objs, scalar_sz] name

def callLeanCtorSet (o i v : LLVM.Value llvmctx) : M llvmctx Unit := do
  let fnName := "lean_ctor_set"
  let retty ← LLVM.voidType llvmctx
  let voidptr ← LLVM.voidPtrType llvmctx
  let unsigned ← LLVM.size_tType llvmctx
  let argtys :=  #[voidptr, unsigned, voidptr]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  _ ← LLVM.buildCall2 (← getBuilder) fnty fn  #[o, i, v]

def callLeanIOResultMKOk (v : LLVM.Value llvmctx) (name : String := "") : M llvmctx (LLVM.Value llvmctx) := do
  let fnName :=  "lean_io_result_mk_ok"
  let voidptr ← LLVM.voidPtrType llvmctx
  let retty := voidptr
  let argtys :=  #[voidptr]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  LLVM.buildCall2 (← getBuilder) fnty fn #[v] name

def callLeanAllocClosureFn (f arity nys : LLVM.Value llvmctx) (retName : String := "") : M llvmctx (LLVM.Value llvmctx) := do
  let fnName :=  "lean_alloc_closure"
  let retty ← LLVM.voidPtrType llvmctx
  let argtys := #[ ← LLVM.voidPtrType llvmctx, ← LLVM.size_tType llvmctx, ← LLVM.size_tType llvmctx]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  LLVM.buildCall2 (← getBuilder) fnty fn  #[f, arity, nys] retName

def callLeanClosureSetFn (closure ix arg : LLVM.Value llvmctx) (retName : String := "") : M llvmctx Unit := do
  let fnName :=  "lean_closure_set"
  let retty ← LLVM.voidType llvmctx
  let argtys := #[ ← LLVM.voidPtrType llvmctx, ← LLVM.size_tType llvmctx, ← LLVM.voidPtrType llvmctx]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  let _ ← LLVM.buildCall2 (← getBuilder) fnty fn  #[closure, ix, arg] retName

def callLeanObjTag (closure : LLVM.Value llvmctx) (retName : String := "") : M llvmctx (LLVM.Value llvmctx) := do
  let fnName :=  "lean_obj_tag"
  let retty ← LLVM.i32Type llvmctx
  let argtys := #[ ← LLVM.voidPtrType llvmctx]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  let out ← LLVM.buildCall2 (← getBuilder) fnty fn  #[closure] retName
  LLVM.buildSextOrTrunc (← getBuilder) out (← LLVM.i64Type llvmctx)

def callLeanIOResultGetValue (v : LLVM.Value llvmctx) (name : String := "") : M llvmctx (LLVM.Value llvmctx) := do
  let fnName :=  "lean_io_result_get_value"
  let retty ← LLVM.voidPtrType llvmctx
  let argtys := #[ ← LLVM.voidPtrType llvmctx]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  LLVM.buildCall2 (← getBuilder) fnty fn #[v] name

def callLeanCtorRelease (closure i : LLVM.Value llvmctx) (retName : String := "") : M llvmctx Unit := do
  let fnName :=  "lean_ctor_release"
  let retty ← LLVM.voidType llvmctx
  let argtys := #[ ← LLVM.voidPtrType llvmctx, ← LLVM.size_tType llvmctx]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  let _ ← LLVM.buildCall2 (← getBuilder) fnty fn  #[closure, i] retName

def callLeanCtorSetTag (closure i : LLVM.Value llvmctx) (retName : String := "") : M llvmctx Unit := do
  let fnName :=  "lean_ctor_set_tag"
  let retty ← LLVM.voidType llvmctx
  let argtys := #[ ← LLVM.voidPtrType llvmctx, ← LLVM.size_tType llvmctx]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  let _ ← LLVM.buildCall2 (← getBuilder) fnty fn  #[closure, i] retName

def toLLVMType (t : IRType) : M llvmctx (LLVM.LLVMType llvmctx) := do
  match t with
  | IRType.float      => LLVM.doubleTypeInContext llvmctx
  | IRType.uint8      => LLVM.intTypeInContext llvmctx 8
  | IRType.uint16     => LLVM.intTypeInContext llvmctx 16
  | IRType.uint32     => LLVM.intTypeInContext llvmctx 32
  | IRType.uint64     => LLVM.intTypeInContext llvmctx 64
  -- TODO: how to cleanly size_t in LLVM? We can do eg. instantiate the current target and query for size.
  | IRType.usize      => LLVM.size_tType llvmctx
  | IRType.object     => do LLVM.pointerType (← LLVM.i8Type llvmctx)
  | IRType.tobject    => do LLVM.pointerType (← LLVM.i8Type llvmctx)
  | IRType.irrelevant => do LLVM.pointerType (← LLVM.i8Type llvmctx)
  | IRType.struct _ _ => panic! "dead code"
  | IRType.union _ _  => panic! "dead code"

def throwInvalidExportName {α : Type} (n : Name) : M llvmctx α := do
  throw s!"invalid export name {n.toString}"

def toCName (n : Name) : M llvmctx String := do
  match getExportNameFor? (← getEnv) n with
  | some (.str .anonymous s) => pure s
  | some _                   => throwInvalidExportName n
  | none                     => if n == `main then pure leanMainFn else pure n.mangle

def toCInitName (n : Name) : M llvmctx String := do
  match getExportNameFor? (← getEnv) n with
  | some (.str .anonymous s) => return "_init_" ++ s
  | some _                   => throwInvalidExportName n
  | none                     => pure ("_init_" ++ n.mangle)

/--
## LLVM Control flow Utilities
-/

-- Indicates whether the API for building the blocks for then/else should
-- forward the control flow to the merge block.
inductive ShouldForwardControlFlow where
| yes | no

-- Get the function we are currently inserting into.
def builderGetInsertionFn : M llvmctx (LLVM.Value llvmctx) := do
  let builderBB ← LLVM.getInsertBlock (← getBuilder)
  LLVM.getBasicBlockParent builderBB

def builderAppendBasicBlock (name : String) : M llvmctx (LLVM.BasicBlock llvmctx) := do
  let fn ← builderGetInsertionFn
  LLVM.appendBasicBlockInContext llvmctx fn name

def buildWhile_ (name : String) (condcodegen : M llvmctx (LLVM.Value llvmctx)) (bodycodegen : M llvmctx Unit) : M llvmctx Unit := do
  let fn ← builderGetInsertionFn

  let nameHeader := name ++ "header"
  let nameBody := name ++ "body"
  let nameMerge := name ++ "merge"

  -- cur → header
  let headerbb ← LLVM.appendBasicBlockInContext llvmctx fn nameHeader
  let _ ← LLVM.buildBr (← getBuilder) headerbb

  let bodybb ← LLVM.appendBasicBlockInContext llvmctx fn nameBody
  let mergebb ← LLVM.appendBasicBlockInContext llvmctx fn nameMerge

  -- header → {body, merge}
  LLVM.positionBuilderAtEnd (← getBuilder) headerbb
  let cond ← condcodegen
  let _ ← LLVM.buildCondBr (← getBuilder) cond bodybb mergebb

  -- body → header
  LLVM.positionBuilderAtEnd (← getBuilder) bodybb
  bodycodegen
  let _ ← LLVM.buildBr (← getBuilder) headerbb

  -- merge
  LLVM.positionBuilderAtEnd (← getBuilder) mergebb

-- build an if, and position the builder at the merge basic block after execution.
-- The '_' denotes that we return Unit on each branch.
def buildIfThen_ (name : String) (brval : LLVM.Value llvmctx) (thencodegen : M llvmctx ShouldForwardControlFlow) : M llvmctx Unit := do
  let fn ← builderGetInsertionFn

  let nameThen := name ++ "Then"
  let nameElse := name ++ "Else"
  let nameMerge := name ++ "Merge"

  let thenbb ← LLVM.appendBasicBlockInContext llvmctx fn nameThen
  let elsebb ← LLVM.appendBasicBlockInContext llvmctx fn nameElse
  let mergebb ← LLVM.appendBasicBlockInContext llvmctx fn nameMerge
  let _ ← LLVM.buildCondBr (← getBuilder) brval thenbb elsebb
  -- then
  LLVM.positionBuilderAtEnd (← getBuilder) thenbb
  let fwd? ← thencodegen
  match fwd? with
  | .yes => let _ ← LLVM.buildBr (← getBuilder) mergebb
  | .no => pure ()
  -- else
  LLVM.positionBuilderAtEnd (← getBuilder) elsebb
  let _ ← LLVM.buildBr (← getBuilder) mergebb
  -- merge
  LLVM.positionBuilderAtEnd (← getBuilder) mergebb

def buildIfThenElse_ (name : String) (brval : LLVM.Value llvmctx)
    (thencodegen : M llvmctx ShouldForwardControlFlow)
    (elsecodegen : M llvmctx ShouldForwardControlFlow) : M llvmctx Unit := do
  let fn ← LLVM.getBasicBlockParent (← LLVM.getInsertBlock (← getBuilder))
  let thenbb ← LLVM.appendBasicBlockInContext llvmctx fn (name ++ "Then")
  let elsebb ← LLVM.appendBasicBlockInContext llvmctx fn (name ++ "Else")
  let mergebb ← LLVM.appendBasicBlockInContext llvmctx fn (name ++ "Merge")
  let _ ← LLVM.buildCondBr (← getBuilder) brval thenbb elsebb
  -- then
  LLVM.positionBuilderAtEnd (← getBuilder) thenbb
  let fwd? ← thencodegen
  match fwd? with
  | .yes => let _ ← LLVM.buildBr (← getBuilder) mergebb
  | .no => pure ()
  -- else
  LLVM.positionBuilderAtEnd (← getBuilder) elsebb
  let fwd? ← elsecodegen
  match fwd? with
  | .yes => let _ ← LLVM.buildBr (← getBuilder) mergebb
  | .no => pure ()
  -- merge
  LLVM.positionBuilderAtEnd (← getBuilder) mergebb

-- Recall that lean uses `i8` for booleans, not `i1`, so we need to compare with `true`.
def buildLeanBoolTrue? (b : LLVM.Value llvmctx) (name : String := "") : M llvmctx (LLVM.Value llvmctx) := do
  LLVM.buildICmp (← getBuilder) LLVM.IntPredicate.NE b (← LLVM.constInt8 llvmctx 0) name

def emitFnDeclAux (mod : LLVM.Module llvmctx)
    (decl : Decl) (cppBaseName : String) (isExternal : Bool) : M llvmctx (LLVM.Value llvmctx) := do
  let ps := decl.params
  let env ← getEnv
  -- bollu: if we have a declaration with no parameters, then we emit it as a global pointer.
  -- bollu: Otherwise, we emit it as a function
  if ps.isEmpty then
      let retty ← (toLLVMType decl.resultType)
      let global ← LLVM.getOrAddGlobal mod cppBaseName retty
      if !isExternal then
        LLVM.setInitializer global (← LLVM.getUndef retty)
      return global
  else
      let retty ← (toLLVMType decl.resultType)
      let mut argtys := #[]
      for p in ps do
        -- if it is extern, then we must not add irrelevant args
        if !(isExternC env decl.name) || !p.ty.isIrrelevant then
          argtys := argtys.push (← toLLVMType p.ty)
      -- TODO (bollu): simplify this API, this code of `closureMaxArgs` is duplicated in multiple places.
      if argtys.size > closureMaxArgs && isBoxedName decl.name then
        argtys := #[← LLVM.pointerType (← LLVM.voidPtrType llvmctx)]
      let fnty ← LLVM.functionType retty argtys (isVarArg := false)
      LLVM.getOrAddFunction mod cppBaseName fnty

def emitFnDecl (decl : Decl) (isExternal : Bool) : M llvmctx Unit := do
  let cppBaseName ← toCName decl.name
  let _ ← emitFnDeclAux (← getLLVMModule) decl cppBaseName isExternal

def emitExternDeclAux (decl : Decl) (cNameStr : String) : M llvmctx Unit := do
  let env ← getEnv
  let extC := isExternC env decl.name
  let _ ← emitFnDeclAux (← getLLVMModule) decl cNameStr extC

def emitFnDecls : M llvmctx Unit := do
  let env ← getEnv
  let decls := getDecls env
  let modDecls  : NameSet := decls.foldl (fun s d => s.insert d.name) {}
  let usedDecls : NameSet := decls.foldl (fun s d => collectUsedDecls env d (s.insert d.name)) {}
  let usedDecls := usedDecls.toList
  for n in usedDecls do
    let decl ← getDecl n
    match getExternNameFor env `c decl.name with
    | some cName => emitExternDeclAux decl cName
    | none       => emitFnDecl decl (!modDecls.contains n)
  return ()

def emitLhsSlot_ (x : VarId) : M llvmctx (LLVM.LLVMType llvmctx × LLVM.Value llvmctx) := do
  let state ← get
  match state.var2val.find? x with
  | .some v => return v
  | .none => throw s!"unable to find variable {x}"

def emitLhsVal (x : VarId) (name : String := "") : M llvmctx (LLVM.Value llvmctx) := do
  let (xty, xslot) ← emitLhsSlot_ x
  LLVM.buildLoad2 (← getBuilder) xty xslot name

def emitLhsSlotStore (x : VarId) (v : LLVM.Value llvmctx) : M llvmctx Unit := do
  let (_, slot) ← emitLhsSlot_ x
  let _ ← LLVM.buildStore (← getBuilder) v slot

def emitArgSlot_ (x : Arg) : M llvmctx (LLVM.LLVMType llvmctx × LLVM.Value llvmctx) := do
  match x with
  | Arg.var x => emitLhsSlot_ x
  | _ => do
    let slotty ← LLVM.voidPtrType llvmctx
    let slot ← LLVM.buildAlloca (← getBuilder) slotty "irrelevant_slot"
    let v ← callLeanBox (← LLVM.constIntUnsigned llvmctx 0) "irrelevant_val"
    let _ ← LLVM.buildStore (← getBuilder) v slot
    return (slotty, slot)

def emitArgVal (x : Arg) (name : String := "") : M llvmctx (LLVM.LLVMType llvmctx × LLVM.Value llvmctx) := do
  let (xty, xslot) ← emitArgSlot_ x
  let xval ← LLVM.buildLoad2 (← getBuilder) xty xslot name
  return (xty, xval)

def emitAllocCtor (c : CtorInfo) : M llvmctx (LLVM.Value llvmctx) := do
  -- TODO(bollu) : find the correct size, don't assume 'void*' size is 8
  let hackSizeofVoidPtr := 8
  let scalarSize := hackSizeofVoidPtr * c.usize + c.ssize
  callLeanAllocCtor c.cidx c.size scalarSize "lean_alloc_ctor_out"

def emitCtorSetArgs (z : VarId) (ys : Array Arg) : M llvmctx Unit := do
  ys.size.forM fun i => do
    let zv ← emitLhsVal z
    let (_yty, yv) ← emitArgVal ys[i]!
    let iv ← LLVM.constIntUnsigned llvmctx (UInt64.ofNat i)
    callLeanCtorSet zv iv yv
    emitLhsSlotStore z zv
    pure ()

def emitCtor (z : VarId) (c : CtorInfo) (ys : Array Arg) : M llvmctx Unit := do
  let (_llvmty, slot) ← emitLhsSlot_ z
  if c.size == 0 && c.usize == 0 && c.ssize == 0 then do
    let v ← callLeanBox (← constIntUnsigned c.cidx) "lean_box_outv"
    let _ ← LLVM.buildStore (← getBuilder) v slot
  else do
    let v ← emitAllocCtor c
    let _ ← LLVM.buildStore (← getBuilder) v slot
    emitCtorSetArgs z ys

def emitInc (x : VarId) (n : Nat) (checkRef? : Bool) : M llvmctx Unit := do
  let xv ← emitLhsVal x
  if n != 1
  then do
     let nv ← LLVM.constIntUnsigned llvmctx (UInt64.ofNat n)
     callLeanRefcountFn (kind := RefcountKind.inc) (checkRef? := checkRef?) (delta := nv) xv
  else callLeanRefcountFn (kind := RefcountKind.inc) (checkRef? := checkRef?) xv

def emitDec (x : VarId) (n : Nat) (checkRef? : Bool) : M llvmctx Unit := do
  let xv ← emitLhsVal x
  if n != 1
  then throw "expected n = 1 for emitDec"
  else callLeanRefcountFn (kind := RefcountKind.dec) (checkRef? := checkRef?) xv

def emitNumLit (t : IRType) (v : Nat) : M llvmctx (LLVM.Value llvmctx) := do
  if t.isObj then
    if v < UInt32.size then
      callLeanUnsignedToNatFn v
    else
      callLeanCStrToNatFn v
  else
    LLVM.constInt (← toLLVMType t) (UInt64.ofNat v)

def toHexDigit (c : Nat) : String :=
  String.singleton c.digitChar

-- TODO(bollu) : Setup code sharing between 'EmitC' and 'EmitLLVM'
def quoteString (s : String) : String :=
  let q := "\"";
  let q := s.foldl
    (fun q c => q ++
      if c == '\n' then "\\n"
      else if c == '\r' then "\\r"
      else if c == '\t' then "\\t"
      else if c == '\\' then "\\\\"
      else if c == '\"' then "\\\""
      else if c.toNat <= 31 then
        "\\x" ++ toHexDigit (c.toNat / 16) ++ toHexDigit (c.toNat % 16)
      -- TODO(Leo) : we should use `\unnnn` for escaping unicode characters.
      else String.singleton c)
    q;
  q ++ "\""

def emitSimpleExternalCall (f : String) (ps : Array Param) (ys : Array Arg) (retty : IRType) (name : String) : M llvmctx (LLVM.Value llvmctx) := do
  let mut args := #[]
  let mut argTys := #[]
  for (p, y) in ps.zip ys do
    if !p.ty.isIrrelevant then
      let (_yty, yv) ← emitArgVal y ""
      argTys := argTys.push (← toLLVMType p.ty)
      args := args.push yv
  let fnty ← LLVM.functionType (← toLLVMType retty) argTys
  let fn ← LLVM.getOrAddFunction (← getLLVMModule) f fnty
  LLVM.buildCall2 (← getBuilder) fnty fn args name

-- TODO: if the external call is one that we cannot code generate, give up and
-- generate fallback code.
def emitExternCall
    (f : FunId)
    (ps : Array Param)
    (extData : ExternAttrData)
    (ys : Array Arg) (retty : IRType)
    (name : String := "") : M llvmctx (LLVM.Value llvmctx) :=
  match getExternEntryFor extData `c with
  | some (ExternEntry.standard _ extFn) => emitSimpleExternalCall extFn ps ys retty name
  | some (ExternEntry.inline "llvm" _pat) => throw "Unimplemented codegen of inline LLVM"
  | some (ExternEntry.inline _ pat) => throw s!"Cannot codegen non-LLVM inline code '{pat}'."
  | some (ExternEntry.foreign _ extFn)  => emitSimpleExternalCall extFn ps ys retty name
  | _ => throw s!"Failed to emit extern application '{f}'."

def getFunIdTy (f : FunId) : M llvmctx (LLVM.LLVMType llvmctx) := do
  let decl ← getDecl f
  let retty ← toLLVMType decl.resultType
  let argtys ← decl.params.mapM (fun p => do toLLVMType p.ty)
  LLVM.functionType retty argtys

/--
Create a function declaration and return a pointer to the function.
If the function actually takes arguments, then we must have a function pointer in scope.
If the function takes no arguments, then it is a top-level closed term, and its value will
be stored in a global pointer. So, we load from the global pointer. The type of the global is function pointer pointer.
This returns a *function pointer.*
-/
def getOrAddFunIdValue (f : FunId) : M llvmctx (LLVM.Value llvmctx) := do
  let decl ← getDecl f
  let fcname ← toCName f
  let retty ← toLLVMType decl.resultType
  if decl.params.isEmpty then
     let gslot ← LLVM.getOrAddGlobal (← getLLVMModule) fcname retty
     LLVM.buildLoad2 (← getBuilder) retty gslot
  else
    let argtys ← decl.params.mapM (fun p => do toLLVMType p.ty)
    let fnty ← LLVM.functionType retty argtys
    LLVM.getOrAddFunction (← getLLVMModule) fcname fnty

def emitPartialApp (z : VarId) (f : FunId) (ys : Array Arg) : M llvmctx Unit := do
  let decl ← getDecl f
  let fv ← getOrAddFunIdValue f
  let arity := decl.params.size
  let (_zty, zslot) ← emitLhsSlot_ z
  let zval ← callLeanAllocClosureFn fv
                                    (← constIntUnsigned arity)
                                    (← constIntUnsigned ys.size)
  let _ ← LLVM.buildStore (← getBuilder) zval zslot
  ys.size.forM fun i => do
    let (yty, yslot) ← emitArgSlot_ ys[i]!
    let yval ← LLVM.buildLoad2 (← getBuilder) yty yslot
    callLeanClosureSetFn zval (← constIntUnsigned i) yval

def emitApp (z : VarId) (f : VarId) (ys : Array Arg) : M llvmctx Unit := do
  if ys.size > closureMaxArgs then do
    let aargs ← LLVM.buildAlloca (← getBuilder) (← LLVM.arrayType (← LLVM.voidPtrType llvmctx) (UInt64.ofNat ys.size)) "aargs"
    for i in List.range ys.size do
      let (yty, yv) ← emitArgVal ys[i]!
      let aslot ← LLVM.buildInBoundsGEP2 (← getBuilder) yty aargs #[← constIntUnsigned 0, ← constIntUnsigned i] s!"param_{i}_slot"
      let _ ← LLVM.buildStore (← getBuilder) yv aslot
    let fnName :=  s!"lean_apply_m"
    let retty ← LLVM.voidPtrType llvmctx
    let args := #[← emitLhsVal f, ← constIntUnsigned ys.size, aargs]
    -- '1 + ...'. '1' for the fn and 'args' for the arguments
    let argtys := #[← LLVM.voidPtrType llvmctx]
    let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
    let fnty ← LLVM.functionType retty argtys
    let zv ← LLVM.buildCall2 (← getBuilder) fnty fn args
    emitLhsSlotStore z zv
  else do

    let fnName :=  s!"lean_apply_{ys.size}"
    let retty ← LLVM.voidPtrType llvmctx
    let args : Array (LLVM.Value llvmctx) := #[← emitLhsVal f] ++ (← ys.mapM (fun y => Prod.snd <$> (emitArgVal y)))
    -- '1 + ...'. '1' for the fn and 'args' for the arguments
    let argtys := (List.replicate (1 + ys.size) (← LLVM.voidPtrType llvmctx)).toArray
    let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
    let fnty ← LLVM.functionType retty argtys
    let zv ← LLVM.buildCall2 (← getBuilder) fnty fn args
    emitLhsSlotStore z zv

def emitFullApp (z : VarId) (f : FunId) (ys : Array Arg) : M llvmctx Unit := do
  let (__zty, zslot) ← emitLhsSlot_ z
  let decl ← getDecl f
  match decl with
  | Decl.extern _ ps retty extData =>
     let zv ← emitExternCall f ps extData ys retty
     let _ ← LLVM.buildStore (← getBuilder) zv zslot
  | Decl.fdecl .. =>
    if ys.size > 0 then
        let fv ← getOrAddFunIdValue f
        let ys ←  ys.mapM (fun y => do
            let (yty, yslot) ← emitArgSlot_ y
            let yv ← LLVM.buildLoad2 (← getBuilder) yty yslot
            return yv)
        let zv ← LLVM.buildCall2 (← getBuilder) (← getFunIdTy f) fv ys
        let _ ← LLVM.buildStore (← getBuilder) zv zslot
    else
       let zv ← getOrAddFunIdValue f
       let _ ← LLVM.buildStore (← getBuilder) zv zslot

-- Note that this returns a *slot*, just like `emitLhsSlot_`.
def emitLit (z : VarId) (t : IRType) (v : LitVal) : M llvmctx (LLVM.Value llvmctx) := do
  let llvmty ← toLLVMType t
  let zslot ← LLVM.buildAlloca (← getBuilder) llvmty
  addVartoState z zslot llvmty
  let zv ← match v with
            | LitVal.num v => emitNumLit t v
            | LitVal.str v =>
                 let zero ← LLVM.constIntUnsigned llvmctx 0
                 let str_global ← LLVM.buildGlobalString (← getBuilder) v
                 -- access through the global, into the 0th index of the array
                 let strPtr ← LLVM.buildInBoundsGEP2 (← getBuilder)
                                (← LLVM.opaquePointerTypeInContext llvmctx)
                                str_global #[zero] ""
                 let nbytes ← LLVM.constIntUnsigned llvmctx (UInt64.ofNat (v.utf8ByteSize))
                 callLeanMkStringFromBytesFn strPtr nbytes ""
  let _ ← LLVM.buildStore (← getBuilder) zv zslot
  return zslot

def callLeanCtorGet (x i : LLVM.Value llvmctx) (retName : String) : M llvmctx (LLVM.Value llvmctx) := do
  let fnName :=  "lean_ctor_get"
  let retty ← LLVM.voidPtrType llvmctx
  let argtys := #[ ← LLVM.voidPtrType llvmctx, ← LLVM.i32Type llvmctx]
  let fnty ← LLVM.functionType retty argtys
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let i ← LLVM.buildSextOrTrunc (← getBuilder) i (← LLVM.i32Type llvmctx)
  LLVM.buildCall2 (← getBuilder) fnty fn  #[x, i] retName

def emitProj (z : VarId) (i : Nat) (x : VarId) : M llvmctx Unit := do
  let xval ← emitLhsVal x
  let zval ← callLeanCtorGet xval (← constIntUnsigned i) ""
  emitLhsSlotStore z zval

def callLeanCtorGetUsize (x i : LLVM.Value llvmctx) (retName : String) : M llvmctx (LLVM.Value llvmctx) := do
  let fnName :=  "lean_ctor_get_usize"
  let retty ← LLVM.size_tType llvmctx
  let argtys := #[ ← LLVM.voidPtrType llvmctx, ← LLVM.size_tType llvmctx]
  let fnty ← LLVM.functionType retty argtys
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  LLVM.buildCall2 (← getBuilder) fnty fn  #[x, i] retName

def emitUProj (z : VarId) (i : Nat) (x : VarId) : M llvmctx Unit := do
  let xval ← emitLhsVal x
  let zval ← callLeanCtorGetUsize xval (← constIntUnsigned i) ""
  emitLhsSlotStore z zval

def emitOffset (n : Nat) (offset : Nat) : M llvmctx (LLVM.Value llvmctx) := do
   -- TODO(bollu) : replace 8 with sizeof(void*)
   let out ← constIntUnsigned 8
   let out ← LLVM.buildMul (← getBuilder) out (← constIntUnsigned n) "" -- sizeof(void*)*n
   LLVM.buildAdd (← getBuilder) out (← constIntUnsigned offset) "" -- sizeof(void*)*n+offset

def emitSProj (z : VarId) (t : IRType) (n offset : Nat) (x : VarId) : M llvmctx Unit := do
  let (fnName, retty) ←
    match t with
    | IRType.float  => pure ("lean_ctor_get_float", ← LLVM.doubleTypeInContext llvmctx)
    | IRType.uint8  => pure ("lean_ctor_get_uint8", ← LLVM.i8Type llvmctx)
    | IRType.uint16 => pure ("lean_ctor_get_uint16", ←  LLVM.i16Type llvmctx)
    | IRType.uint32 => pure ("lean_ctor_get_uint32", ← LLVM.i32Type llvmctx)
    | IRType.uint64 => pure ("lean_ctor_get_uint64", ← LLVM.i64Type llvmctx)
    | _             => throw s!"Invalid type for lean_ctor_get: '{t}'"
  let argtys := #[ ← LLVM.voidPtrType llvmctx, ← LLVM.size_tType llvmctx]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let xval ← emitLhsVal x
  let offset ← emitOffset n offset
  let fnty ← LLVM.functionType retty argtys
  let zval ← LLVM.buildCall2 (← getBuilder) fnty fn  #[xval, offset]
  emitLhsSlotStore z zval

def callLeanIsExclusive (closure : LLVM.Value llvmctx) (retName : String := "") : M llvmctx (LLVM.Value llvmctx) := do
  let fnName :=  "lean_is_exclusive"
  let retty ← LLVM.i1Type llvmctx
  let argtys := #[ ← LLVM.voidPtrType llvmctx]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  let out ← LLVM.buildCall2 (← getBuilder) fnty fn  #[closure] retName
  LLVM.buildSextOrTrunc (← getBuilder) out (← LLVM.i8Type llvmctx)

def callLeanIsScalar (closure : LLVM.Value llvmctx) (retName : String := "") : M llvmctx (LLVM.Value llvmctx) := do
  let fnName :=  "lean_is_scalar"
  let retty ← LLVM.i8Type llvmctx
  let argtys := #[ ← LLVM.voidPtrType llvmctx]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  LLVM.buildCall2 (← getBuilder) fnty fn  #[closure] retName

def emitIsShared (z : VarId) (x : VarId) : M llvmctx Unit := do
    let xv ← emitLhsVal x
    let exclusive? ← callLeanIsExclusive xv
    let exclusive? ← LLVM.buildSextOrTrunc (← getBuilder) exclusive? (← LLVM.i1Type llvmctx)
    let shared? ← LLVM.buildNot (← getBuilder) exclusive?
    let shared? ← LLVM.buildSext (← getBuilder) shared? (← LLVM.i8Type llvmctx)
    emitLhsSlotStore z shared?

def emitBox (z : VarId) (x : VarId) (xType : IRType) : M llvmctx Unit := do
  let xv ← emitLhsVal x
  let (fnName, argTy, xv) ←
    match xType with
    | IRType.usize  => pure ("lean_box_usize", ← LLVM.size_tType llvmctx, xv)
    | IRType.uint32 => pure ("lean_box_uint32", ← LLVM.i32Type llvmctx, xv)
    | IRType.uint64 => pure ("lean_box_uint64", ← LLVM.size_tType llvmctx, xv)
    | IRType.float  => pure ("lean_box_float", ← LLVM.doubleTypeInContext llvmctx, xv)
    | _             => do
         -- sign extend smaller values into i64
         let xv ← LLVM.buildSext (← getBuilder) xv (← LLVM.size_tType llvmctx)
         pure ("lean_box", ← LLVM.size_tType llvmctx, xv)
  let retty ← LLVM.voidPtrType llvmctx
  let argtys := #[argTy]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  let zv ← LLVM.buildCall2 (← getBuilder) fnty fn  #[xv]
  emitLhsSlotStore z zv

def IRType.isIntegerType (t : IRType) : Bool :=
  match t with
  | .uint8 => true
  | .uint16 => true
  | .uint32 => true
  | .uint64 => true
  | .usize => true
  | _ => false

def callUnboxForType (t : IRType) (v : LLVM.Value llvmctx) (retName : String := "") : M llvmctx (LLVM.Value llvmctx) := do
  let (fnName, retty) ←
     match t with
     | IRType.usize  => pure ("lean_unbox_usize", ← toLLVMType t)
     | IRType.uint32 => pure ("lean_unbox_uint32", ← toLLVMType t)
     | IRType.uint64 => pure ("lean_unbox_uint64", ← toLLVMType t)
     | IRType.float  => pure ("lean_unbox_float", ← toLLVMType t)
     | _             => pure ("lean_unbox", ← LLVM.size_tType llvmctx)
  let argtys := #[← LLVM.voidPtrType llvmctx ]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  LLVM.buildCall2 (← getBuilder) fnty fn #[v] retName

def emitUnbox (z : VarId) (t : IRType) (x : VarId) (retName : String := "") : M llvmctx Unit := do
  let zval ← callUnboxForType t (← emitLhsVal x) retName
  -- NOTE(bollu) : note that lean_unbox only returns an i64, but we may need to truncate to
  -- smaller widths. see `phashmap` for an example of this occurring at calls to `lean_unbox`
  let zval ←
    if IRType.isIntegerType t
    then LLVM.buildSextOrTrunc (← getBuilder) zval (← toLLVMType t)
    else pure zval
  emitLhsSlotStore z zval

def emitReset (z : VarId) (n : Nat) (x : VarId) : M llvmctx Unit := do
  let xv ← emitLhsVal x
  let isExclusive ← callLeanIsExclusive xv
  let isExclusive ← buildLeanBoolTrue? isExclusive
  buildIfThenElse_ "isExclusive" isExclusive
   (do
     let xv ← emitLhsVal x
     n.forM fun i => do
         callLeanCtorRelease xv (← constIntUnsigned i)
     emitLhsSlotStore z xv
     return ShouldForwardControlFlow.yes
   )
   (do
      let xv ← emitLhsVal x
      callLeanDecRef xv
      let box0 ← callLeanBox (← constIntUnsigned 0) "box0"
      emitLhsSlotStore z box0
      return ShouldForwardControlFlow.yes
   )

def emitReuse (z : VarId) (x : VarId) (c : CtorInfo) (updtHeader : Bool) (ys : Array Arg) : M llvmctx Unit := do
  let xv ← emitLhsVal x
  let isScalar ← callLeanIsScalar xv
  let isScalar ← buildLeanBoolTrue? isScalar
  buildIfThenElse_  "isScalar" isScalar
    (do
      let cv ← emitAllocCtor c
      emitLhsSlotStore z cv
      return ShouldForwardControlFlow.yes
   )
   (do
       let xv ← emitLhsVal x
       emitLhsSlotStore z xv
       if updtHeader then
          let zv ← emitLhsVal z
          callLeanCtorSetTag zv (← constIntUnsigned c.cidx)
       return ShouldForwardControlFlow.yes
   )
  emitCtorSetArgs z ys

def emitVDecl (z : VarId) (t : IRType) (v : Expr) : M llvmctx Unit := do
  match v with
  | Expr.ctor c ys      => emitCtor z c ys
  | Expr.reset n x      => emitReset z n x
  | Expr.reuse x c u ys => emitReuse z x c u ys
  | Expr.proj i x       => emitProj z i x
  | Expr.uproj i x      => emitUProj z i x
  | Expr.sproj n o x    => emitSProj z t n o x
  | Expr.fap c ys       => emitFullApp z c ys
  | Expr.pap c ys       => emitPartialApp z c ys
  | Expr.ap x ys        => emitApp z x ys
  | Expr.box t x        => emitBox z x t
  | Expr.unbox x        => emitUnbox z t x
  | Expr.isShared x     => emitIsShared z x
  | Expr.lit v          => let _ ← emitLit z t v

def declareVar (x : VarId) (t : IRType) : M llvmctx Unit := do
  let llvmty ← toLLVMType t
  let alloca ← LLVM.buildAlloca (← getBuilder) llvmty "varx"
  addVartoState x alloca llvmty

partial def declareVars (f : FnBody) : M llvmctx Unit := do
  match f with
  | FnBody.vdecl x t _ b => do
      declareVar x t
      declareVars b
  | FnBody.jdecl _ xs _ b => do
      for param in xs do declareVar param.x param.ty
      declareVars b
  | e => do
      if e.isTerminal then pure () else declareVars e.body

def emitTag (x : VarId) (xType : IRType) : M llvmctx (LLVM.Value llvmctx) := do
  if xType.isObj then do
    let xval ← emitLhsVal x
    callLeanObjTag xval
  else if xType.isScalar then do
    emitLhsVal x
  else
    throw "Do not know how to `emitTag` in general."

def emitSet (x : VarId) (i : Nat) (y : Arg) : M llvmctx Unit := do
  let fnName :=  "lean_ctor_set"
  let retty ← LLVM.voidType llvmctx
  let argtys := #[ ← LLVM.voidPtrType llvmctx, ← LLVM.size_tType llvmctx, ← LLVM.voidPtrType llvmctx]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  let _ ← LLVM.buildCall2 (← getBuilder) fnty fn  #[← emitLhsVal x, ← constIntUnsigned i, (← emitArgVal y).2]

def emitUSet (x : VarId) (i : Nat) (y : VarId) : M llvmctx Unit := do
  let fnName :=  "lean_ctor_set_usize"
  let retty ← LLVM.voidType llvmctx
  let argtys := #[ ← LLVM.voidPtrType llvmctx, ← LLVM.size_tType llvmctx, ← LLVM.size_tType llvmctx]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  let _ ← LLVM.buildCall2 (← getBuilder) fnty fn  #[← emitLhsVal x, ← constIntUnsigned i, (← emitLhsVal y)]

def emitTailCall (f : FunId) (v : Expr) : M llvmctx Unit := do
   match v with
  | Expr.fap _ ys => do
    let llvmctx ← read
    let ps := llvmctx.mainParams
    unless ps.size == ys.size do throw s!"Invalid tail call. f:'{f}' v:'{v}'"
    let args ← ys.mapM (fun y => Prod.snd <$> emitArgVal y)
    let fn ← builderGetInsertionFn
    let call ← LLVM.buildCall2 (← getBuilder) (← getFunIdTy f) fn args
    -- TODO (bollu) : add 'musttail' attribute using the C API.
    LLVM.setTailCall call true -- mark as tail call
    let _ ← LLVM.buildRet (← getBuilder) call
  | _ => throw s!"EmitTailCall expects function application, found '{v}'"

def emitJmp (jp : JoinPointId) (xs : Array Arg) : M llvmctx Unit := do
 let llvmctx ← read
  let ps ← match llvmctx.jpMap.find? jp with
  | some ps => pure ps
  | none    => throw s!"Unknown join point {jp}"
  unless xs.size == ps.size do throw s!"Invalid goto, mismatched sizes between arguments, formal parameters."
  for (p, x)  in ps.zip xs do
    let (_xty, xv) ← emitArgVal x
    emitLhsSlotStore p.x xv
  let _ ← LLVM.buildBr (← getBuilder) (← emitJp jp)

def emitSSet (x : VarId) (n : Nat) (offset : Nat) (y : VarId) (t : IRType) : M llvmctx Unit := do
  let (fnName, setty) ←
  match t with
  | IRType.float  => pure ("lean_ctor_set_float", ← LLVM.doubleTypeInContext llvmctx)
  | IRType.uint8  => pure ("lean_ctor_set_uint8", ← LLVM.i8Type llvmctx)
  | IRType.uint16 => pure ("lean_ctor_set_uint16", ← LLVM.i16Type llvmctx)
  | IRType.uint32 => pure ("lean_ctor_set_uint32", ← LLVM.i32Type llvmctx)
  | IRType.uint64 => pure ("lean_ctor_set_uint64", ← LLVM.i64Type llvmctx)
  | _             => throw s!"invalid type for 'lean_ctor_set': '{t}'"
  let argtys := #[ ← LLVM.voidPtrType llvmctx, ← LLVM.size_tType llvmctx, setty]
  let retty  ← LLVM.voidType llvmctx
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let xv ← emitLhsVal x
  let offset ← emitOffset n offset
  let yv ← emitLhsVal y
  let fnty ← LLVM.functionType retty argtys
  let _ ← LLVM.buildCall2 (← getBuilder) fnty fn  #[xv, offset, yv]

def emitDel (x : VarId) : M llvmctx Unit := do
  let argtys := #[ ← LLVM.voidPtrType llvmctx]
  let retty  ← LLVM.voidType llvmctx
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty "lean_free_object" argtys
  let xv ← emitLhsVal x
  let fnty ← LLVM.functionType retty argtys
  let _ ← LLVM.buildCall2 (← getBuilder) fnty fn  #[xv]

def emitSetTag (x : VarId) (i : Nat) : M llvmctx Unit := do
  let argtys := #[← LLVM.voidPtrType llvmctx, ← LLVM.size_tType llvmctx]
  let retty  ← LLVM.voidType llvmctx
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty "lean_ctor_set_tag" argtys
  let xv ← emitLhsVal x
  let fnty ← LLVM.functionType retty argtys
  let _ ← LLVM.buildCall2 (← getBuilder) fnty fn  #[xv, ← constIntUnsigned i]

def ensureHasDefault' (alts : Array Alt) : Array Alt :=
  if alts.any Alt.isDefault then alts
  else
    let last := alts.back
    let alts := alts.pop
    alts.push (Alt.default last.body)

mutual
partial def emitCase
    (x : VarId) (xType : IRType) (alts : Array Alt) : M llvmctx Unit := do
  let oldBB ← LLVM.getInsertBlock (← getBuilder)
  -- NOTE: In this context, 'Zext' versus 'Sext' have a meaninful semantic difference.
  --       We perform a zero extend so that one-bit tags of `0/-1` actually extend to `0/1`
  --       in 64-bit space.
  let tag ← emitTag  x xType
  let tag ← LLVM.buildZext (← getBuilder) tag (← LLVM.i64Type llvmctx)
  let alts := ensureHasDefault' alts
  let defaultBB ← builderAppendBasicBlock s!"case_{xType}_default"
  let numCasesHint := alts.size
  let switch ← LLVM.buildSwitch (← getBuilder) tag defaultBB (UInt64.ofNat numCasesHint)
  alts.forM fun alt => do
    match alt with
    | Alt.ctor c b  =>
       let destbb ← builderAppendBasicBlock s!"case_{xType}_{c.name}_{c.cidx}"
       LLVM.addCase switch (← constIntUnsigned c.cidx) destbb
       LLVM.positionBuilderAtEnd (← getBuilder) destbb
       emitFnBody b
    | Alt.default b =>
       LLVM.positionBuilderAtEnd (← getBuilder) defaultBB
       emitFnBody b
  LLVM.clearInsertionPosition (← getBuilder)
  LLVM.positionBuilderAtEnd (← getBuilder) oldBB -- reset state to previous insertion point.

-- NOTE:  emitJP promises to keep the builder context untouched.
partial def emitJDecl
    (jp : JoinPointId) (_ps : Array Param) (b : FnBody) : M llvmctx Unit := do
  let oldBB ← LLVM.getInsertBlock (← getBuilder)
  let jpbb ← builderAppendBasicBlock s!"jp_{jp.idx}"
  addJpTostate jp jpbb
  LLVM.positionBuilderAtEnd (← getBuilder) jpbb
  -- NOTE(bollu) : Note that we declare the slots for the variables that are inside
  --              the join point body before emitting the join point body.
  --              This ensures reachability via dominance.
  -- TODO(bollu) : Eliminate the need entirely for 'alloca'/slots by generating SSA phi nodes
  --              directly as discussed with digamma(Mario Carneiro <di.gama@gmail.com>)
  declareVars b
  emitBlock b
  LLVM.positionBuilderAtEnd (← getBuilder) oldBB -- reset state

partial def emitUnreachable : M llvmctx Unit := do
  let retty ← LLVM.voidType llvmctx
  let argtys := #[]
  let fn ← getOrCreateFunctionPrototype  (← getLLVMModule) retty "lean_internal_panic_unreachable" argtys
  let fnty ← LLVM.functionType retty argtys
  let _ ← LLVM.buildCall2 (← getBuilder) fnty fn #[]
  let _ ← LLVM.buildUnreachable (← getBuilder)

partial def emitBlock (b : FnBody) : M llvmctx Unit := do
  match b with
  | FnBody.jdecl j xs  v b      =>
       emitJDecl j xs v
       emitBlock b
  | d@(FnBody.vdecl x t v b)   => do
    let llvmctx ← read
    if isTailCallTo llvmctx.mainFn d then
      emitTailCall llvmctx.mainFn v
    else
      emitVDecl x t v
      emitBlock b
  | FnBody.inc x n c p b       =>
    unless p do emitInc x n c
    emitBlock b
  | FnBody.dec x n c p b       =>
    unless p do emitDec x n c
    emitBlock b
  | FnBody.del x b             => emitDel x; emitBlock b
  | FnBody.setTag x i b        => emitSetTag x i; emitBlock b
  | FnBody.set x i y b         => emitSet x i y; emitBlock b
  | FnBody.uset x i y b        => emitUSet x i y; emitBlock b
  | FnBody.sset x i o y t b    => emitSSet x i o y t; emitBlock b
  | FnBody.mdata _ b           => emitBlock b
  | FnBody.ret x               => do
      let (_xty, xv) ← emitArgVal x "ret_val"
      let _ ← LLVM.buildRet (← getBuilder) xv
  | FnBody.case _ x xType alts =>
     emitCase x xType alts
  | FnBody.jmp j xs            =>
     emitJmp j xs
  | FnBody.unreachable         => emitUnreachable

partial def emitFnBody (b : FnBody) : M llvmctx Unit := do
  declareVars b
  emitBlock b

end

def emitFnArgs (needsPackedArgs? : Bool)  (llvmfn : LLVM.Value llvmctx) (params : Array Param) : M llvmctx Unit := do
  if needsPackedArgs? then do
      let argsp ← LLVM.getParam llvmfn 0 -- lean_object **args
      for i in List.range params.size do
          let param := params[i]!
          -- argsi := (args + i)
          let argsi ← LLVM.buildGEP2 (← getBuilder) (← LLVM.voidPtrType llvmctx) argsp #[← constIntUnsigned i] s!"packed_arg_{i}_slot"
          let llvmty ← toLLVMType param.ty
          -- pv := *(argsi) = *(args + i)
          let pv ← LLVM.buildLoad2 (← getBuilder) llvmty argsi
          -- slot for arg[i] which is always void* ?
          let alloca ← LLVM.buildAlloca (← getBuilder) llvmty s!"arg_{i}"
          let _ ← LLVM.buildStore (← getBuilder) pv alloca
          addVartoState params[i]!.x alloca llvmty
  else
      let n := LLVM.countParams llvmfn
      for i in (List.range n.toNat) do
        let llvmty ← toLLVMType params[i]!.ty
        let alloca ← LLVM.buildAlloca (← getBuilder)  llvmty s!"arg_{i}"
        let arg ← LLVM.getParam llvmfn (UInt64.ofNat i)
        let _ ← LLVM.buildStore (← getBuilder) arg alloca
        addVartoState params[i]!.x alloca llvmty

def emitDeclAux (mod : LLVM.Module llvmctx) (d : Decl) : M llvmctx Unit := do
  let env ← getEnv
  let (_, jpMap) := mkVarJPMaps d
  withReader (fun llvmctx => { llvmctx with jpMap := jpMap }) do
  unless hasInitAttr env d.name do
    match d with
    | .fdecl (f := f) (xs := xs) (type := t) (body := b) .. =>
      let baseName ← toCName f
      let name := if xs.size > 0 then baseName else "_init_" ++ baseName
      let retty ← toLLVMType t
      let mut argtys := #[]
      let needsPackedArgs? := xs.size > closureMaxArgs && isBoxedName d.name
      if needsPackedArgs? then
          argtys := #[← LLVM.pointerType (← LLVM.voidPtrType llvmctx)]
      else
        for x in xs do
          argtys := argtys.push (← toLLVMType x.ty)
      let fnty ← LLVM.functionType retty argtys (isVarArg := false)
      let llvmfn ← LLVM.getOrAddFunction mod name fnty
      withReader (fun llvmctx => { llvmctx with mainFn := f, mainParams := xs }) do
        set { var2val := default, jp2bb := default : EmitLLVM.State llvmctx } -- flush variable map
        let entrybb ← LLVM.appendBasicBlockInContext llvmctx llvmfn "entry"
        LLVM.positionBuilderAtEnd (← getBuilder) entrybb
        -- This name is bankrupt anyway, because `d` may get specialized.
        -- Howver. Henrik has infomed me that extern declarations are passed
        -- unmolested through the entire compiler pipelines, and thus this lookup
        -- is in fact """legal""", since our `CodeGeneratedBy` attribute marks
        -- definitions as `extern`.
        emitFnArgs needsPackedArgs? llvmfn xs
        match ← LLVM.CodeGeneratedBy.getCodeGeneratorFromEnv? d.name (← getEnv) (← getOptions)  with
        | some cgen =>
          -- TODO: convert code generator state into an LLVM builder state.
          -- TODO: convert the arguments of the function into LLVM builder registers.
          let var2val := (← get).var2val
          let entryBBId : LLVM.Pure.BBId := 0
          let entryBB : LLVM.Pure.BasicBlock := { name := "entry" }
          let initBuilderState : LLVM.Pure.PureBuilderState := {
             bbs := HashMap.ofList [(entryBBId, entryBB)]
          }
          let mut argRegisters : Array LLVM.Pure.Reg := #[]
          let mut registerFile : HashMap LLVM.Pure.Reg (LLVM.Value llvmctx) := {}
          -- create a registers for each argument.
          for (_var, (_ty, val)) in var2val.toList do
            let reg := LLVM.Pure.Reg.ofNat argRegisters.size
            argRegisters := argRegisters.push reg
            registerFile := registerFile.insert reg val

          -- TODO: create the correct initBuilderState
          let pureBuilderState ← match (cgen argRegisters).run initBuilderState with
            | .ok (_, state) => pure state
            | .error err => throw err
          -- instantiate the user's build commands.
          let instantiationCtx : LLVM.Pure.InstantiationContext llvmctx := {
            llvmmodule := mod,
            llvmbuilder := (← getBuilder),
            registerFile := registerFile,
            basicBlocks := HashMap.ofList [(entryBBId, entrybb)]
            -- TODO: we need to also ideally setup `functions`
            -- to allow the user to find functions.
            -- However, maybe we do not need `functions` since we can always lookup functions
            -- in the context. Think about this.
          }
          -- Run the code generator to produce LLVM code.
          pureBuilderState.instantiate instantiationCtx
        | none =>
          emitFnBody b
      pure ()
    | _ => pure ()

def emitDecl (mod : LLVM.Module llvmctx) (d : Decl) : M llvmctx Unit := do
  let d := d.normalizeIds -- ensure we don't have gaps in the variable indices
  try
    emitDeclAux mod d
    return ()
  catch err =>
    throw (s!"emitDecl:\ncompiling:\n{d}\nerr:\n{err}\n")

def emitFns (mod : LLVM.Module llvmctx) : M llvmctx Unit := do
  let env ← getEnv
  let decls := getDecls env
  decls.forM (emitDecl mod)

def callIODeclInitFn (initFnName : String) (world : LLVM.Value llvmctx) : M llvmctx (LLVM.Value llvmctx) := do
  let retty ← LLVM.voidPtrType llvmctx
  let argtys := #[← LLVM.voidPtrType llvmctx]
  let fn ← getOrCreateFunctionPrototype  (← getLLVMModule) retty initFnName argtys
  let fnty ← LLVM.functionType retty argtys
  LLVM.buildCall2 (← getBuilder) fnty fn #[world]

def callPureDeclInitFn (initFnName : String) (retty : LLVM.LLVMType llvmctx) : M llvmctx (LLVM.Value llvmctx) := do
  let argtys := #[]
  let fn ← getOrCreateFunctionPrototype  (← getLLVMModule) retty initFnName argtys
  let fnty ← LLVM.functionType retty argtys
  LLVM.buildCall2 (← getBuilder) fnty fn #[]

def emitDeclInit (parentFn : LLVM.Value llvmctx) (d : Decl) : M llvmctx Unit := do
  let env ← getEnv
  if isIOUnitInitFn env d.name then do
    let world ← callLeanIOMkWorld
    let resv ← callIODeclInitFn (← toCName d.name) world
    let err? ← callLeanIOResultIsError resv "is_error"
    buildIfThen_ s!"init_{d.name}_isError" err?
      (do
        let _ ← LLVM.buildRet (← getBuilder) resv
        pure ShouldForwardControlFlow.no)
    -- TODO (bollu) : emit lean_dec_ref. For now, it does not matter.
  else if d.params.size == 0 then
    match getInitFnNameFor? env d.name with
    | some initFn =>
      let llvmty ← toLLVMType d.resultType
      let dslot ←  LLVM.getOrAddGlobal (← getLLVMModule) (← toCName d.name) llvmty
      LLVM.setInitializer dslot (← LLVM.getUndef llvmty)
      let initBB ← builderAppendBasicBlock s!"do_{d.name}_init"
      let restBB ← builderAppendBasicBlock s!"post_{d.name}_init"
      let checkBuiltin? := getBuiltinInitFnNameFor? env d.name |>.isSome
      if checkBuiltin? then
        -- `builtin` is set to true if the initializer is part of the executable,
        -- and not loaded dynamically.
        let builtinParam ← LLVM.getParam parentFn 0
        let cond ← buildLeanBoolTrue? builtinParam "is_builtin_true"
        let _ ← LLVM.buildCondBr (← getBuilder) cond initBB restBB
       else
        let _ ← LLVM.buildBr (← getBuilder) initBB
      LLVM.positionBuilderAtEnd (← getBuilder) initBB
      let world ← callLeanIOMkWorld
      let resv ← callIODeclInitFn (← toCName initFn) world
      let err? ← callLeanIOResultIsError resv s!"{d.name}_is_error"
      buildIfThen_ s!"init_{d.name}_isError" err?
        (do
          let _ ← LLVM.buildRet (← getBuilder) resv
          pure ShouldForwardControlFlow.no)
      let dval ← callLeanIOResultGetValue resv s!"{d.name}_res"
      let _ ← LLVM.buildStore (← getBuilder) dval dslot
      if d.resultType.isScalar then
        let dval ← callLeanIOResultGetValue resv s!"{d.name}_res"
        let dval ← callUnboxForType d.resultType dval
        let _ ← LLVM.buildStore (← getBuilder) dval dslot
      else
         let dval ← callLeanIOResultGetValue resv s!"{d.name}_res"
         let _ ← LLVM.buildStore (← getBuilder) dval dslot
         callLeanMarkPersistentFn dval
      let _ ← LLVM.buildBr (← getBuilder) restBB
      LLVM.positionBuilderAtEnd (← getBuilder) restBB
    | none => do
      let llvmty ← toLLVMType d.resultType
      let dslot ←  LLVM.getOrAddGlobal (← getLLVMModule) (← toCName d.name) llvmty
      LLVM.setInitializer dslot (← LLVM.getUndef llvmty)
      let dval ← callPureDeclInitFn (← toCInitName d.name) (← toLLVMType d.resultType)
      let _ ← LLVM.buildStore (← getBuilder) dval dslot
      if d.resultType.isObj then
         callLeanMarkPersistentFn dval

def callModInitFn (modName : Name) (input world : LLVM.Value llvmctx) (retName : String): M llvmctx (LLVM.Value llvmctx) := do
  let fnName := mkModuleInitializationFunctionName modName
  let retty ← LLVM.voidPtrType llvmctx
  let argtys := #[ (← LLVM.i8Type llvmctx), (← LLVM.voidPtrType llvmctx)]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  LLVM.buildCall2 (← getBuilder) fnty fn #[input, world] retName

def emitInitFn (mod : LLVM.Module llvmctx) : M llvmctx Unit := do
  let env ← getEnv
  let modName ← getModName

  let initFnTy ← LLVM.functionType (← LLVM.voidPtrType llvmctx) #[ (← LLVM.i8Type llvmctx), (← LLVM.voidPtrType llvmctx)] (isVarArg := false)
  let initFn ← LLVM.getOrAddFunction mod (mkModuleInitializationFunctionName modName) initFnTy
  let entryBB ← LLVM.appendBasicBlockInContext llvmctx initFn "entry"
  LLVM.positionBuilderAtEnd (← getBuilder) entryBB
  let ginit?ty := ← LLVM.i1Type llvmctx
  let ginit?slot ← LLVM.getOrAddGlobal mod (modName.mangle ++ "_G_initialized") ginit?ty
  LLVM.setInitializer ginit?slot (← LLVM.constFalse llvmctx)
  let ginit?v ← LLVM.buildLoad2 (← getBuilder) ginit?ty ginit?slot "init_v"
  buildIfThen_ "isGInitialized" ginit?v
    (do
      let box0 ← callLeanBox (← LLVM.constIntUnsigned llvmctx 0) "box0"
      let out ← callLeanIOResultMKOk box0 "retval"
      let _ ← LLVM.buildRet (← getBuilder) out
      pure ShouldForwardControlFlow.no)
  let _ ← LLVM.buildStore (← getBuilder) (← LLVM.constTrue llvmctx) ginit?slot

  env.imports.forM fun import_ => do
    let builtin ← LLVM.getParam initFn 0
    let world ← callLeanIOMkWorld
    let res ← callModInitFn import_.module builtin world ("res_" ++ import_.module.mangle)
    let err? ← callLeanIOResultIsError res ("res_is_error_"  ++ import_.module.mangle)
    buildIfThen_ ("IsError" ++ import_.module.mangle) err?
      (do
        let _ ← LLVM.buildRet (← getBuilder) res
        pure ShouldForwardControlFlow.no)
    callLeanDecRef res
  let decls := getDecls env
  decls.reverse.forM (emitDeclInit initFn)
  let box0 ← callLeanBox (← LLVM.constIntUnsigned llvmctx 0) "box0"
  let out ← callLeanIOResultMKOk box0 "retval"
  let _ ← LLVM.buildRet (← getBuilder) out

def callLeanInitialize : M llvmctx Unit := do
  let fnName :=  "lean_initialize"
  let retty ← LLVM.voidType llvmctx
  let argtys := #[]
  let fnty ← LLVM.functionType retty argtys
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let _ ← LLVM.buildCall2 (← getBuilder) fnty fn #[]

def callLeanInitializeRuntimeModule : M llvmctx Unit := do
  let fnName :=  "lean_initialize_runtime_module"
  let retty ← LLVM.voidType llvmctx
  let argtys := #[]
  let fnty ← LLVM.functionType retty argtys
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let _ ← LLVM.buildCall2 (← getBuilder) fnty fn #[]

def callLeanSetPanicMessages
    (enable? : LLVM.Value llvmctx) : M llvmctx Unit := do
  let fnName :=  "lean_set_panic_messages"
  let retty ← LLVM.voidType llvmctx
  let argtys := #[ ← LLVM.i1Type llvmctx ]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  let _ ← LLVM.buildCall2 (← getBuilder) fnty fn #[enable?]

def callLeanIOMarkEndInitialization : M llvmctx Unit := do
  let fnName :=  "lean_io_mark_end_initialization"
  let retty ← LLVM.voidType llvmctx
  let argtys := #[]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  let _ ← LLVM.buildCall2 (← getBuilder) fnty fn #[]

def callLeanIOResultIsOk
    (arg : LLVM.Value llvmctx) (name : String := "") : M llvmctx (LLVM.Value llvmctx) := do
  let fnName :=  "lean_io_result_is_ok"
  let retty ← LLVM.i1Type llvmctx
  let argtys := #[ ← LLVM.voidPtrType llvmctx ]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  LLVM.buildCall2 (← getBuilder) fnty fn #[arg] name

def callLeanInitTaskManager : M llvmctx Unit := do
  let fnName :=  "lean_init_task_manager"
  let retty ← LLVM.voidType llvmctx
  let argtys := #[]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  let _ ← LLVM.buildCall2 (← getBuilder) fnty fn #[]

def callLeanFinalizeTaskManager : M llvmctx Unit := do
  let fnName :=  "lean_finalize_task_manager"
  let retty ← LLVM.voidPtrType llvmctx
  let argtys := #[]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  let _ ← LLVM.buildCall2 (← getBuilder) fnty fn #[]

def callLeanUnboxUint32
    (v : LLVM.Value llvmctx) (name : String := "") : M llvmctx (LLVM.Value llvmctx) := do
  let fnName :=  "lean_unbox_uint32"
  let retty ← LLVM.i32Type llvmctx
  let argtys := #[ ← LLVM.voidPtrType llvmctx ]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  LLVM.buildCall2 (← getBuilder) fnty fn  #[v] name

def callLeanIOResultShowError
    (v : LLVM.Value llvmctx) (name : String := "") : M llvmctx Unit := do
  let fnName :=  "lean_io_result_show_error"
  let retty ← LLVM.voidType llvmctx
  let argtys := #[ ← LLVM.voidPtrType llvmctx ]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  let _ ← LLVM.buildCall2 (← getBuilder) fnty fn #[v] name

def callLeanMainFn (argv? : Option (LLVM.Value llvmctx)) (world : LLVM.Value llvmctx) (name : String) : M llvmctx (LLVM.Value llvmctx) := do
  let retty ← LLVM.voidPtrType llvmctx
  let voidptr ← LLVM.voidPtrType llvmctx
  let argtys := if argv?.isSome then #[ voidptr, voidptr ] else #[ voidptr ]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty leanMainFn argtys
  let fnty ← LLVM.functionType retty argtys
  let args := match argv? with
              | .some argv => #[argv, world]
              | .none => #[world]
  LLVM.buildCall2 (← getBuilder) fnty fn args name

-- TODO (hargonix): This function is taking 2s in both the old and the new compiler, why is this the case?
def emitMainFn (mod : LLVM.Module llvmctx) : M llvmctx Unit := do
  let d ← getDecl `main
  let xs ← match d with
   | .fdecl (xs := xs) .. => pure xs
   | _ =>  throw "Function declaration expected for 'main'"

  unless xs.size == 2 || xs.size == 1 do throw s!"Invalid main function, main expected to have '2' or '1' arguments, found '{xs.size}' arguments"
  let env ← getEnv
  let usesLeanAPI := usesModuleFrom env `Lean
  let mainTy ← LLVM.functionType (← LLVM.i64Type llvmctx)
      #[(← LLVM.i64Type llvmctx), (← LLVM.pointerType (← LLVM.voidPtrType llvmctx))]
  let main ← LLVM.getOrAddFunction mod "main" mainTy
  let entry ← LLVM.appendBasicBlockInContext llvmctx main "entry"
  LLVM.positionBuilderAtEnd (← getBuilder) entry
  /-
  #if defined(WIN32) || defined(_WIN32)
  SetErrorMode(SEM_FAILCRITICALERRORS);
  #endif
  -/
  let inty ← LLVM.voidPtrType llvmctx
  let inslot ← LLVM.buildAlloca (← getBuilder) (← LLVM.pointerType inty) "in"
  let resty ← LLVM.voidPtrType llvmctx
  let res ← LLVM.buildAlloca (← getBuilder) (← LLVM.pointerType resty) "res"
  if usesLeanAPI then callLeanInitialize else callLeanInitializeRuntimeModule
    /- We disable panic messages because they do not mesh well with extracted closed terms.
        See issue #534. We can remove this workaround after we implement issue #467. -/
  callLeanSetPanicMessages (← LLVM.constFalse llvmctx)
  let world ← callLeanIOMkWorld
  let resv ← callModInitFn (← getModName) (← LLVM.constInt8 llvmctx 1) world ((← getModName).toString ++ "_init_out")
  let _ ← LLVM.buildStore (← getBuilder) resv res

  callLeanSetPanicMessages (← LLVM.constTrue llvmctx)
  callLeanIOMarkEndInitialization

  let resv ← LLVM.buildLoad2 (← getBuilder) resty res "resv"
  let res_is_ok ← callLeanIOResultIsOk resv "res_is_ok"
  buildIfThen_ "resIsOkBranches"  res_is_ok
    (do -- then clause of the builder)
      callLeanDecRef resv
      callLeanInitTaskManager
      if xs.size == 2 then
        let inv ← callLeanBox (← LLVM.constInt (← LLVM.size_tType llvmctx) 0) "inv"
        let _ ← LLVM.buildStore (← getBuilder) inv inslot
        let ity ← LLVM.size_tType llvmctx
        let islot ← LLVM.buildAlloca (← getBuilder) ity "islot"
        let argcval ← LLVM.getParam main 0
        let argvval ← LLVM.getParam main 1
        let _ ← LLVM.buildStore (← getBuilder) argcval islot
        buildWhile_ "argv"
          (condcodegen := do
            let iv ← LLVM.buildLoad2 (← getBuilder) ity islot "iv"
            let i_gt_1 ← LLVM.buildICmp (← getBuilder) LLVM.IntPredicate.UGT iv (← constIntUnsigned 1) "i_gt_1"
            return i_gt_1)
          (bodycodegen := do
            let iv ← LLVM.buildLoad2 (← getBuilder) ity islot "iv"
            let iv_next ← LLVM.buildSub (← getBuilder) iv (← constIntUnsigned 1) "iv.next"
            let _ ← LLVM.buildStore (← getBuilder) iv_next islot
            let nv ← callLeanAllocCtor 1 2 0 "nv"
            let argv_i_next_slot ← LLVM.buildGEP2 (← getBuilder) (← LLVM.voidPtrType llvmctx) argvval #[iv_next] "argv.i.next.slot"
            let argv_i_next_val ← LLVM.buildLoad2 (← getBuilder) (← LLVM.voidPtrType llvmctx) argv_i_next_slot "argv.i.next.val"
            let argv_i_next_val_str ← callLeanMkString argv_i_next_val "arg.i.next.val.str"
            callLeanCtorSet nv (← constIntUnsigned 0) argv_i_next_val_str
            let inv ← LLVM.buildLoad2 (← getBuilder) inty inslot "inv"
            callLeanCtorSet nv (← constIntUnsigned 1) inv
            let _ ← LLVM.buildStore (← getBuilder) nv inslot)
        let world ← callLeanIOMkWorld
        let inv ← LLVM.buildLoad2 (← getBuilder) inty inslot "inv"
        let resv ← callLeanMainFn (argv? := .some inv) (world := world) "resv"
        let _ ← LLVM.buildStore (← getBuilder) resv res
        pure ShouldForwardControlFlow.yes
      else
          let world ← callLeanIOMkWorld
          let resv ← callLeanMainFn (argv? := .none) (world := world) "resv"
          let _ ← LLVM.buildStore (← getBuilder) resv res
          pure ShouldForwardControlFlow.yes
  )

  -- `IO _`
  let retTy := env.find? `main |>.get! |>.type |>.getForallBody
  -- either `UInt32` or `(P)Unit`
  let retTy := retTy.appArg!
  -- finalize at least the task manager to avoid leak sanitizer false positives
  -- from tasks outliving the main thread
  callLeanFinalizeTaskManager
  let resv ← LLVM.buildLoad2 (← getBuilder) resty res "resv"
  let res_is_ok ← callLeanIOResultIsOk resv "res_is_ok"
  buildIfThenElse_ "res.is.ok" res_is_ok
    (do -- then builder
      if retTy.constName? == some ``UInt32 then
        let resv ← LLVM.buildLoad2 (← getBuilder) resty res "resv"
        let retv ← callLeanUnboxUint32 (← callLeanIOResultGetValue resv "io_val") "retv"
        let retv ← LLVM.buildSext (← getBuilder) retv (← LLVM.i64Type llvmctx) "retv_sext"
        callLeanDecRef resv
        let _ ← LLVM.buildRet (← getBuilder) retv
        pure ShouldForwardControlFlow.no
      else
        callLeanDecRef resv
        let _ ← LLVM.buildRet (← getBuilder) (← LLVM.constInt64 llvmctx 0)
        pure ShouldForwardControlFlow.no

    )
    (do -- else builder
        let resv ← LLVM.buildLoad2 (← getBuilder) resty res "resv"
        callLeanIOResultShowError resv
        callLeanDecRef resv
        let _ ← LLVM.buildRet (← getBuilder) (← LLVM.constInt64 llvmctx 1)
        pure ShouldForwardControlFlow.no)
  -- at the merge
  let _ ← LLVM.buildUnreachable (← getBuilder)

def hasMainFn : M llvmctx Bool := do
  let env ← getEnv
  let decls := getDecls env
  return decls.any (fun d => d.name == `main)

def emitMainFnIfNeeded (mod : LLVM.Module llvmctx) : M llvmctx Unit := do
  if (← hasMainFn) then emitMainFn mod

def main : M llvmctx Unit := do
  emitFnDecls
  emitFns (← getLLVMModule)
  emitInitFn (← getLLVMModule)
  emitMainFnIfNeeded (← getLLVMModule)
end EmitLLVM

def getLeanHBcPath : IO System.FilePath := do
  return (← getLibDir (← getBuildDir)) / "lean.h.bc"

def optimizeLLVMModule (mod : LLVM.Module ctx) : IO Unit := do
  let pm  ← LLVM.createPassManager
  let pmb ← LLVM.createPassManagerBuilder
  pmb.setOptLevel 3
  pmb.populateModulePassManager pm
  LLVM.runPassManager pm mod
  LLVM.disposePassManager pm
  LLVM.disposePassManagerBuilder pmb

/--
`emitLLVM` is the entrypoint for the lean shell to code generate LLVM.
-/
@[export lean_ir_emit_llvm]
def emitLLVM (env : Environment) (options : Options) (modName : Name) (filepath : String) (tripleStr? : Option String) : IO Unit := do
  LLVM.llvmInitializeTargetInfo
  let llvmctx ← LLVM.createContext
  let module ← LLVM.createModule llvmctx modName.toString
  let builder ← LLVM.createBuilderInContext llvmctx
  let emitLLVMCtx : EmitLLVM.Context llvmctx :=
    {env := env, options := options, modName := modName, llvmmodule := module, builder := builder}
  let initState := { var2val := default, jp2bb := default : EmitLLVM.State llvmctx}
  let out? ← ((EmitLLVM.main (llvmctx := llvmctx)).run initState).run emitLLVMCtx
  match out? with
  | .ok _ => do
         let membuf ← LLVM.createMemoryBufferWithContentsOfFile (← getLeanHBcPath).toString
         let modruntime ← LLVM.parseBitcode llvmctx membuf
         LLVM.linkModules (dest := emitLLVMCtx.llvmmodule) (src := modruntime)
         optimizeLLVMModule emitLLVMCtx.llvmmodule
         LLVM.writeBitcodeToFile emitLLVMCtx.llvmmodule filepath
         let tripleStr := tripleStr?.getD (← LLVM.getDefaultTargetTriple)
         let target ← LLVM.getTargetFromTriple tripleStr
         let cpu := "generic"
         let features := ""
         let targetMachine ← LLVM.createTargetMachine target tripleStr cpu features
         let codegenType := LLVM.CodegenFileType.ObjectFile
         LLVM.targetMachineEmitToFile targetMachine emitLLVMCtx.llvmmodule (filepath ++ ".o") codegenType
         LLVM.disposeModule emitLLVMCtx.llvmmodule
         LLVM.disposeTargetMachine targetMachine
  | .error err => throw (IO.Error.userError err)
end Lean.IR
