/-
Copyright (c) 2023 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Siddharth Bhat
-/

import Lean.Data.HashMap
import Lean.Compiler.IR.LLVM.LLVMBindings

namespace Lean.Compiler.LLVM.Pure

declare_syntax_cat llvm_ty
declare_syntax_cat llvm_assignment
declare_syntax_cat llvm_instr
declare_syntax_cat llvm_terminator
declare_syntax_cat llvm_bb
-- may need function_def, function_decl
declare_syntax_cat llvm_function
declare_syntax_cat llvm_global

inductive Ty where
| function (args : Array Ty) (ret : Ty)
| void
| int (width : UInt64)
| opaquePointer (addrspace : UInt64 := 0)
| float
| double
| array (elemty : Ty) (nelem : UInt64)
deriving Inhabited, BEq

scoped syntax llvm_ty " (" (llvm_ty),* ")" : llvm_ty
scoped syntax "void" : llvm_ty
scoped syntax "i" noWs num : llvm_ty
scoped syntax "ptr" : llvm_ty
scoped syntax "float" : llvm_ty
scoped syntax "double" : llvm_ty
scoped syntax "[" num " x " llvm_ty "]" : llvm_ty

-- TODO: implement
-- instance : DecidableEq Ty := fun x y => sorry

abbrev BBId := UInt64
abbrev Reg := UInt64

syntax llvm_reg := "%" noWs (num <|> ident)
syntax llvm_bb_label := llvm_reg
syntax llvm_sym := "@" noWs (num <|> ident)
syntax llvm_value := llvm_reg -- TODO: extend with LLVM constants on demand

inductive Instruction where
| alloca (ty : Ty) (name : String)
| load2 (ty : Ty) (val : Reg) (name : String)
| store (val pointer : Reg)
| gep (ty : Ty) (base : Reg) (ixs : Array Reg)
| inboundsgep (ty : Ty) (base : Reg) (ixs : Array Reg)
| sext (val : Reg) (destTy : Ty) -- TODO: add source type argument.
| zext (val : Reg) (destTy : Ty) -- TODO: add source type argument.
| sext_or_trunc (val : Reg) (destTy : Ty) -- TODO: remove pseudo-instruction, provide builder.
| ptrtoint (pointer : Reg) (destTy : Ty)
| mul (lhs rhs : Reg) (name : String)
| add (lhs rhs : Reg) (name : String)
| sub (lhs rhs : Reg) (name : String)
| not (arg : Reg) (name : String) -- -- TODO: remove pseudo-instruction, provide builder.
| icmp (pred : LLVM.IntPredicate) (lhs rhs : Reg) (name : String)
| phi (ty : Ty) (args : Array (BBId × Reg))
deriving Inhabited, BEq

scoped syntax "alloca" llvm_ty : llvm_instr
scoped syntax "load" llvm_ty ", " "ptr" llvm_reg : llvm_instr
scoped syntax "store" llvm_ty llvm_value : llvm_instr
scoped syntax "getelemenptr" ("inbounds")? llvm_ty ", " "ptr" llvm_reg (llvm_ty llvm_reg)* : llvm_instr
scoped syntax "sext" llvm_ty llvm_reg "to" llvm_ty : llvm_instr
scoped syntax "zext" llvm_ty llvm_reg "to" llvm_ty : llvm_instr
scoped syntax "sext_or_trunc" llvm_ty llvm_reg "to" llvm_ty : llvm_instr
scoped syntax "ptrtoint" llvm_ty llvm_reg "to" llvm_ty : llvm_instr
scoped syntax "mul" llvm_ty llvm_reg ", " llvm_reg : llvm_instr
scoped syntax "add" llvm_ty llvm_reg ", " llvm_reg : llvm_instr
scoped syntax "sub" llvm_ty llvm_reg ", " llvm_reg : llvm_instr
scoped syntax "not" llvm_ty llvm_reg : llvm_instr

syntax llvm_icmp_op := ("eq" <|> "ne" <|> "ugt" <|> "uge" <|> "ult" <|> "ule" <|> "sgt" <|> "sge" <|> "slt" <|> "sle")
scoped syntax "icmp" llvm_icmp_op llvm_ty llvm_reg ", " llvm_reg : llvm_instr
scoped syntax "phi" llvm_ty ("[" llvm_value ", " llvm_bb_label "]") : llvm_instr

-- TODO: check why we do not need 'fmul' etc.

abbrev InsertionPoint := BBId

inductive Terminator where
| default
| unreachable
| br (bbid : BBId)
| condbr (val : Reg) (then_ else_ : BBId)
| ret (val : Reg)
| switch (val : Reg) (cases : Array (Reg × BBId)) (default : BBId)

scoped syntax "unreachable" : llvm_terminator
scoped syntax "br" "label" llvm_bb_label : llvm_terminator
scoped syntax "br" "i1" llvm_reg
   ", " "label" llvm_bb_label
   ", " "label" llvm_bb_label : llvm_terminator
scoped syntax "ret" llvm_ty llvm_value : llvm_terminator
scoped syntax "switch"  llvm_ty llvm_value ", "
  "label" llvm_bb_label
     "[" (llvm_ty llvm_reg ", " "label" llvm_bb_label )* "]" : llvm_terminator

abbrev Arg := String × Ty
structure BasicBlock where
  id : BBId
  name : String
  instrs : Array Instruction
  terminator : Terminator

syntax llvm_assignment := llvm_reg " = " llvm_instr
scoped syntax ident noWs ":"
  colGt linebreak
    (colEq (llvm_assignment <|> llvm_instr) linebreak)*
    llvm_terminator : llvm_bb

structure FunctionDeclaration where
  name : String
  args : Array Arg
  retty : Ty

scoped syntax "declare" llvm_ty llvm_sym "(" (llvm_ty),* ")" : llvm_function

structure FunctionDefinition extends FunctionDeclaration where
  body : Array BBId

scoped syntax "define" llvm_ty llvm_sym "(" (llvm_ty llvm_reg),* ")"
  "{" (llvm_bb)* "}": llvm_function

structure GlobalDeclaration where
  name : String
  ty : Ty

scoped syntax llvm_sym " = " ("global" <|> "constant")  llvm_ty : llvm_global

abbrev GlobalId := UInt64

inductive Initializer where
| zero -- zero initialize.
| undef -- leave undefiend.
| string (string : String)

-- TODO: convert strings to array constants
syntax llvm_initializer := ("zeroinitializer" <|> "undef" <|> str)

structure GlobalDefinition extends GlobalDeclaration where
  initializer : Initializer

scoped syntax llvm_sym " = " ("global" <|> "constant")
  llvm_ty llvm_initializer : llvm_global

scoped syntax "[llvm_ty|" llvm_ty "]" : term
scoped syntax "[llvm_assignment|" llvm_assignment "]" : term
scoped syntax "[llvm_instr|" llvm_instr "]" : term
scoped syntax "[llvm_terminator|" llvm_terminator "]" : term
scoped syntax "[llvm_bb|" llvm_bb "]" : term
scoped syntax "[llvm_function|" llvm_function "]" : term
scoped syntax "[llvm_global|" llvm_global "]" : term

abbrev FunctionId := UInt64

structure BuilderState where
  instrs : HashMap Reg Instruction
  bbs : HashMap BBId BasicBlock

  functionDefs : HashMap FunctionId FunctionDefinition
  functionDecls : HashMap FunctionId FunctionDeclaration

  globalDefs : HashMap GlobalId GlobalDeclaration
  globalDecls : HashMap GlobalId GlobalDefinition

  reg : UInt64
  bbid : UInt64

  insertionpt : Option InsertionPoint

abbrev BuilderT (m : Type → Type) [STWorld β m] (α : Type) := StateRefT BuilderState m α
abbrev BuilderM := BuilderT IO

structure InstantiationContext (llvmctx : LLVM.Context) where
  llvmmodule : LLVM.Module llvmctx
  llvmbuilder : LLVM.Builder llvmctx
  registerFile : HashMap Reg (LLVM.Value llvmctx)
  basicBlocks : HashMap BBId (LLVM.BasicBlock llvmctx)
  functions : HashMap String (LLVM.Value llvmctx)

abbrev InstantiationM (llvmctx : LLVM.Context) (α : Type) : Type :=
  ReaderT BuilderState (StateRefT (InstantiationContext llvmctx) IO) α

def getLLVMBuilder : InstantiationM llvmctx (LLVM.Builder llvmctx) :=
  InstantiationContext.llvmbuilder <$> get

def getBuilderState : InstantiationM llvmctx BuilderState :=
   read


def getModule : InstantiationM llvmctx (LLVM.Module llvmctx) :=
  InstantiationContext.llvmmodule <$> get
def getRegisterFile : InstantiationM llvmctx (HashMap Reg (LLVM.Value llvmctx)) :=
  InstantiationContext.registerFile <$> get

def getBasicBlocks : InstantiationM llvmctx (HashMap BBId (LLVM.BasicBlock llvmctx)) :=
  InstantiationContext.basicBlocks <$> get

def getFunctions : InstantiationM llvmctx (HashMap String (LLVM.Value llvmctx)) :=
  InstantiationContext.functions <$> get

partial def Ty.instantiate : Ty → InstantiationM llvmctx (LLVM.LLVMType llvmctx)
| .function args retTy => do
  LLVM.functionType (← retTy.instantiate) (← args.mapM Ty.instantiate)
| .void => LLVM.voidType llvmctx -- TODO: change function name to `LLVM.voidTypeInContext`
| .int width => LLVM.intTypeInContext llvmctx width
| .opaquePointer addrspace => LLVM.opaquePointerTypeInContext llvmctx addrspace
| .float => LLVM.floatTypeInContext llvmctx
| .double => LLVM.doubleTypeInContext llvmctx
| .array elemty nelem => do LLVM.arrayType (← elemty.instantiate) nelem

def FunctionDeclaration.instantiate (decl : FunctionDeclaration) : InstantiationM llvmctx (LLVM.Value llvmctx) := do
  let fnty ← (Ty.function (decl.args.map Prod.snd) decl.retty).instantiate
  let fn ← LLVM.getOrAddFunction (← getModule) decl.name fnty
  modify (fun s => { s with functions := s.functions.insert decl.name fn })
  return fn


def Reg.instantiate (reg : Reg) : InstantiationM llvmctx (LLVM.Value llvmctx) := do
  match (← getRegisterFile).find? reg with
  | .none => throw <| .userError s!"unable to find register '{reg}', this is a miscompilation."
  | .some v => return v

def BBId.instantiate (bbid : BBId) : InstantiationM llvmctx (LLVM.BasicBlock llvmctx) := do
  match (← getBasicBlocks).find? bbid with
  | .none => throw <| .userError s!"unable to find basic block '{bbid}', this is a miscompilation."
  | .some v => return v

def Instruction.instantiate : Instruction → InstantiationM llvmctx (LLVM.Value llvmctx)
| .alloca ty name => do
   LLVM.buildAlloca (← getLLVMBuilder) (← ty.instantiate) name
| .load2 ty val name => do
    LLVM.buildLoad2 (← getLLVMBuilder) (← ty.instantiate) (← val.instantiate) name
| .store val pointer => do
    LLVM.buildStore (← getLLVMBuilder) (← val.instantiate) (← pointer.instantiate)
| .gep ty base ixs => do
  LLVM.buildGEP2 (← getLLVMBuilder) (← ty.instantiate) (← base.instantiate) (← ixs.mapM Reg.instantiate)
| .inboundsgep ty base ixs => do
  LLVM.buildInBoundsGEP2 (← getLLVMBuilder) (← ty.instantiate) (← base.instantiate) (← ixs.mapM Reg.instantiate)
| .sext val destTy => do
  LLVM.buildSext (← getLLVMBuilder) (← val.instantiate) (← destTy.instantiate)
| .zext val destTy => do
  LLVM.buildZext (← getLLVMBuilder) (← val.instantiate) (← destTy.instantiate)
| .sext_or_trunc val destTy => do
  LLVM.buildSextOrTrunc (← getLLVMBuilder) (← val.instantiate) (← destTy.instantiate)
| .ptrtoint pointer destTy => do
  LLVM.buildPtrToInt (← getLLVMBuilder) (← pointer.instantiate) (← destTy.instantiate)
| .mul lhs rhs name => do
  LLVM.buildMul (← getLLVMBuilder) (← lhs.instantiate) (← rhs.instantiate) name
| .add lhs rhs name => do
  LLVM.buildAdd (← getLLVMBuilder) (← lhs.instantiate) (← rhs.instantiate) name
| .sub lhs rhs name => do
  LLVM.buildSub (← getLLVMBuilder) (← lhs.instantiate) (← rhs.instantiate) name
| .not arg name => do
  LLVM.buildNot (← getLLVMBuilder) (← arg.instantiate) name
| .icmp pred lhs rhs name => do
  LLVM.buildICmp (← getLLVMBuilder) pred (← lhs.instantiate) (← rhs.instantiate) name
| .phi ty bbIdAndVals => do
  let phiNode ← LLVM.buildPhi (← getLLVMBuilder) (← ty.instantiate)
  let vals : Array (LLVM.Value llvmctx) ← bbIdAndVals.mapM (Reg.instantiate ∘ Prod.snd)
  let bbs : Array (LLVM.BasicBlock llvmctx) ← bbIdAndVals.mapM (BBId.instantiate ∘ Prod.fst)
  LLVM.addIncoming phiNode vals bbs
  return phiNode

def reassureUserString : String := "This is a compiler bug."

def findBasicBlock! (bbid : BBId) : InstantiationM llvmctx (LLVM.BasicBlock llvmctx) := do
  let some bb := (← getBasicBlocks).find? bbid
    | throw <| .userError s!"Unable to find LLVM basic block {bbid}. {reassureUserString}"
  return bb

def findReg! (reg : Reg) : InstantiationM llvmctx (LLVM.Value llvmctx) := do
  let some v := (← getRegisterFile).find? reg
    | throw <| .userError s!"UnabuildRetble to find LLVM value {reg}. {reassureUserString}"
  return v

def Terminator.instantiate : Terminator → InstantiationM llvmctx (LLVM.Value llvmctx)
| .default => throw <| .userError s!"should not have default when instantiating terminator. {reassureUserString}"
| .unreachable => do LLVM.buildUnreachable (← getLLVMBuilder)
| .br bbid => do
    LLVM.buildBr (← getLLVMBuilder) (← findBasicBlock! bbid)
| .condbr val then_ else_ => do
    LLVM.buildCondBr (← getLLVMBuilder) (← findReg! val) (← findBasicBlock! then_) (← findBasicBlock! else_)
| .ret val => do LLVM.buildRet (← getLLVMBuilder) (← findReg! val)
| .switch val cases defCase => do
    let switchInstr ← LLVM.buildSwitch (← getLLVMBuilder) (← findReg! val) (← findBasicBlock! defCase)
                    (UInt64.ofNat cases.size)
    cases.forM (fun (val, bb) => do LLVM.addCase switchInstr (← findReg! val) (← findBasicBlock! bb))
    return switchInstr

def FunctionDefinition.instantiate (defn : FunctionDefinition) : InstantiationM llvmctx Unit := do
  let some llvmfn := (← getFunctions).find? defn.name
    | throw <| .userError s!"Unable to find LLVM function declaration for {defn.name}. {reassureUserString}"

  let mut llvmbbs : Array (BasicBlock × LLVM.BasicBlock llvmctx) :=
    Array.mkEmpty defn.body.size
  -- generate basic blocks. Only after generating all the basic blocks
  -- do we fill them in with instructions to allow for mutual dependencies in
  -- the control flow graph.
  for bbid in defn.body do
    let some bb := (← getBuilderState).bbs.find? bbid
      | throw <| .userError s!"Unable to find LLVM Basic block {bbid}. {reassureUserString}"
    let llvmbb ← LLVM.appendBasicBlockInContext llvmctx llvmfn bb.name
    llvmbbs := llvmbbs.push (bb, llvmbb)
    modify fun s => { s with basicBlocks := s.basicBlocks.insert bbid llvmbb }

  for (bb, llvmbb) in llvmbbs do
      LLVM.positionBuilderAtEnd (← getLLVMBuilder) llvmbb
      bb.instrs.forM (fun instr => do let _ ← Instruction.instantiate instr)
      let _ ← bb.terminator.instantiate

-- create an LLVM module that maps the pure 'BuilderState' into a real LLVM module pointer.
def BuilderState.instantiate (modName : Name) (state : BuilderState) : InstantiationM llvmctx (LLVM.Module llvmctx) := do
  let module ← LLVM.createModule llvmctx modName.toString
  let _builder ← LLVM.createBuilderInContext llvmctx

  -- 1. Create all function declarations up-front, to allow for mutual
  --    definitions
  for (_declName, decl) in (state.functionDecls.toArray) do
    let _ ← decl.instantiate

  for (_defnName, defn) in state.functionDefs.toArray do
    let _ ← defn.toFunctionDeclaration.instantiate
    defn.instantiate
  return module

end Lean.Compiler.LLVM.Pure
