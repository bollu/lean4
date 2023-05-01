/-
Copyright (c) 2023 Siddharth Bhat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat
-/
import Lean.Attributes
import Lean.Environment
import Lean.CoreM
import Lean.Compiler.IR.LLVM.Pure

namespace Lean.IR.LLVM.CodeGeneratedBy
open Lean
open Lean.IR.LLVM.Pure

def CodeGenerator : Type := List Reg → BuilderM Reg

instance : Inhabited CodeGenerator where
  default := fun _ => pure (0 : Reg)

-- Unqualified `getEnv` refers to `CompilerM.getEnv`, which
-- assumes the specific `CompilerM` monad stack, instead of implementing
-- `MonadEnv CompilerM`.
-- Thus, we explicitly refer to `MonadEnv.getEnv`
-- TODO: Refactor `CompilerM` to use `MonadEnv`.

private unsafe def getLLVMCodeGeneratorUnsafe (declName : Name) : CoreM CodeGenerator := do
  ofExcept <| (← MonadEnv.getEnv).evalConstCheck CodeGenerator (← getOptions) ``CodeGenerator declName

/-- Unsafely lookup a declaration, and cast its value into a code generator -/
@[implemented_by getLLVMCodeGeneratorUnsafe]
private opaque lookupCodeGeneratorForDeclaration (declName : Name) : CoreM CodeGenerator

/-- does `PersistentEnvExtension` not know how to use `HashMap` ? -/
builtin_initialize codeGeneratorExt : PersistentEnvExtension Name (Name × CodeGenerator) (HashMap Name CodeGenerator) ←
  registerPersistentEnvExtension {
    mkInitial := return {}
    addImportedFn := fun nss => return ← ImportM.runCoreM $ do
      let mut hm := {}
      for ns in nss do
        for n in ns do
          hm := hm.insert n (← lookupCodeGeneratorForDeclaration n)
      return hm
    addEntryFn := fun hm (name, codegen) => hm.insert name codegen
    exportEntriesFn := fun hm => hm.toArray.map Prod.fst
  }


/-- get the code generator for a given declaration name -/
def getCodeGeneratorFromEnv? (env : Environment) (name : Name) : Option CodeGenerator :=
   codeGeneratorExt.getState env |>.find? name

/-- add a code generator, given the declaration name and the code generator -/
def addCodeGenerator (declName : Name) (gen : CodeGenerator) : CoreM Unit := do
    MonadEnv.modifyEnv fun env => codeGeneratorExt.addEntry env (declName, gen)

/-- add a code generator, given the declaration name -/
def addCodeGeneratorFromDeclName (declName : Name) : CoreM Unit := do
  let info ← getConstInfo declName
  match info.type with
  | .const ``Lean.IR.LLVM.CodeGeneratedBy.CodeGenerator .. =>
    addCodeGenerator declName (← lookupCodeGeneratorForDeclaration declName)
  | _ =>
    throwError "Expected type 'CodeGenerator', found incorrect type '{info.type}'. Invalid code generator declaration '{declName}'."

builtin_initialize
  registerBuiltinAttribute {
    name  := `codeGeneratedBy
    descr := "functions that are code generated by a custom LLVM builder."
    applicationTime := .afterCompilation
    add   := fun declName stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      -- | TODO: what does a global attribute kind mean?
      unless kind == AttributeKind.global do throwError "invalid attribute 'codeGeneratedBy', must be global"
      addCodeGeneratorFromDeclName declName
  }
end Lean.IR.LLVM.CodeGeneratedBy
