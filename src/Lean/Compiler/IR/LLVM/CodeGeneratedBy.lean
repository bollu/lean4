/-
Copyright (c) 2023 Siddharth Bhat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat
-/
import Lean.Compiler.IR.LLVM.Pure
import Lean.Compiler.ExternAttr

namespace Lean.IR.LLVM.CodeGeneratedBy
open Lean
open Lean.IR.LLVM.Pure

def CodeGenerator : Type := Array Reg → BuilderM Reg

instance : Inhabited CodeGenerator where
  default := fun _ => pure (0 : Reg)

private unsafe def lookupCodeGeneratorFromNameUnsafe (name : Name) (env : Environment) (opt : Options) : Except String CodeGenerator := do
  env.evalConst CodeGenerator opt name

/-- Unsafely lookup a declaration, and cast its value into a code generator -/
@[implemented_by lookupCodeGeneratorFromNameUnsafe]
private opaque lookupCodeGeneratorFromName (name : Name) (env : Environment) (opt : Options) : Except String CodeGenerator

/-- Get the LLVM code generator for a given declaration name if present -/
def getCodeGeneratorFromEnv? (name : Name) (env : Environment) (opt : Options) : Except String (Option CodeGenerator) := do
  let some externData := getExternAttrData? env name | return none
  let some externEntry := getExternEntryFor externData `llvm | return none
  match externEntry with
  | .codeGeneratedBy generator => lookupCodeGeneratorFromName generator env opt
  | _ => return none

end Lean.IR.LLVM.CodeGeneratedBy
