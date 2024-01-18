/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat

This file constructs the bounded recursion principles from the raw
primitive recursor.

Recall that the bounded recursion principle, also known
as "course of values recursion",
(https://en.wikipedia.org/wiki/Course-of-values_recursion),
allows a function definition of `f(n)` to refer to the previous
values of function `f(n-1), f(n-2), ..., f(n-k)` for a constant `k`.
-/

/-
Porting functions from:
https://github.com/leanprover/lean4/blob/684f32fabe06a33c77973af7e4f4f9acfa1fc087/src/library/constructions/brec_on.cpp#L361

This connects to lean from:
https://github.com/leanprover/lean4/blob/7c38649527c85116345df831254985afa2680dd0/src/Lean/Meta/Constructions.lean#L11-L31
-/
import Lean.AuxRecursor
import Lean.Meta.AppBuilder

namespace Lean

namespace BrecOn
@[extern "lean_mk_cases_on"] opaque mkCasesOnImp (env : Environment) (declName : @& Name) : Except KernelException Environment
@[extern "lean_mk_rec_on"] opaque mkRecOnImp (env : Environment) (declName : @& Name) : Except KernelException Environment
@[extern "lean_mk_no_confusion"] opaque mkNoConfusionCoreImp (env : Environment) (declName : @& Name) : Except KernelException Environment
@[extern "lean_mk_below"] opaque mkBelowImp (env : Environment) (declName : @& Name) : Except KernelException Environment
@[extern "lean_mk_ibelow"] opaque mkIBelowImp (env : Environment) (declName : @& Name) : Except KernelException Environment
@[extern "lean_mk_brec_on"] opaque mkBRecOnImp (env : Environment) (declName : @& Name) : Except KernelException Environment
@[extern "lean_mk_binduction_on"] opaque mkBInductionOnImp (env : Environment) (declName : @& Name) : Except KernelException Environment

variable [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m]

@[inline] private def adaptFn (f : Environment → Name → Except KernelException Environment) (declName : Name) : m Unit := do
  let env ← ofExceptKernelException (f (← getEnv) declName)
  modifyEnv fun _ => env

def mkCasesOn (declName : Name) : m Unit := adaptFn mkCasesOnImp declName
def mkRecOn (declName : Name) : m Unit := adaptFn mkRecOnImp declName
def mkNoConfusionCore (declName : Name) : m Unit := adaptFn mkNoConfusionCoreImp declName

def mkBelow_ (declName : Name) : m ConstantInfo := sorry
/-
Run the C++ implementation of mkBelow, and compare the output to our
version in mkBelow_
-/
def mkBelow (declName : Name) : m Unit := do
  adaptFn mkBelowImp declName
  let e <- getEnv
  let correct <-  
    match e.find? declName with
    | .some v => pure v
    | .none => error "cannot find declaration '{declName}'"
  let out <- mkBelow_ declName
  if correct /= out 
  then error "incorrect output from mkBelow"
  else pure ()

def mkIBelow (declName : Name) : m Unit := adaptFn mkIBelowImp declName
def mkBRecOn (declName : Name) : m Unit := adaptFn mkBRecOnImp declName
def mkBInductionOn (declName : Name) : m Unit := adaptFn mkBInductionOnImp declName
end BrecOn

end Lean
