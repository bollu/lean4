import Lean
--
--open Lean Compiler IR LLVM Pure CodeGeneratedBy
--
--def Real : Type := UInt64
--
--instance : Inhabited Real where
--  default := (0 : UInt64)
--
--@[codeGeneratedBy real42impl]
--def real42 : Real := default
--
--
--@[codeGeneratedBy realaddimpl]
--opaque realadd : Real → Real → Real
--

def stuff : IO Unit := do
  let mut xs := #[]
  for i in [0:100:2] do
    xs := xs.push i
  IO.println s!"{xs}"

def main : IO Unit := do
  allocprof (msg := "hello there") stuff
#eval main
