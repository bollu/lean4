namespace Foo
initialize vals : IO.Ref (Array String) ← IO.mkRef #[]

def registerVal (s : String) : IO Unit := do
  if (← vals.get).contains s then
    throw $ IO.userError "value already registered"
  vals.modify (·.push s)

initialize
  registerVal "hello"
end Foo
open Foo

def main : IO Unit := do
  IO.println (← vals.get)
