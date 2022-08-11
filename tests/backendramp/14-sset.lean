structure Foo :=
  (x : Nat)
  (w : UInt64)

@[noinline] def mkFoo (x : Nat) : Foo :=
  { x := x, w := x.toUInt64 }

def tst2 (x : Nat) : IO Unit := do
  let foo := mkFoo x;
  IO.println foo.x;
  IO.println foo.w;

def main : IO Unit := do
  tst2 7;
