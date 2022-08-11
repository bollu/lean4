structure Foo := (x : Nat) (y : Float)

@[noinline] def mkFoo (x : Nat) : Foo := { x := x, y := x.toFloat / 3 }

def tst2 (x : Nat) : IO Unit := do
  let foo := mkFoo x;
  IO.println foo.y;


def main : IO Unit := do
  tst2 7;
