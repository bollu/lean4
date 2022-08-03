--  RUN: ./run-lean.sh %s | FileCheck %s --check-prefix=CHECK-INTERPRET
--  RUN: ./validate-lean.sh %s 


-- | check that we generate pap and papExtend.
-- CHECK: lz.pap
-- CHECK: lz.papExtend

-- makeList: 
-- 1 2 3 4 5

-- INCREMENT: 
-- 2 3 4 5 6

-- 1 + 2 + 3 + 4 + 5 + 5 = 15 + 5 = 20
-- CHECK-INTERPRET: 20

set_option trace.compiler.ir.init true
set_option compiler.extract_closed false

-- | this produces a papExtend
def ap10 (f: Nat -> Nat -> Nat): Nat -> Nat := f 10
def replicate2 (f: Nat -> Nat -> Nat)  (x: Nat) : Nat := f x x
def add3 (x: Nat) (y: Nat) (z: Nat) : Nat := x + y + z
def foo: Unit -> Nat
 | _ => replicate2 (add3 10) 20
