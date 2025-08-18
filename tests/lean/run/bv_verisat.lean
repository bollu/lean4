import Std.Tactic.BVDecide


theorem eg1 (x : BitVec 1) : (x = 1#1) ∨ (x = 0#1) := by
  bv_normalize
  bv_decide (config := { satBackend := .verisat })

#print axioms eg1

theorem eg2 (x y : BitVec 1) : x * y = y * x := by
  bv_normalize
  bv_decide (config := { satBackend := .verisat })

set_option trace.Meta.Tactic.sat true in
theorem eg3 (x : BitVec 2) : x  = 0#2 ∨ x = 3#2 ∨ x = 1#2 := by
  bv_normalize
  bv_decide (config := { satBackend := .verisat })


/--
error: The prover found a counterexample, consider the following assignment:
x = 0#1
-/
#guard_msgs in theorem eg4 (x : BitVec 1) : (x = 1#1) := by
  bv_normalize
  bv_decide (config := { satBackend := .verisat })
