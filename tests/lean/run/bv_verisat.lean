import Std.Tactic.BVDecide
set_option trace.Meta.Tactic.sat true
-- set_option trace.Meta.Tactic.bv true
theorem eg1 (x : BitVec 1) : (x = 1#1) ∨ (x = 0#1) := by
  bv_normalize
  bv_decide (config := { satBackend := .verisat })

theorem eg2 (x y : BitVec 1) : x * y = y * x := by
  bv_normalize
  bv_decide (config := { satBackend := .verisat })
#print eg2
