import Std.Tactic.BVDecide

#check Array Std.Tactic.BVDecide.LRAT.IntAction
set_option trace.Meta.Tactic.sat true
-- set_option trace.Meta.Tactic.bv true
theorem eg1 (x : BitVec 1) : (x = 1#1) ∨ (x = 0#1) := by
  bv_decide (config := { satBackend := .verisat })
#print eg1

theorem eg2 (x y : BitVec 3) : x * y = y * x := by
  bv_decide (config := { satBackend := .verisat })
#print eg2
