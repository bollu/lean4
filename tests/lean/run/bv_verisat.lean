import Std.Tactic.BVDecide

set_option trace.Meta.Tactic.sat true
theorem eg1 (x y : BitVec 1) : (x ||| y) = 1#1 := by
  bv_decide (config := { satBackend := .verisat })
#print eg1

theorem eg2 (x y : BitVec 3) : x * y = y * x := by
  bv_decide (config := { satBackend := .verisat })
#print eg2
