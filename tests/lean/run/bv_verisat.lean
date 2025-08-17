import Std.Tactic.BVDecide

theorem eg1 (x y : BitVec 3) : y + x + y = x + 2 * y := by
  bv_normalize
  bv_decide (config := { satBackend := .verisat })
#print eg1

theorem eg2 (x y : BitVec 3) : x * y = y * x := by
  bv_decide (config := { satBackend := .verisat })
#print eg2
