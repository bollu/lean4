import Std.Tactic.BVDecide


theorem eg1 (x : BitVec 1) : (x = 1#1) ∨ (x = 0#1) := by
  bv_normalize
  bv_decide (config := { satBackend := .verisat })

#print axioms eg1

theorem eg2 (x y : BitVec 1) : x * y = y * x := by
  bv_normalize
  bv_decide (config := { satBackend := .verisat })

set_option trace.Meta.Tactic.sat true in
theorem eg3 (x y : Bool) :
    ((x || y) && (x || !y) && (!x || y) && (!x || !y)) = false := by
  bv_normalize
  -- bv_decide
  bv_decide (config := { satBackend := .verisat })



set_option trace.Meta.Tactic.sat true in
theorem eg4 (x y : BitVec 1) :
    ((x ||| y) &&& (x ||| ~~~ y) &&& (~~~ x ||| y) &&& (~~~ x ||| ~~~ y)) =
    0#1 := by
  bv_normalize
  bv_decide (config := { satBackend := .verisat })


/--
error: The prover found a counterexample, consider the following assignment:
x = 0#1
-/
#guard_msgs in theorem eg5 (x : BitVec 1) : (x = 1#1) := by
  bv_normalize
  bv_decide (config := { satBackend := .verisat })
