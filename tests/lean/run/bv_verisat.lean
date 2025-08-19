import Std.Tactic.BVDecide

set_option trace.Meta.Tactic.sat true

theorem eg1 (x : BitVec 1) : (x = 1#1) ∨ (x = 0#1) := by
  bv_normalize
  -- bv_decide -- LRAT: '[addEmpty (id: 3) (hints: #[1, 2])]'
  bv_decide (config := { satBackend := .verisat }) -- LRAT of Unsat proof: [addEmpty (id: 2) (hints: #[1, 0])]



theorem eg2 (x y : BitVec 1) : x * y = y * x := by
  bv_normalize
  bv_decide (config := { satBackend := .verisat })

set_option trace.Meta.Tactic.sat true in
theorem eg3 (x y : Bool) :
    ((x || y) && (x || !y) && (!x || y) && (!x || !y)) = false := by
  bv_normalize
  bv_decide
  -- [Meta.Tactic.sat] LRAT: '[addRup #[8] (id : 27) (hints: #[1, 2]),
  --    addRup #[-9] (id : 28) (hints: #[1, 3]),
  --    addRup #[-2, -3] (id : 29) (hints: #[28, 7]),
  --    addRup #[6] (id : 30) (hints: #[27, 8]),
  --    addRup #[-7] (id : 31) (hints: #[27, 9]),
  --    addRup #[-2, 3] (id : 32) (hints: #[31, 13]),
  --    addRup #[-4] (id : 33) (hints: #[30, 14]),
  --    addRup #[-5] (id : 34) (hints: #[30, 15]),
  --    addRup #[2, -3] (id : 35) (hints: #[34, 19]),
  --    addRup #[2, 3] (id : 36) (hints: #[33, 22]),
  --    addRup #[-3] (id : 37) (hints: #[29, 35]),
  --    addRup #[-2] (id : 38) (hints: #[37, 32]),
  --    addEmpty (id: 39) (hints: #[38, 37, 36])]'
  -- bv_decide
-- [Meta.Tactic.sat] LRAT of Unsat proof: [addRup #[-3, -2, -1] (id : 26) (hints: #[0, 2, 6]),
--      addRup #[-2, -1] (id : 27) (hints: #[1, 12, 0, 26, 8]),
--      addRup #[-3, -1] (id : 28) (hints: #[1, 7, 0, 18, 14, 27]),
--      addRup #[-1] (id : 29) (hints: #[1, 21, 13, 7, 0, 28, 27]),
--      addRup #[-3, -2] (id : 30) (hints: #[0, 2, 6]),
--      addRup #[-2] (id : 31) (hints: #[1, 12, 0, 30, 8]),
--      addRup #[-3] (id : 32) (hints: #[1, 7, 0, 18, 31, 14]),
--      addEmpty (id: 33) (hints: #[32, 1, 21, 13, 7, 0, 31])]
  -- bv_decide (config := { satBackend := .verisat })


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
