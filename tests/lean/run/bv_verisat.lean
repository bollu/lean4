import Std.Tactic.BVDecide

set_option trace.Meta.Tactic.sat true

theorem eg1 (x : BitVec 1) : (x = 1#1) ∨ (x = 0#1) := by
  bv_normalize
  -- bv_decide -- LRAT: '[addEmpty (id: 3) (hints: #[1, 2])]'
  bv_decide (config := { satBackend := .verisat }) -- LRAT of Unsat proof: [addEmpty (id: 2) (hints: #[1, 0])]


theorem eg100 (x y : BitVec 2) : x = 0#2 ∨ x = 1#2 ∨ x = 3#2 ∨ x = 2#2 := by
  bv_normalize
  -- bv_decide
  bv_decide (config := { satBackend := .verisat })

theorem eg2 (x y : BitVec 1) : x * y = y * x := by
  bv_normalize
  bv_decide (config := { satBackend := .verisat })

set_option trace.Meta.Tactic.sat true in
theorem eg3 (x y : Bool) :
    ((x || y) && (x || !y) && (!x || y) && (!x || !y)) = false := by
  bv_normalize
  -- [Meta.Tactic.sat] CNF: '[[(9, true)],
  --    [(9, false), (7, true)],
  --    [(9, false), (8, false)],
  --    [(9, true), (7, false), (8, true)],
  --    [(8, false), (1, true)],
  --    [(8, false), (2, true)],
  --    [(8, true), (1, false), (2, false)],
  --    [(7, false), (5, true)],
  --    [(7, false), (6, false)],
  --    [(7, true), (5, false), (6, true)],
  --    [(6, false), (1, true)],
  --    [(6, false), (2, false)],
  --    [(6, true), (1, false), (2, true)],
  --    [(5, false), (3, false)],
  --    [(5, false), (4, false)],
  --    [(5, true), (3, true), (4, true)],
  --    [(4, false), (1, false)],
  --    [(4, false), (2, true)],
  --    [(4, true), (1, true), (2, false)],
  --    [(3, false), (1, false)],
  --    [(3, false), (2, false)],
  --    [(3, true), (1, true), (2, true)],
  --    [(2, true), (11, false)],
  --    [(2, false), (11, true)],
  --    [(1, true), (10, false)],
  --    [(1, false), (10, true)]]'
  -- =================================
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
  -- =================================
-- [Meta.Tactic.sat] LRAT of Unsat proof: [addRup #[-3, -2, -1] (id : 27) (hints: #[1, 3, 7]),
--      addRup #[-2, -1] (id : 28) (hints: #[2, 13, 1, 27, 9]),
--      addRup #[-3, -1] (id : 29) (hints: #[2, 8, 1, 19, 15, 28]),
--      addRup #[-1] (id : 30) (hints: #[2, 22, 14, 8, 1, 29, 28]),
--      addRup #[-3, -2] (id : 31) (hints: #[1, 3, 7]),
--      addRup #[-2] (id : 32) (hints: #[2, 13, 1, 31, 9]),
--      addRup #[-3] (id : 33) (hints: #[2, 8, 1, 19, 32, 15]),
--      addEmpty (id: 34) (hints: #[33, 2, 22, 14, 8, 1, 32])]
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
