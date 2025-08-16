module

prelude
-- This module serves as the root of the `Verisat` library.
-- Import modules here that should be built as part of the library.
public import Std.Sat.CNF
public import Std.Tactic.BVDecide.LRAT
public import Std.Data.HashMap
public import Std.Data.HashSet
public import Init.Data.List.Lemmas
public import Init.Data.List.Impl
public import Std.Sat.CNF.Literal

@[expose] public section

namespace Verisat
open Std Sat Tactic BVDecide

structure Var where ofNat ::
  toNat : Nat
deriving DecidableEq, Hashable, Inhabited

/-- Negated variable is '-varId'. -/
structure Lit where ofRawInt ::
  toRawInt : Int32
deriving DecidableEq, Hashable, Inhabited

/-- convert a variable into a literal, given the polarity. -/
def Var.toLit (v : Var) (positive : Bool) : Lit :=
  Lit.ofRawInt <| Int32.ofNat v.toNat * (if positive then 1 else -1)

def Var.toPositiveLit (v : Var) : Lit := v.toLit (positive := true)

def Lit.toVar (l : Lit) : Var :=
    Var.ofNat <| (Int32.abs l.toRawInt).toNatClampNeg

def Lit.positive? (l : Lit) : Bool := l.toRawInt > 0

def Lit.negative? (l : Lit) : Bool := l.toRawInt < 0

/-- negate a literal. -/
def Lit.negate (l : Lit) : Lit where
  toRawInt := - l.toRawInt

/-- convert a literal to an array index. -/
def Lit.toIndex (l : Lit) : Nat :=
  l.toRawInt.abs.toNatClampNeg * 2 + (if l.positive? then 0 else 1)

def Lit.ofIndex (ix : Nat) : Lit :=
    let val := Int32.ofNat (ix / 2)
    Lit.ofRawInt (if ix % 2 == 1 then - val else val)

/-
theorem Lit.ofIndex_toIndex (l : Lit) :
    Lit.ofIndex l.toIndex = l := by
  rcases l with ⟨l⟩
  simp [ofIndex, toIndex, Lit.positive?, Lit.toRawInt]
  sorry
-/


/-- Id of a clause. -/
structure ClauseId where ofUInt32 ::
  toUInt32 : UInt32
deriving DecidableEq, Hashable

def ClauseId.toIndex (cid : ClauseId) : Nat :=
  cid.toUInt32.toNat

/-- A clause is an array of literals. -/
structure Clause where ofArray ::
  toArray : Array Lit
deriving Inhabited

/-- An axiom for showing that computations are inbounds. -/
axiom Inbounds {P : Prop} : P

def Clause.swapIx (c : Clause) (i j : Nat) : Clause where
   toArray :=
     let arr := c.toArray
     arr.swap i j (by exact Inbounds) (by exact Inbounds)

def Clause.size (c : Clause)  : Nat := c.toArray.size

def Clause.ofCNF (c : CNF.Clause Nat) : Clause where
  toArray :=
    c.toArray.map fun (varId, positive) =>
      (Var.ofNat varId).toLit positive

def Clause.get (c : Clause) (ix : Nat) : Lit := c.toArray[ix]!

def Clause.findLitIx (c : Clause) (lit : Lit) (startIx : Nat := 0) :
    Option Nat := Id.run do
  let arr := c.toArray
  for i in [startIx:arr.size] do
    if arr[i]! == lit
    then return some i
  return none


/-- Resolution tree with assumptions for RAT. -/
inductive ResolutionTree
| given (clause : ClauseId)
| branch (lit : Lit) (fals tru : ResolutionTree)
| assumption (lit : Lit) -- TODO: cache these?
deriving Hashable, Inhabited, DecidableEq

namespace ResolutionTree
end ResolutionTree

/-- a boolean which is potentially unassigned. -/
inductive xbool
| tru
| fals
| x
deriving Inhabited, Repr, DecidableEq, Hashable

namespace xbool
def ofBool : Bool → xbool
| true => .tru
| false => .fals

def ofOption : Option Bool → xbool
| some true => .tru
| some false => .fals
| none => .x

def toOption : xbool → Option Bool
| .tru => some true
| .fals => some false
| .x => none

def negate : xbool → xbool
| .tru => .fals
| .fals => .tru
| .x => .x

end xbool

structure State where
  /-- Literals to be propagated, with explanation. -/
  propQ : Queue (Lit × ResolutionTree) := ∅
  /-- UNSAT clause -/
  unsatClause? : Option ClauseId := none
  /-- variable → (assignment, resolution proof explaining assignment -/
  var2assign : Array (Option (Bool × ResolutionTree)) := #[]
  /-- array of clauses, with explanations. -/
  clauses : Array (Clause × ResolutionTree) := #[]
  /-- index from which learnt clauses start. -/
  learntClausesStartIx : Nat := 0
  /-- unassigned variables. Improvement: Switch to using activity. -/
  unassignedVars : Std.HashSet Var := ∅
  /-- Lit → clauses that contain the Lit as a watch. -/
  lit2clauses : Array (Array ClauseId) := ∅
  /-- Lit → clauses that should be watched when Lit is unassigned. -/
  lit2clausesOnUndo : Array (Array ClauseId) := ∅
  /-- array of decisions. -/
  decisionTrail : Array (Lit) := #[]
  /--
  array of literals that were propgated,
  to be unassigned in each level.
  We start with a toplevel undo level, that allows
  unit clauses and conflict clause assignments at the toplevel level,
  before any decisions have been made.
  This corresponds to 'level 0'.
  Decisions are 1-indexed, and the first decision
  occurs on level 1.
  -/
  level2Undo : Array (Array Lit) := #[#[]]

instance : EmptyCollection State where
  emptyCollection := {}

instance : Inhabited State where
  default := ∅


namespace State
def empty : State := ∅

/--
Create a new clause, with optionally an explanation.
If no explanation is given, then a default 'assumption' explanation
is created.
-/
def newClauseWithExplanation (s : State)
    (clause : Clause) (explanation? : Option ResolutionTree) :
    ClauseId × State :=
  let clauseId := ClauseId.ofUInt32 s.clauses.size
  let explanation := explanation?.getD (.given clauseId)
  let s := { s with clauses := s.clauses.push ⟨clause, explanation⟩ }
  (clauseId, s)

/--
Create a new clause from the problem description.
-/
def newProblemClause (s : State) (clause : Clause) :
    ClauseId × State :=
  newClauseWithExplanation s clause none

/--
Setup the solver state from the given problem.
-/
def newFromProblem (problem : CNF Nat) : State :=
    problem.foldl (init := .empty) fun s clause =>
        s.newProblemClause (Clause.ofCNF clause) |>.snd

def newVar (s : State) : State × Var :=
  let v := Var.ofNat s.var2assign.size
  let s := { s with var2assign := s.var2assign.push none }
  (s, v)

def nVars (s : State) : UInt32 := s.var2assign.size

/-- Evaluate a variable. -/
def evalVar (s : State) (v : Var) : xbool :=
  s.var2assign[v.toNat]! |>.map Prod.fst |> xbool.ofOption

def evalLit (s : State) (l : Lit) : xbool :=
    let val := s.evalVar l.toVar
    if l.positive? then val else val.negate


def isUnsat (s : State) : Bool := s.unsatClause?.isSome

def dequePropQ (s : State) : Option ((Lit × ResolutionTree) × State) :=
  if let some (val, propQ) := s.propQ.dequeue? then
    some (val, { s with propQ := propQ })
  else
    none

def assert [Repr α] (s : State) (_b : Bool) (_msg : Unit → α) : State :=
  s

def unwrapOption [Inhabited α] (s : State) (a? : Option α) : α × State :=
   match a? with
   | none =>
     dbg_trace "unable to unwrap option."
     (default, s)
   | some a => (a, s)


private def traverse {α : Type} (xs : Array (Option α)) :
    Option (Array α) := Id.run do
  let mut out := #[]
  for x? in xs do
    if let some x := x? then
      out := out.push x
    else
      return none
  return out

/--
Produce a model from the state.
-/
def model? (s : State) : Option (Array Bool) :=
    let var2obool : Array (Option Bool) := s.var2assign.map
      (fun oval => oval.map Prod.fst)
    traverse var2obool

end State



inductive FindNonFalseLitResult
| tru
| unassigned (lit : Lit) (clauseIx : Nat)
| allFalse

def State.findNonFalseLit
    (s : State) (cid : ClauseId) (startIx : Nat) :
    FindNonFalseLitResult := Id.run do
  for i in [startIx:s.clauses[cid.toIndex]!.fst.size] do
    let lit := s.clauses[cid.toIndex]!.fst.get i
    let val := s.evalLit lit
    if val = .tru then
      return .tru
    else if val = .x then
      return .unassigned lit i
  return .allFalse


/-- Makes a new conflict clause from a given clause. -/
def State.mkConflictClause (s : State) (cid : ClauseId)
    : ClauseId × State := Id.run do
  let mut clause : Array Lit := #[]
  let mut clauseProof : ResolutionTree := .given cid
  for lit  in s.decisionTrail do
    clause := clause.push lit.negate
    let litProof := .assumption lit
    clauseProof := .branch lit (fals:= clauseProof) (tru := litProof)
  s.newClauseWithExplanation (Clause.ofArray clause) clauseProof


/-- undo the assignment of the given literal. -/
def State.undoAssignment (s : State) (lit : Lit) : State := Id.run do
  let mut s := s
  -- delete assignment.
  s := { s with var2assign :=
    s.var2assign.set! (lit.toVar.toNat) none }
  s := { s with lit2clauses :=
    s.lit2clauses.set! lit.toIndex (s.lit2clausesOnUndo[lit.toIndex]!)
  }
  -- note that the variable is unassigned.
  s := { s with unassignedVars :=
      s.unassignedVars.insert lit.toVar
    }
  s

/--
Whether we have decisions, or whether a toplevel conflict
has been found.
-/
def State.lastDecision? (s : State) : Option Lit := s.decisionTrail.back?

/-- undo a single decision. -/
def State.undoOneDecision (s : State) : State := Id.run do
  let lit := s.decisionTrail.back!
  let s := s.undoAssignment lit
  let s := { s with decisionTrail := s.decisionTrail.pop }
  let assigns := s.level2Undo.back!
  let s := { s with level2Undo := s.level2Undo.pop }
  let mut s := s
  for assign in assigns do
    s := s.undoAssignment assign
  s

/-- Add a literal for propgation. -/
def State.enqueuePropQ (s : State) (lit : Lit) (reason : ResolutionTree) : State :=
  { s with propQ := s.propQ.enqueue (lit, reason) }

/-- empty the propgation queue. -/
def State.emptyPropQ (s : State) : State :=
  { s with propQ := .empty }

/-- Add a clause to the watched clauses of this literal. -/
def State.watchClauseAtLit (s : State) (cid : ClauseId) (lit : Lit) : State :=
  { s with lit2clauses :=
      s.lit2clauses.modify lit.toIndex fun clauses =>
        clauses.push cid
  }

/-- Get all watched clauses for a literal, and clear the watched clauses list. -/
def State.getAndClearWatchedClausesAtLit (s : State) (lit : Lit) :
    Array ClauseId × State :=
  let clauses := s.lit2clauses[lit.toIndex]!
  let s := { s with lit2clauses := s.lit2clauses.set! lit.toIndex #[] }
  (clauses, s)


/-- Propagate a literal assignment of lit 'Lit' in clause 'clauseId'. -/
def State.propagateLitInClause (s : State)
  (_lit : Lit) (reason: ResolutionTree)
  (cid : ClauseId) :
    State := Id.run do
  match s.findNonFalseLit cid 0 with
  | .allFalse =>
    /-
    We've found a conflict clause. Flush the queue,
    add the clause.
    -/
    let s := s.emptyPropQ
    let (conflictId, s) := s.mkConflictClause cid
    if let some _lit := s.lastDecision? then
      -- We have not found UNSAT, but we have found a conflict.
      -- return the conf, _)lict clause.
      let s := s.undoOneDecision
      s
    else
      -- We have found UNSAT.
      let s := { s with unsatClause? := some conflictId }
      return s
    | .tru => s -- nothing to propagate, clause has 'true' in it.
    | .unassigned lit litIx =>
        -- hurray, we have a watched literal.
        -- check if it's the *only* unassigned literal.
        -- If it is, propagate.
        -- If not, swap it with lit[0], and make it watched.
        match s.findNonFalseLit cid (litIx + 1) with
        | .tru => s -- nothing to do, we have a true literal.
        | .unassigned _lit' _litIx' =>
            -- we have another unassigned literal, so we
            -- cannot propagate.
            -- Swap clause[0] with clause[litIx],
            -- watch clause[0], and continue on our way.
            let s := { s with clauses :=
              s.clauses.modify cid.toIndex fun (c, tree) =>
                (c.swapIx 0 litIx, tree)
            }
            let s := s.watchClauseAtLit cid lit
            s
        | .allFalse =>
            -- we have no other unassigned literals,
            -- so we can propagate!
            let reason : ResolutionTree :=
               .branch lit (.given cid) reason
            s.enqueuePropQ lit reason

def State.propagate (s : State) : State := propagateAux s where
  propagateAux (s : State) : State := Id.run do
    if let some ((lit, litProof), s) := s.dequePropQ then
      let (watchedClauses, s) := s.getAndClearWatchedClausesAtLit lit
      let mut s := s
      for clauseId in watchedClauses do
         s := s.propagateLitInClause lit litProof clauseId
         if s.unsatClause?.isSome then return s
      s
    else s

inductive SatSolveResult
| sat
| unsat
| nofuel
deriving DecidableEq, Inhabited

def State.getUnassignedVar (s : State) : Option Var :=
  (s.var2assign.findIdx? fun val => val.isNone).map Var.ofNat

/-- Solve. -/
partial def State.solve (s : State) : SatSolveResult × State :=
  if s.unsatClause?.isSome then (.unsat, s)
  else
    if let some v := s.getUnassignedVar
    then
      let vlit := v.toPositiveLit
      let vproof := .assumption vlit
      let s := { s with var2assign := s.var2assign.set! v.toNat (some (true, vproof)) }
      let s := { s with decisionTrail := s.decisionTrail.push vlit }
      let s := { s with level2Undo := s.level2Undo.push #[] }
      let s := s.enqueuePropQ vlit vproof
      let s := s.propagate
      s.solve
    else -- TODO: I need to get some variable from the HashSet.
      (.sat, s)


end Verisat
