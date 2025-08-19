module

prelude
-- This module serves as the root of the `Verisat` library.
-- Import modules here that should be built as part of the library.
public import Std.Sat.CNF
public import Std.Tactic.BVDecide.LRAT
public import Std.Data.HashMap
public import Std.Data.HashSet
public import Init.Data.Queue
public import Init.Data.List.Lemmas
public import Init.Data.List.Impl
public import Std.Sat.CNF.Literal
public import Lean.CoreM
public import Lean.Message

@[expose] public section

protected def Array.traverse {α : Type} (xs : Array (Option α)) :
    Option (Array α) := do
  let mut out := #[]
  for x? in xs do
    let x ← x?
    out := out.push x
  return out


namespace Verisat
open Std Sat Tactic BVDecide

structure Var where ofRawNatPos ::
  toRawNatPos : Nat
deriving DecidableEq, Hashable, Inhabited

/-- convert a 'Var' (which is a positive natural number) to an array index, which is zero-indexed. -/
def Var.toIndex (v : Var) : Nat :=
  v.toRawNatPos - 1

/-- convert an array index into a 'Var', which converts a zero based offset into a 1-based offset. -/
def Var.ofIndex (ix : Nat) : Var :=
  ofRawNatPos (ix + 1)

instance : Lean.ToMessageData Var where
  toMessageData v := m!"v{v.toRawNatPos}"

/-- Negated variable is '-varId'. -/
structure Lit where ofRawInt32Nonzero ::
  toRawInt32Nonzero : Int32
deriving DecidableEq, Hashable, Inhabited

def Lit.toMessageDataRaw (lit : Lit) :=
  if lit.toRawInt32Nonzero > 0 then m!"+v{lit.toRawInt32Nonzero}" else m!"~v{lit.toRawInt32Nonzero.abs}"


/-- convert a variable into a literal, given the polarity. -/
def Var.toLit (v : Var) (positive : Bool) : Lit :=
  .ofRawInt32Nonzero <| Int32.ofNat v.toRawNatPos * (if positive then 1 else -1)

def Var.toPositiveLit (v : Var) : Lit := v.toLit (positive := true)

def Lit.toVar (l : Lit) : Var :=
    Var.ofRawNatPos <| (Int32.abs l.toRawInt32Nonzero).toNatClampNeg

def Lit.positive? (l : Lit) : Bool := l.toRawInt32Nonzero > 0

def Lit.negative? (l : Lit) : Bool := l.toRawInt32Nonzero < 0

/-- negate a literal. -/
def Lit.negate (l : Lit) : Lit where
  toRawInt32Nonzero := - l.toRawInt32Nonzero

/-- convert a literal to an array index. -/
def Lit.toIndex (l : Lit) : Nat :=
  -- 1 /-1 => [0 * 2, 0 * 2 + 1] => [0, 1]
  -- 2/-2  => [1 * 2, 1 * 2 + 1] => [2, 3]
  -- 3/-3 →  [2 * 2, 2 * 2 + 1] => [4, 5]
  ((l.toRawInt32Nonzero.abs.toNatClampNeg - 1) * 2) + (if l.positive? then 0 else 1)

def Lit.toIntNonzero (l : Lit) : Int :=
  l.toRawInt32Nonzero.toInt



/-- Id of a clause. -/
structure ClauseId where ofUInt32 ::
  toUInt32 : UInt32
deriving DecidableEq, Hashable, Inhabited

/-- print the clause ID as a message. -/
def ClauseId.toMessageDataRaw (cid : ClauseId) : Lean.MessageData :=
  m!"clause({cid.toUInt32})"

def ClauseId.toIndex (cid : ClauseId) : Nat :=
  cid.toUInt32.toNat

/-- The LRAT proof format uses 1-indexing. -/
def ClauseId.toLratPos (cid : ClauseId) : Nat :=
  cid.toUInt32.toNat + 1


def ClauseId.ofIndex (ix : Nat) : ClauseId :=
  ClauseId.ofUInt32 (UInt32.ofNat ix)

/-- A clause is an array of literals. -/
structure Clause where ofArray ::
  toArray : Array Lit
deriving Inhabited

def Clause.toMessageDataRaw (cls : Clause) : Lean.MessageData :=
  m!"[{cls.toArray.map Lit.toMessageDataRaw}]"

/-- An axiom for showing that computations are inbounds. -/
axiom Inbounds {P : Prop} : P

def Clause.size (c : Clause)  : Nat := c.toArray.size

def Clause.ofCNF (c : CNF.Clause Nat) : Clause where
  toArray :=
    c.toArray.map fun (varId, positive) =>
      -- these come from a CNF, which is `([0..n), polarity:true/false)`.
      -- we need to convert it to our representation.
      (Var.ofIndex varId).toLit positive

def Clause.get (c : Clause) (ix : Nat) : Lit := c.toArray[ix]!

def Clause.findLitIx (c : Clause) (lit : Lit) (startIx : Nat := 0) :
    Option Nat := Id.run do
  let arr := c.toArray
  for i in [startIx:arr.size] do
    if arr[i]! = lit
    then return some i
  return none

/-- set the watched literal in this clause. -/
def Clause.swapLitTo0 (c : Clause) (litIx : Nat) : Clause :=
  let arr := c.toArray
  let arr := arr.swap 0 litIx Inbounds Inbounds
  Clause.ofArray arr

def Clause.toIntArray (c : Clause) : Array Int :=
  c.toArray.map Lit.toIntNonzero

def Clause.toLitSet (c : Clause) : Std.HashSet Lit :=
  Std.HashSet.ofArray c.toArray

def Clause.isEmpty (c : Clause) : Bool :=
  c.toArray.isEmpty

/-- Return the unique literal in the clause, if it exists. -/
def Clause.isUnit? (c : Clause) : Option Lit :=
  if h : c.toArray.size = 1 then some c.toArray[0] else none

/-- Resolution tree with assumptions for RAT. -/
inductive ResolutionTree
| given (clause : ClauseId)
| branch (lit : Lit) (fals tru : ResolutionTree)
| assumption (lit : Lit) -- TODO: cache these?
deriving Hashable, Inhabited, DecidableEq

def ResolutionTree.toMessageDataRaw (r : ResolutionTree) : Lean.MessageData :=
  match r with
  | .given clauseId =>
    m!"(given:{clauseId.toMessageDataRaw})"
  | .branch lit fals tru =>
    m!"(branch:{lit.toMessageDataRaw} {Format.line} {Lean.MessageData.nest 2 <| fals.toMessageDataRaw} {Format.line} {Lean.MessageData.nest 2 <| tru.toMessageDataRaw})"
  | .assumption lit =>
    m!"(assumption:{lit.toMessageDataRaw})"

/-- a boolean which is potentially unassigned. -/
inductive xbool
| tru
| fals
| x
deriving Inhabited, Repr, DecidableEq, Hashable

instance : Lean.ToMessageData xbool where
  toMessageData b := match b with
    | .tru => "✅"
    | .fals => "❌"
    | .x => "·"

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

def or : xbool → xbool → xbool
| .tru, _ => .tru
| _, .tru => .tru
| .fals, x => x
| x, .fals => x
| .fals, .fals => .fals
| .x, .x => .x

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
  /-- mapping from a level to the literals that were propagated. -/
  level2Propagations : Array (Array (Lit × ResolutionTree)) := #[#[]]
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
  /-- Message log. -/
  messages        : Array (Lean.MessageData × Lean.MessageSeverity) := #[]


/-- Evaluate a variable. -/
def State.evalVar (s : State) (v : Var) : xbool :=
  s.var2assign[v.toIndex]! |>.map Prod.fst |> xbool.ofOption

def State.evalLit (s : State) (l : Lit) : xbool :=
    let val := s.evalVar l.toVar
    if l.positive? then val else val.negate

def Lit.toMessageData (lit : Lit) (s : State) : Lean.MessageData :=
  m!"{lit.toMessageDataRaw}:{s.evalLit lit}"

def Var.toMessageData (var : Var) (s : State) : Lean.MessageData :=
  var.toPositiveLit.toMessageData s

def Clause.toMessageData (clause : Clause) (s : State) : Lean.MessageData :=
  Lean.toMessageData <| clause.toArray.map (Lit.toMessageData · s)

def State.decisionTrailMessageData (s : State) : Lean.MessageData :=
  m!"{s.decisionTrail.map (Lit.toMessageData · s)}"

def State.propQMessageData (s : State) : Lean.MessageData :=
  m!"{s.propQ.toArray.map (fun (lit, _proof) => m!"{lit.toMessageData s}")}"

def State.var2assignMessageData (s : State) : Lean.MessageData :=
  let msgs := s.var2assign.zipIdx.map fun (oval, i) =>
    m!"{Var.ofIndex i}:{xbool.ofOption <| oval.map Prod.fst}"
  m!"{msgs}"

instance : EmptyCollection State where
  emptyCollection := {}

instance : Inhabited State where
  default := ∅

/-- convert a clause ID a clause, using the state in the solver. -/
def ClauseId.toClause (s : State) (cid : ClauseId) : Clause :=
  s.clauses[cid.toIndex]!.fst

/-- convert a clause ID a clause, using the state in the solver. -/
def ClauseId.toProof (s : State) (cid : ClauseId) : ResolutionTree :=
  s.clauses[cid.toIndex]!.snd


def ClauseId.toMessageData (s : State) (cid : ClauseId) : Lean.MessageData :=
  m!"{cid.toMessageDataRaw}:{cid.toClause s |>.toMessageData s}"

def ClauseId.isLearnt (cid : ClauseId) (s : State) : Bool :=
  cid.toIndex >= s.learntClausesStartIx

partial def ResolutionTree.toLitSet (r : ResolutionTree) (s : State) : Std.HashSet Lit :=
  match r with
  | .given clauseId => clauseId.toClause s |>.toArray |> HashSet.ofArray
  | .branch lit fals tru =>
    let falsSet := fals.toLitSet s
    let truSet := tru.toLitSet s
    (falsSet.erase lit.negate).union (truSet.erase lit)
  | .assumption lit => Std.HashSet.emptyWithCapacity 1 |>.insert lit

partial def ResolutionTree.assumptions (r : ResolutionTree) (s : State) : Std.HashSet Lit :=
  match r with
  | .given _ => Std.HashSet.emptyWithCapacity 1
  | .branch lit fals tru =>
    let falsSet := fals.assumptions s
    let truSet := tru.assumptions s
    falsSet.union truSet
  | .assumption lit => Std.HashSet.emptyWithCapacity 1 |>.insert lit


/--
Insert the clauses that were used to prove 'r'
into the set of clauses 'HashSet clauseId'.
-/
def ResolutionTree.clausesUsed (r : ResolutionTree)
  (cs : HashSet ClauseId) :
    HashSet ClauseId :=
  match r with
  | .given clauseId =>
    cs.insert clauseId
  | .branch _ fals tru =>
    (fals.clausesUsed cs).union (tru.clausesUsed cs)
  | .assumption _ => cs


/-- Create a resolution tree that is fully expanded. -/
partial def ResolutionTree.toMessageData (r : ResolutionTree) (s : State) (alreadyExpanded : Std.HashSet ClauseId := ∅) : Lean.MessageData :=
  match r with
  | .given clauseId =>
    if clauseId.isLearnt s then
      if alreadyExpanded.contains clauseId then
        m!"(learnt:{clauseId.toMessageData s})"
      else
        let out := m!"(learnt:{clauseId.toMessageData s})"
        let alreadyExpanded := alreadyExpanded.insert clauseId
        let out := out ++ (Format.line ++ (clauseId.toProof s |>.toMessageData s alreadyExpanded))
        out
    else
      let alreadyExpanded := alreadyExpanded.insert clauseId
      if clauseId.isLearnt s
      then m!"(learnt:{clauseId.toMessageData s}{Format.line ++ (clauseId.toProof s |>.toMessageData s alreadyExpanded)})"
      else m!"(given:{clauseId.toMessageData s})"
  | .branch lit fals tru =>
    let set := r.toLitSet s |>.toArray |>.map (·.toMessageData s)
    m!"(branch:{lit.toMessageData s} {set} {Lean.indentD <| fals.toMessageData s alreadyExpanded}{Lean.indentD <| tru.toMessageData s alreadyExpanded})"
  | .assumption lit =>
    m!"(assump:{lit.toMessageData s})"

/-- Create a resolution tree that has no learnt nodes expanded. -/
def ResolutionTree.toMessageDataNoExpand (r : ResolutionTree) (s : State) : Lean.MessageData :=
  r.toMessageData s (HashSet.ofArray <| Array.range (s.clauses.size) |>.map ClauseId.ofIndex)

namespace State
def empty : State := ∅

def resetMessageLog (s : State) : State :=
  { s with messages := #[] }

/-- log a message. -/
def log (s : State) (msgData : Lean.MessageData) (severity : Lean.MessageSeverity) : State :=
  { s with messages := s.messages.push (msgData, severity) }

def logInfo (s : State) (msgData : Lean.MessageData) : State :=
  s.log msgData Lean.MessageSeverity.information

def logWarning (s : State) (msgData : Lean.MessageData) : State :=
  s.log msgData Lean.MessageSeverity.warning

def logError (s : State) (msgData : Lean.MessageData) : State :=
  s.log msgData Lean.MessageSeverity.error

/-- Add a literal for propgation. -/
def enqueuePropQ (s : State) (lit : Lit) (reason : ResolutionTree) : State :=
  let s := s.logInfo m!"ENQUEUE-PROP-Q @ {lit.toMessageData s}"
  let s := s.logInfo (reason.toMessageData s)
  { s with
    propQ := s.propQ.enqueue (lit, reason)
    level2Propagations := s.level2Propagations.modify (s.level2Propagations.size - 1) (fun l => l.push (lit, reason))
  }

/-- empty the propgation queue. -/
def emptyPropQ (s : State) : State :=
  { s with propQ := .empty }

/-- add the watched literal of clause 'cid' to the undo stack. -/
def addClauseWatchUndo (s : State) (cid : ClauseId) : State :=
  let s := s.logInfo m!"ADD-CLAUSE-WATCH-UNDO @ {cid.toMessageData s}"
  let c := cid.toClause s
  let s := { s with lit2clausesOnUndo := s.lit2clausesOnUndo.modify (c.get 0).toIndex (fun cs => cs.push cid) }
  s

/-- set the watched literal for a clause 'cid' to be index 'litIx'. -/
def setClauseWatchedLiteral (s : State) (cid : ClauseId) (litIx : Nat) : State :=
  let s := s.logInfo m!"SET-CLAUSE-WATCHED-LITERAL @ {cid.toMessageData s} : {litIx}"
  { s with clauses := s.clauses.modify cid.toIndex (fun (clause, proof) => (clause.swapLitTo0 litIx, proof)) }

/-- Add a clause to the watched clauses of this literal. -/
def watchClause (s : State) (cid : ClauseId) : State := Id.run do
  let s := s.logInfo m!"WATCH-CLAUSE @ {cid.toMessageData s}"
  let c := cid.toClause s
  let lit := c.get 0
  let s := { s with lit2clauses :=
      s.lit2clauses.modify lit.toIndex fun c => c.push cid
  }
  s

/--
Create a new clause, with optionally an explanation.
If no explanation is given, then a default 'assumption' explanation
is created.
-/
def newClauseWithExplanation (s : State)
    (clause : Clause)
    (explanation? : Option ResolutionTree)
    :
    ClauseId × State :=
  let clauseId := ClauseId.ofUInt32 <| UInt32.ofNat <| s.clauses.size
  let explanation := explanation?.getD (.given clauseId)
  let s := { s with clauses := s.clauses.push ⟨clause, explanation⟩ }
  let s  := s.logInfo m!"NEW-CLAUSE-WITH-EXPLAIN '{clauseId.toMessageData s}'"
  let s := s.logInfo <| explanation.toMessageData s
  if clause.size = 0 then
    let s := { s with unsatClause? := some clauseId }
    (clauseId, s)
  else if clause.size = 1 then
    let lit := clause.get 0
    let s := s.enqueuePropQ lit (.given clauseId)
    (clauseId, s)
  else
    -- | Setup 1-watch literal. Always watch at index '0'.
    let s := s.watchClause clauseId
    (clauseId, s)
/--
Create a new clause from the problem description.
-/
def newProblemClause (s : State) (clause : Clause) :
    ClauseId × State :=
  newClauseWithExplanation s clause none


def newVar (s : State) : State × Var :=
  let v := Var.ofIndex s.var2assign.size
  let s := { s with var2assign := s.var2assign.push none }
  let s := { s with lit2clauses := s.lit2clauses.push #[] }
  let s := { s with lit2clauses := s.lit2clauses.push #[] }
  let s := { s with lit2clausesOnUndo := s.lit2clausesOnUndo.push #[] }
  let s := { s with lit2clausesOnUndo := s.lit2clausesOnUndo.push #[] }
  (s, v)


def nVars (s : State) : UInt32 := UInt32.ofNat <| s.var2assign.size

/-- Check that the variable is well-formed. -/
def assertVarWellFormed (s : State) (v : Var) : State := Id.run do
  let mut s := s
  if v.toRawNatPos = 0 then
    s := s.logError m!"variable {v} is zero."

  if v.toIndex >= s.var2assign.size then
    s := s.logError m!"variable {v} is larger than defined variables ({s.var2assign.size})."
  return s

/-- Check that the literal is well-formed. -/
def assertLitWellFormed (s : State) (l : Lit) : State := Id.run do
  s.assertVarWellFormed l.toVar

/-- Check that the clause is well-formed. -/
def assertClauseWellFormed (s : State) (clause : Clause) : State := Id.run do
  let mut s := s
  for lit in clause.toArray do
    s := s.assertLitWellFormed lit
  return s

/--
Setup the solver state from the given problem.
-/
def newFromProblem (problem : CNF Nat) : State := Id.run do
  let mut s := State.empty
  /- get the largest variable ID. Since all variable IDs are nonzero,
  we know that this will be right. This is zero-indexed. -/
  let maxVarId : Nat := problem.foldl (init := 0) fun n clause =>
    clause.foldl (init := n) fun n (varId, _polarity) =>
      max n varId
  let maxVars := maxVarId + 1
  while s.nVars.toNat < maxVars do
    let (snew, _v) := s.newVar
    s := snew

  problem.foldl (init := s) fun s clause =>
      s.newProblemClause (Clause.ofCNF clause) |>.snd


def isUnsat (s : State) : Bool := s.unsatClause?.isSome

def dequePropQ (s : State) : Option ((Lit × ResolutionTree) × State) :=
  if let some ((lit, proof), propQ) := s.propQ.dequeue? then
    some ((lit, proof), { s with
      propQ := propQ
      level2Undo := s.level2Undo.modify (s.level2Undo.size - 1) (·.push lit)
    })
  else
    none

def assert [Lean.ToMessageData α] (s : State) (b : Bool) (msgFn : Unit → α) : State :=
  if b then s
  else s.logError (Lean.toMessageData <| msgFn ())

def unwrapOption [Inhabited α] (s : State) (a? : Option α) : α × State :=
  match a? with
  | none =>
    let s := s.logError "unable to unwrap option."
    (default, s)
  | some a => (a, s)

/--
Produce a partial assignment from the solver state.
-/
def partialAssignment (s : State) : Array (Nat × Bool) :=
    let var2obool : Array (Option Bool) := s.var2assign.map
      (fun oval => oval.map Prod.fst)
    var2obool.zipIdx
      |>.filterMap fun
        | (none, _) => none
        | (some b, ix) => some (ix, b)
/--
Produce a model from the state.
-/
def model? (s : State) : Option (Array Bool) :=
    let var2obool : Array (Option Bool) := s.var2assign.map
      (fun oval => oval.map Prod.fst)
    var2obool.traverse

def setLiteral (s : State) (lit : Lit) (proof : ResolutionTree) : State :=
  let s := s.logInfo m!"SET-LIT '{lit.toMessageData s}'"
  let s := { s with var2assign := s.var2assign.set! (lit.toVar.toIndex) (some (lit.positive?, proof)) }
  s

def unsetLiteral (s : State) (lit : Lit) : State :=
  let s := s.logInfo m!"UNSET-LIT '{lit.toMessageData s}'"
  let s := { s with var2assign := s.var2assign.set! (lit.toVar.toIndex) none }
  s

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


/-- undo the assignment of the given literal. -/
def State.undoAssignment (s : State) (lit : Lit) : State := Id.run do
  let mut s := s
  s := s.logInfo m!"UNDO-ASSIGN '{lit.toMessageData s}'"
  -- delete assignment.
  s := s.unsetLiteral lit
  -- note that the variable is unassigned.
  s := { s with unassignedVars := s.unassignedVars.insert lit.toVar }
  -- need to rewatch.
  let undos := s.lit2clausesOnUndo[lit.toIndex]!
  s := { s with
    lit2clauses := s.lit2clauses.modify lit.toIndex (· ++ undos)
    lit2clausesOnUndo := s.lit2clausesOnUndo.set! lit.toIndex #[]
  }
  s := { s with
    level2Propagations := s.level2Propagations.pop
  }
  s

/--
Whether we have decisions, or whether a toplevel conflict
has been found.
-/
def State.lastDecision? (s : State) : Option Lit := s.decisionTrail.back?

/-- undo a single decision, and return undone literal. -/
def State.undoOneDecision? (s : State) : Option Lit × State := Id.run do
  match s.decisionTrail.back? with
  | none => (none, s)
  | some lit =>
    let s := s.logInfo m!"UNDO-DECISION '{lit.toMessageData s}'"
    let s := { s with decisionTrail := s.decisionTrail.pop }
    let assigns := s.level2Undo.back!
    let s := { s with level2Undo := s.level2Undo.pop }
    let mut s := s
    s := s.undoAssignment lit
    -- undo assignments.
    for assign in assigns do
      s := s.undoAssignment assign
    (some lit, s)


/--
Makes a new conflict clause from a given proof of 'false' @ 'cid'.
- clears propagation queue, with only the conflict clause on the queue.
- undoes an assignment so we are at the base decision level.
- adds the conflict clause.
-/
def State.mkAndPropagateConflictClause (s : State) (unsatProof : ResolutionTree)
    : ClauseId × State := Id.run do
  let mut clauseProof : ResolutionTree := unsatProof
  let litsToBeResolved := clauseProof.assumptions s
  let mut clause : Array Lit := litsToBeResolved.toArray |>.map Lit.negate
  -- for lit in s.decisionTrail do
  --   if lit.negate ∈ litsToBeResolved then
  --     clause := clause.push lit.negate
  --     let litProof := .assumption lit
  --     clauseProof := .branch lit (fals:= clauseProof) (tru := litProof)

  -- for (lit, proof) in s.level2Propagations.back! do
  --   -- TODO: check if we need to do it this way? Do I need to add *all* literals?
  --   clauseProof := .branch lit (fals := clauseProof) (tru := proof)

  let s := { s with propQ := ∅ }
  -- TODO (george): how does kissat orchestrate undoing the assignment,
  -- and adding the new conflict clause to the watch queue?
  -- undo assignment.
  -- and when kissat decides to add clause to two watches.
  let (litLastDecided?, s) := s.undoOneDecision?
  -- | now make the new clause.
  -- The annoying thing is, the decision that is undone will be at the *end* of the clause,
  -- but we want this to be the *beginning* of the clause so that this is the watched literal.
  -- TODO (george): how does kissat do this?
  -- Here, we swap the last element (which should be unassigned)
  -- with the first element (which will become the watched element).
  clause := clause.swapIfInBounds 0 (clause.size - 1)
  let (conflictId, s) := s.newClauseWithExplanation
    (Clause.ofArray clause)
    (some clauseProof)
  let s := s.logInfo m!"CONFLICT-CLAUSE {conflictId.toMessageData s}"
  let s := s.logInfo m!"{clauseProof.toMessageData s}"
  if let some lit := litLastDecided? then
    let s := s.enqueuePropQ lit.negate (ResolutionTree.given conflictId)
    (conflictId, s)
  else
    let s := { s with unsatClause? := .some conflictId }
    (conflictId, s)


/-- Get all watched clauses for a literal, and clear the watched clauses list. -/
def State.getAndClearWatchedClausesAtLit (s : State) (lit : Lit) :
    Array ClauseId × State :=
  let clauses := s.lit2clauses[lit.toIndex]!
  let s := { s with lit2clauses := s.lit2clauses.set! lit.toIndex #[] }
  (clauses, s)



/--
Propagate a literal assignment of lit 'Lit' in clause 'clauseId'.
Returns a conflict clause if a conflict clause was created.


The state will contain the conflicting assignment in case a
conflict clause is returned.
-/
def State.propagateLitInClause (s : State)
  (litTrue : Lit) (reason: ResolutionTree)
  (cid : ClauseId) :
    Option ClauseId × State := Id.run do
  let c := cid.toClause s
  if c.get 0 ≠ litTrue.negate then
    let s := s.logInfo "ERROR: Clause {cid.toMessageData s} does not start with {litTrue.negate.toMessageData s}"
    return ⟨none, s⟩
  let s := s.logInfo m! "propagating assignment lit that became false {litTrue.negate.toMessageData s} @ {cid.toMessageData s}"
  match s.findNonFalseLit cid 0 with
  | .allFalse =>
    let s := s.logInfo m!"found clause that is all false: {cid.toMessageData s}"
    /-
    We've found a conflict clause. Flush the queue,
    add the clause.
    -/
    let clause := cid.toClause s
    let mut unsatProof := cid.toProof s
    for lit in clause.toArray do
      let litProof := s.var2assign[lit.toVar.toIndex]!.get!.snd
      -- | clause has all the literals, and all the literals are negated.
      unsatProof := .branch lit  (fals := litProof) (tru := unsatProof)
    let (conflictId, s):= s.mkAndPropagateConflictClause unsatProof
    let s := s.addClauseWatchUndo cid
    return (some conflictId, s)
  | .tru =>
    let s := s.logInfo m!"found 'tru' in clause. Skipping..."
    let s := s.addClauseWatchUndo cid
    (none, s) -- nothing to propagate, clause has 'true' in it.
  | .unassigned lit litIx =>
      let s := s.logInfo m!"found unassigned literal '{lit.toMessageData s}' in clause {cid.toMessageData s}."
      -- hurray, we have a watched literal.
      -- check if it's the *only* unassigned literal.
      -- If it is, propagate.
      -- If not, swap it with lit[0], and make it watched.
      match s.findNonFalseLit cid (litIx + 1) with
      | .tru =>
        let s := s.logInfo m!"found true literal in clause {cid.toMessageData s}, skipping. "
        let s := s.addClauseWatchUndo cid
        (none, s) -- nothing to do, we have a true literal.
      | .unassigned litUnassigned litUnassignedIx =>
          -- we have another unassigned literal, so we
          -- cannot propagate.
          -- Swap clause[0] with clause[litIx],
          -- watch clause[0], and continue on our way.
          let s := s.logInfo m!"found another unassigned literal {litUnassigned.toMessageData s} in clause {cid.toMessageData s}. "
          let s := s.addClauseWatchUndo cid
          let s := s.setClauseWatchedLiteral cid litUnassignedIx
          let s := s.watchClause cid
          (none, s)
      | .allFalse =>
          -- we have no other unassigned literals,
          -- so we can propagate!
          let s := s.logInfo m!"found all other literals to be false, so propagating literal '{lit.toMessageData s}'."
          let mut unitProof := cid.toProof s
          let clause := cid.toClause s
          for cLitFals in clause.toArray do
            if cLitFals = lit then continue
            let litProof := s.var2assign[cLitFals.toVar.toIndex]!.get!.snd
            -- | clause has all the literals, and all the literals are negated.
            unitProof := .branch cLitFals  (tru := unitProof) (fals := litProof)
          let s := s.enqueuePropQ lit unitProof
          let s := s.addClauseWatchUndo cid
          (none, s)

partial def State.propagate (s : State) : Option ClauseId × State := propagateAux s where
  propagateAux (s : State) : Option ClauseId × State := Id.run do
    let s := s.logInfo m!"== PROPAGATION QUEUE: '{s.propQMessageData}' =="
    if let some ((lit, litProof), s) := s.dequePropQ then
      match s.evalLit lit with
      | .tru =>
          let s := s.logInfo m!"{lit.toMessageData s} already assigned. Continuing..."
          s.propagate
      | .fals =>
          let s := s.logInfo m!"{lit.toMessageData s} has conflicting assignment. Creating conflict clause..."
          -- we have a conflicting assignment.
          let vProof := s.var2assign[lit.toVar.toIndex]!.get!.snd
          let conflictReason : ResolutionTree := .branch lit vProof litProof
          let (conflictId, s) := s.mkAndPropagateConflictClause conflictReason
          (some conflictId, s)
      | .x =>
        let s := s.logInfo m!"{lit.toMessageData s} has no assignments. Propagating..."
        -- we don't have an assignment, continue.
        let s := s.setLiteral lit litProof
        let s := s.logInfo m!"-- Current variable assignments: {s.var2assignMessageData} --"
        -- since 'lit' has been assigned, we need to propagate '~lit'.
        let (watchedClauses, s) := s.getAndClearWatchedClausesAtLit lit.negate
        let mut s := s
        s := s.logInfo m!"#clauses watched at negated {lit.negate.toMessageData s}: '{watchedClauses.size}'"
        for clauseId in watchedClauses do
          s := s.logInfo m!"  👀 {clauseId.toMessageData s}"

        for (clauseId, ix) in watchedClauses.zipIdx do
          let res := s.propagateLitInClause lit litProof clauseId
          s := res.snd
          let conflictId? := res.fst
          if let some conflictId := conflictId? then
            -- we should make sure that we don't wipe the watches for the later clauses,
            -- so we add these clauses back into the watch list.
            -- alternatively, do we just add these into the undos? I'm not sure.
            -- TODO(george): this is super error prone. What is a nicer way of doing this?
            s := watchedClauses[ix+1:].foldl (init := s) fun s laterClauseId =>
              s.addClauseWatchUndo laterClauseId
            return (some conflictId, s)
        s.propagate
    else
      -- queue is empty, stop recursion.
      (none, s)

inductive SatSolveResult
| sat
| unsat
| nofuel
deriving DecidableEq, Inhabited

def State.getUnassignedVar (s : State) : Option Var :=
  (s.var2assign.findIdx? fun val => val.isNone).map Var.ofIndex

/-- Solve. -/
partial def State.solve (s : State) : SatSolveResult × State :=
  let s := { s with learntClausesStartIx := s.clauses.size }
  solveAux s
  where
  solveAux (s : State) : SatSolveResult × State := Id.run do
    let s := s.logInfo m!"== Starting solve @ level {s.level2Undo.size} {s.decisionTrailMessageData}=="
    let (conflictId?, s) := s.propagate
    if let some conflictId := conflictId? then
      let conflictClause := s.clauses[conflictId.toIndex]!.fst
      if conflictClause.isEmpty then
        let s := { s with unsatClause? := some conflictId }
        return (.unsat, s)
      else
        solveAux s
    else
      if let some v := s.getUnassignedVar
      then
        let vlit := v.toPositiveLit
        -- add the decision to the trail.
        let s := { s with decisionTrail := s.decisionTrail.push vlit }
        let s := { s with level2Undo := s.level2Undo.push #[] }
        let s := { s with level2Propagations := s.level2Propagations.push #[] }
        let s := s.logInfo m!"DECISION {s.level2Undo.size}, {vlit.toMessageData s} | trail: {s.decisionTrailMessageData}."
        let vproof := .assumption vlit
        -- | TODO: decide who assigns: Do we assume that the assignment is done before propagation?
        let s := s.enqueuePropQ vlit vproof
        solveAux s
      else
        (.sat, s)

namespace ResolutionTree

variable (r : ResolutionTree) (s : State)



/--
Appends the conflicts that were used to produce
the resolution tree 'r' to the array 'conflicts'.
The order of conflicts is from earliest to latest,
in terms of their creation time.
-/
def appendConflictIdsInOrder
  (alreadyAddedConflicts : HashSet ClauseId)
  (conflicts : Array ClauseId)
  (r : ResolutionTree) :
  Array ClauseId :=
  match r with
  | .given clauseId =>
    if clauseId.isLearnt s
    then -- is a learnt clause
      conflicts.push clauseId
    else conflicts
  | .branch _lit fals tru =>
    let conflicts :=
      appendConflictIdsInOrder
        alreadyAddedConflicts conflicts fals
    let conflicts :=
      appendConflictIdsInOrder
        alreadyAddedConflicts conflicts tru
    conflicts
  | .assumption _lit => conflicts



end ResolutionTree

def ResolutionTree.isValidForConflictClause (s : State) (r : ResolutionTree) (clauseLits : Std.HashSet Lit) : Bool × State :=
  match r with
  | .assumption lit =>
    if lit.negate ∈ clauseLits then
      (true, s)
    else
      (false, s.logError m!"clause {clauseLits.toArray.map (Lit.toMessageData · s)} does not contain literal {lit.negate.toMessageData s}")
  | .given _ =>
      (true, s)
  | .branch lit fals tru => Id.run do
    let falsLits := fals.toLitSet s
    let truLits := tru.toLitSet s
    let mut good := true
    let mut s := s
    if !falsLits.contains lit.negate then
      s := s.logError m!"branch fals does not contain {lit.negate.toMessageData s} in '{r.toMessageData s}', branch '{fals.toMessageData s}'"
      good := false
    if !truLits.contains lit then
      s := s.logError m!"branch tru does not contain {lit.toMessageData s} in '{r.toMessageData s}', branch '{tru.toMessageData s}'"
      good := false
    let res := fals.isValidForConflictClause s clauseLits
    let goodLeft := res.fst
    s := res.snd
    let res := tru.isValidForConflictClause s clauseLits
    let goodRight := res.fst
    s := res.snd
    (good && goodLeft && goodRight, s)

namespace State

/--
Convert a resolution tree into an LRAT proof.
-/
def toLrat (s : State) : Array LRAT.IntAction × State := Id.run do
  let mut actions := #[]
  let mut s := s
  let startIx := s.learntClausesStartIx
  let endIx := s.clauses.size
  s := s.logInfo "=== LRAT Proof ==="
  for cid in [startIx:endIx] do
    let (clause, proof) := s.clauses[cid]!
    s := s.logInfo <| m!"{cid + 1}) {clause.toMessageData s} {proof.toMessageDataNoExpand s}"
    let res := proof.isValidForConflictClause s (clause.toLitSet)
    let good := res.fst
    s := res.snd
    if good then
      s := s.logInfo m!"GOOD PROOF ({cid + 1})"
    else
      s := s.logInfo m!"BAD PROOF ({cid + 1})"
    let clausesUsedToProveConflict :=
      proof.clausesUsed ∅
      |>.toArray
      |>.map ClauseId.toLratPos

    if clause.isEmpty then
      actions := actions.push
        (LRAT.Action.addEmpty
          (id := cid + 1) -- one-indexed.
          (rupHints := clausesUsedToProveConflict))
    else
      actions := actions.push
        (LRAT.Action.addRup
          (id := cid + 1) -- one-indexed.
          (c := clause.toIntArray)
          (rupHints := clausesUsedToProveConflict))
  (actions, s)

end State

def State.evalClause (c : Clause) (s : State) : xbool :=
  c.toArray.foldl (init := xbool.fals) (fun acc lit => acc.or (s.evalLit lit))

/-! Helpers for bvDecide interaction. -/
open Lean Meta in
def runOneShot (cnf : CNF Nat) :
    ((Option (Except (Array (Bool × Nat)) (Array LRAT.IntAction))) × State) :=
  let solver := State.newFromProblem cnf
  let (result, solver) := solver.solve
  match result with
  | .unsat =>
    let conflictId := solver.unsatClause?.get!
    let resolutionProof :=
      conflictId.toProof solver
    let solver := solver.logInfo m!"======= UNSAT Resolution treee ========"
    let solver := solver.logInfo m!"UNSAT clause: {conflictId.toMessageData solver}"
    let solver := solver.logInfo m!"{resolutionProof.toMessageDataNoExpand solver}"
    let (lrat, solver) := solver.toLrat
    (some (Except.ok <| lrat), solver)
  | .sat => Id.run do
    let partialAssign := solver.partialAssignment
    let mut solver := solver
    solver := solver.logInfo m!"===== SAT model {solver.var2assignMessageData} ======"
    for cid in [0:solver.learntClausesStartIx] do
      let cid := ClauseId.ofIndex cid
      let val := solver.evalClause (cid.toClause solver)
      let errStr := if  val = xbool.fals then m!"[☠️]" else m!""
      solver := solver.logInfo m!"⟦{cid.toMessageData solver}⟧ {val} {errStr}"
    (some (Except.error <| partialAssign.map Prod.swap), solver)
  | .nofuel =>
    let solver := solver.logError "Solver ran out of fuel."
    (none, solver)

end Verisat
