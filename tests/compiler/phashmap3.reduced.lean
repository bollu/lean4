-- import Std.Data.PersistentHashMap'
-- import Lean.Data.Format
-- open Lean Std Std.PersistentHashMap'
import Std

namespace Std
universe u v w w'

namespace PersistentHashMap'

inductive Node (α : Type u) : Type (max u v) where
  | entries   (es : Array ((Node α))) : Node α
  | collision (ks : Array α): Node α
  | entry (key : α) : Node α
  | ref   (node : Node α) : Node α
  | null  : Node α


instance [ToString α] : ToString (Node α) where
  toString e := match e with
                | .entry k => "entry"
                | .null => ".null"
                | .ref _ => ".ref"
                | _ => ".unk"

instance {α} : Inhabited (Node α) := ⟨Node.entries #[]⟩

abbrev shift         : USize  := 5
abbrev branching     : USize  := USize.ofNat (2 ^ shift.toNat)
abbrev maxDepth      : USize  := 7
abbrev maxCollisions : Nat    := 4

def mkEmptyEntriesArray {α} : Array (Node α) :=
  (Array.mkArray PersistentHashMap'.branching.toNat PersistentHashMap'.Node.null)

end PersistentHashMap'

structure PersistentHashMap' (α : Type u) [BEq α] [Hashable α] where
  root    : PersistentHashMap'.Node α := PersistentHashMap'.Node.entries PersistentHashMap'.mkEmptyEntriesArray

abbrev PHashMap' (α : Type u) (β : Type v) [BEq α] [Hashable α] := PersistentHashMap' α

namespace PersistentHashMap'

def empty [BEq α] [Hashable α] : PersistentHashMap' α := {}

instance [BEq α] [Hashable α] : Inhabited (PersistentHashMap' α) := ⟨{}⟩

def mkEmptyEntries {α} : Node α :=
  Node.entries mkEmptyEntriesArray

abbrev div2Shift (i : USize) (shift : USize) : USize := i.shiftRight shift
abbrev mod2Shift (i : USize) (shift : USize) : USize := USize.land i ((USize.shiftLeft 1 shift) - 1)

partial def insertAtCollisionNodeAux [BEq α] : Node α → Nat → α → β → Node α
  | n@(Node.collision keys), i, k, v =>
    if h : i < keys.size then
      let idx : Fin keys.size := ⟨i, h⟩;
      let k' := keys.get idx;
      if k == k' then
         (Node.collision (keys.set idx k))
      else insertAtCollisionNodeAux n (i+1) k v
    else
      (Node.collision (keys.push k))
  | n@(Node.entries _), _, _, _ => n
  | n, _, _, _ => n

def insertAtCollisionNode [BEq α] : Node α → α → β → IO (Node α) :=
  fun n k v => do 
     IO.println s!"insertAtCollisionNode"
     pure$ insertAtCollisionNodeAux n 0 k v

def getCollisionNodeSize : Node α → Nat
  | Node.collision keys   => keys.size
  | Node.entries   _  => 0
  | _ => 0

def mkCollisionNode [ToString α] (k₁ : α) (k₂ : α) : IO (Node α) := do
  let ks : Array α := Array.mkEmpty maxCollisions
  let ks := (ks.push k₁).push k₂
  IO.println s!"mkCollisionNode {ks.toList}"
  pure $ Node.collision ks 

partial def insertAux [Inhabited α] [ToString α] [BEq α] [Hashable α] (n: Node α) (h: USize) (depth: USize) (k: α) :IO (Node α) := do
  IO.println s!"insertAux {n} {h} {depth} {k}"
  match n with
  | Node.collision keys => pure n
  | Node.entries entries => 
    let j     := (mod2Shift h shift).toNat
    let es ← entries.modifyM j fun entry => do
      match entry with
      | Node.null        => IO.println "null"; pure $ .entry k
      | Node.ref node    => IO.println "ref"; pure $ Node.ref $ (← insertAux node (div2Shift h shift) (depth+1) k)
      | Node.entry k' =>
        if k == k' then IO.println "entry.entry"; pure $ Node.entry k 
        else IO.println "entry.ref"; pure $ Node.ref $ ← mkCollisionNode k' k
      | _  => IO.println "other"; pure $ .entry k
    pure $ Node.entries es
  | _ => return n

def insert [Inhabited α] [Inhabited β] [ToString α] [ToString β] {_ : BEq α} {_ : Hashable α} (m: PersistentHashMap' α) (k: α) (v: β): IO (PersistentHashMap' α) := do
  match m with
  | { root := n } => pure { root := (← insertAux n (hash k |>.toUSize) 1 k) }
end PersistentHashMap'
end Std

open Std PersistentHashMap'

abbrev Map' := PersistentHashMap' Nat

def main : IO Unit := do
  let m : Map' := PersistentHashMap'.empty;
  let m ←  m.insert 1 1;
  let m ← m.insert 34359738369 3;
  return ()
