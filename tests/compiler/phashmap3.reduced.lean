-- import Std.Data.PersistentHashMap'
-- import Lean.Data.Format
-- open Lean Std Std.PersistentHashMap'
import Std

namespace Std
universe u v w w'

namespace PersistentHashMap'

inductive Entry (α : Type u) (β : Type v) (σ : Type w) where
  | entry (key : α) : Entry α β σ
  | ref   (node : σ) : Entry α β σ
  | null  : Entry α β σ

instance {α β σ} : Inhabited (Entry α β σ) := ⟨Entry.null⟩

instance [ToString α] [ToString β] : ToString (Entry α β σ) where
  toString e := match e with
                | .entry k => "entry"
                | .null => ".null"
                | .ref _ => ".ref"

inductive Node (α : Type u) (β : Type v) : Type (max u v) where
  | entries   (es : Array (Entry α β (Node α β))) : Node α β
  | collision (ks : Array α): Node α β

instance {α β} : Inhabited (Node α β) := ⟨Node.entries #[]⟩

abbrev shift         : USize  := 5
abbrev branching     : USize  := USize.ofNat (2 ^ shift.toNat)
abbrev maxDepth      : USize  := 7
abbrev maxCollisions : Nat    := 4

def mkEmptyEntriesArray {α β} : Array (Entry α β (Node α β)) :=
  (Array.mkArray PersistentHashMap'.branching.toNat PersistentHashMap'.Entry.null)

end PersistentHashMap'

structure PersistentHashMap' (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  root    : PersistentHashMap'.Node α β := PersistentHashMap'.Node.entries PersistentHashMap'.mkEmptyEntriesArray

abbrev PHashMap' (α : Type u) (β : Type v) [BEq α] [Hashable α] := PersistentHashMap' α β

namespace PersistentHashMap'

def empty [BEq α] [Hashable α] : PersistentHashMap' α β := {}

instance [BEq α] [Hashable α] : Inhabited (PersistentHashMap' α β) := ⟨{}⟩

def mkEmptyEntries {α β} : Node α β :=
  Node.entries mkEmptyEntriesArray

abbrev div2Shift (i : USize) (shift : USize) : USize := i.shiftRight shift
abbrev mod2Shift (i : USize) (shift : USize) : USize := USize.land i ((USize.shiftLeft 1 shift) - 1)

partial def insertAtCollisionNodeAux [BEq α] : Node α β → Nat → α → β → Node α β
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

def insertAtCollisionNode [BEq α] : Node α β → α → β → IO (Node α β) :=
  fun n k v => do 
     IO.println s!"insertAtCollisionNode"
     pure$ insertAtCollisionNodeAux n 0 k v

def getCollisionNodeSize : Node α β → Nat
  | Node.collision keys   => keys.size
  | Node.entries   _  => 0

def mkCollisionNode (k₁ : α) (k₂ : α) : IO (Node α β) := do
  IO.println s!"mkCollisionNode"
  let ks : Array α := Array.mkEmpty maxCollisions
  let ks := (ks.push k₁).push k₂
  pure $ Node.collision ks 

partial def insertAux [Inhabited α] [Inhabited β] [ToString α] [ToString β] [BEq α] [Hashable α] (n: Node α β) (h: USize) (depth: USize) (k: α) (v: β):IO (Node α β) := do
  match n with
  | Node.collision keys => pure n
  | Node.entries entries => 
    let j     := (mod2Shift h shift).toNat
    let es ← entries.modifyM j fun entry => do
      match entry with
      | Entry.null        => IO.println "null"; pure $ .entry k
      | Entry.ref node    => IO.println "ref"; pure $ Entry.ref $ (← insertAux node (div2Shift h shift) (depth+1) k v)
      | Entry.entry k' =>
        if k == k' then IO.println "entry.entry"; pure $ Entry.entry k 
        else IO.println "entry.ref"; pure $ Entry.ref $ ← mkCollisionNode k' k
    pure $ Node.entries es

def insert [Inhabited α] [Inhabited β] [ToString α] [ToString β] {_ : BEq α} {_ : Hashable α} (m: PersistentHashMap' α β) (k: α) (v: β): IO (PersistentHashMap' α β) := do
  match m with
  | { root := n } => pure { root := (← insertAux n (hash k |>.toUSize) 1 k v) }
end PersistentHashMap'
end Std

open Std PersistentHashMap'

abbrev Map' := PersistentHashMap' Nat Nat

def main : IO Unit := do
  let m : Map' := PersistentHashMap'.empty;
  let m ←  m.insert 1 1;
  let m ← m.insert 34359738369 3;
  return ()
