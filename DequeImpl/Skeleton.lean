/-!
# Doubly-Linked-List Deque — TDD Skeleton

This file is your playground.  Every definition body and proof tactic is
replaced with `sorry`; your job is to fill them in one by one, guided by
the failing goals in the theorem stubs.

## Design

Because Lean 4 is purely functional we model heap pointers with **array
indices**.  A single `Array (Node α)` acts as the node pool; each node
stores the index of its predecessor and successor rather than a raw pointer.

```
   head                            tail
    │                               │
    ▼                               ▼
┌───────────┐     ┌───────────┐     ┌───────────┐
│ prev=none │────▶│ prev=0    │────▶│ prev=1    │
│ next=some1│     │ next=some2│     │ next=none │
│  val= a   │     │  val= b   │     │  val= c   │
└───────────┘     └───────────┘     └───────────┘
```

`NodeId` is a plain `Nat`; invalid / freed slots are never reused in this
skeleton (append-only pool), so every live id is always in-bounds.
-/

universe u

/-! ## Core types -/

/-- An index into the node pool (`LinkedDeque.nodes`). -/
abbrev NodeId := Nat

/-- One node in the doubly-linked chain. -/
structure Node (α : Type u) where
  /-- The stored value. -/
  val  : α
  /-- Index of the previous node, or `none` at the left end. -/
  prev : Option NodeId
  /-- Index of the next node, or `none` at the right end. -/
  next : Option NodeId
  deriving Repr

/-- A doubly-linked-list deque.
    Nodes are stored in `nodes`; `head` and `tail` are indices into that array. -/
structure LinkedDeque (α : Type u) where
  /-- Backing array — append-only node pool. -/
  nodes : Array (Node α)
  /-- Index of the leftmost node, or `none` when empty. -/
  head  : Option NodeId
  /-- Index of the rightmost node, or `none` when empty. -/
  tail  : Option NodeId
  deriving Repr

namespace LinkedDeque

variable {α : Type u}

/-! ## Construction -/

/-- The empty deque. -/
def empty : LinkedDeque α := sorry

/-- A deque containing exactly one element. -/
def singleton (x : α) : LinkedDeque α := sorry

/-! ## Basic predicates -/

/-- `true` iff the deque contains no elements. -/
def isEmpty (d : LinkedDeque α) : Bool := sorry

/-- Number of live elements (nodes reachable from `head`). -/
def size (d : LinkedDeque α) : Nat := sorry

/-! ## Insertion -/

/-- Push `x` onto the left end, creating a new head node. -/
def pushLeft (x : α) (d : LinkedDeque α) : LinkedDeque α := sorry

/-- Push `x` onto the right end, creating a new tail node. -/
def pushRight (x : α) (d : LinkedDeque α) : LinkedDeque α := sorry

/-! ## Inspection -/

/-- Traverse from `head` to `tail` and collect all values in order. -/
def toList (d : LinkedDeque α) : List α := sorry

/-- The value of the leftmost node, if any. -/
def peekLeft (d : LinkedDeque α) : Option α := sorry

/-- The value of the rightmost node, if any. -/
def peekRight (d : LinkedDeque α) : Option α := sorry

/-! ## Removal -/

/-- Remove the leftmost element, advancing `head` to the next node.
    Returns the value together with the updated deque, or `none` when empty. -/
def popLeft (d : LinkedDeque α) : Option (α × LinkedDeque α) := sorry

/-- Remove the rightmost element, retreating `tail` to the previous node.
    Returns the value together with the updated deque, or `none` when empty. -/
def popRight (d : LinkedDeque α) : Option (α × LinkedDeque α) := sorry

/-! ## Theorem stubs — fill in the `sorry` tactics -/

section Proofs

/-! ### `empty` -/

@[simp] theorem empty_head  : (empty : LinkedDeque α).head = none := by sorry
@[simp] theorem empty_tail  : (empty : LinkedDeque α).tail = none := by sorry
@[simp] theorem empty_nodes : (empty : LinkedDeque α).nodes = #[]  := by sorry

@[simp] theorem empty_isEmpty : (empty : LinkedDeque α).isEmpty = true  := by sorry
@[simp] theorem empty_size    : (empty : LinkedDeque α).size    = 0     := by sorry
@[simp] theorem empty_toList  : (empty : LinkedDeque α).toList  = []    := by sorry

/-! ### `singleton` -/

@[simp] theorem singleton_size (x : α) : (singleton x).size = 1           := by sorry
@[simp] theorem singleton_toList (x : α) : (singleton x).toList = [x]     := by sorry
@[simp] theorem singleton_not_isEmpty (x : α) : (singleton x).isEmpty = false := by sorry

/-! ### `size` -/

@[simp] theorem pushLeft_size (x : α) (d : LinkedDeque α) :
    (d.pushLeft x).size = d.size + 1 := by sorry

@[simp] theorem pushRight_size (x : α) (d : LinkedDeque α) :
    (d.pushRight x).size = d.size + 1 := by sorry

/-! ### `isEmpty` -/

@[simp] theorem pushLeft_not_isEmpty (x : α) (d : LinkedDeque α) :
    (d.pushLeft x).isEmpty = false := by sorry

@[simp] theorem pushRight_not_isEmpty (x : α) (d : LinkedDeque α) :
    (d.pushRight x).isEmpty = false := by sorry

theorem isEmpty_iff_size_zero (d : LinkedDeque α) :
    d.isEmpty = true ↔ d.size = 0 := by sorry

theorem isEmpty_iff_toList_nil (d : LinkedDeque α) :
    d.isEmpty = true ↔ d.toList = [] := by sorry

/-! ### `toList` -/

@[simp] theorem pushLeft_toList (x : α) (d : LinkedDeque α) :
    (d.pushLeft x).toList = x :: d.toList := by sorry

@[simp] theorem pushRight_toList (x : α) (d : LinkedDeque α) :
    (d.pushRight x).toList = d.toList ++ [x] := by sorry

/-! ### `popLeft` -/

@[simp] theorem popLeft_empty : (empty : LinkedDeque α).popLeft = none := by sorry

/-- Push then pop from the same side is the identity. -/
@[simp] theorem popLeft_pushLeft (x : α) (d : LinkedDeque α) :
    (d.pushLeft x).popLeft = some (x, d) := by sorry

/-- Popping recovers the head element and the tail of the logical list. -/
theorem popLeft_toList {d : LinkedDeque α} {x : α} {d' : LinkedDeque α}
    (h : d.popLeft = some (x, d')) :
    x :: d'.toList = d.toList := by sorry

/-! ### `popRight` -/

@[simp] theorem popRight_empty : (empty : LinkedDeque α).popRight = none := by sorry

/-- Push then pop from the same side is the identity. -/
@[simp] theorem popRight_pushRight (x : α) (d : LinkedDeque α) :
    (d.pushRight x).popRight = some (x, d) := by sorry

/-- Popping recovers the tail element and the init of the logical list. -/
theorem popRight_toList {d : LinkedDeque α} {x : α} {d' : LinkedDeque α}
    (h : d.popRight = some (x, d')) :
    d'.toList ++ [x] = d.toList := by sorry

/-! ### `peekLeft` / `peekRight` -/

@[simp] theorem peekLeft_empty  : (empty : LinkedDeque α).peekLeft  = none := by sorry
@[simp] theorem peekRight_empty : (empty : LinkedDeque α).peekRight = none := by sorry

@[simp] theorem peekLeft_pushLeft (x : α) (d : LinkedDeque α) :
    (d.pushLeft x).peekLeft = some x := by sorry

@[simp] theorem peekRight_pushRight (x : α) (d : LinkedDeque α) :
    (d.pushRight x).peekRight = some x := by sorry

end Proofs

end LinkedDeque
