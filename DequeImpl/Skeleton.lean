/-!
# Deque — TDD Skeleton

Fill in each `sorry` to make the proofs pass. The completed reference
implementation lives in `DequeImpl.Basic`.

The deque is backed by two lists:
- `left`:  elements at the left end, in order (head = leftmost element)
- `right`: elements at the right end, stored **reversed** (head = rightmost element)

Logical sequence: `left ++ right.reverse`
-/

universe u

/-- A double-ended queue backed by two lists. -/
structure Deque' (α : Type u) where
  left  : List α
  right : List α
  deriving Repr

namespace Deque'

variable {α : Type u}

/-! ## Construction — fill in the bodies -/

/-- The empty deque. -/
def empty : Deque' α := sorry

/-- A deque containing exactly one element. -/
def singleton (x : α) : Deque' α := sorry

/-! ## Basic predicates — fill in the bodies -/

/-- `true` iff the deque has no elements. -/
def isEmpty (d : Deque' α) : Bool := sorry

/-- Number of elements in the deque. -/
def size (d : Deque' α) : Nat := sorry

/-! ## Insertion — fill in the bodies -/

/-- Push `x` onto the left end. -/
def pushLeft (x : α) (d : Deque' α) : Deque' α := sorry

/-- Push `x` onto the right end. -/
def pushRight (x : α) (d : Deque' α) : Deque' α := sorry

/-! ## Inspection — fill in the bodies -/

/-- Flatten to a list: `left ++ right.reverse`. -/
def toList (d : Deque' α) : List α := sorry

/-- The leftmost element, if any. -/
def peekLeft (d : Deque' α) : Option α := sorry

/-- The rightmost element, if any. -/
def peekRight (d : Deque' α) : Option α := sorry

/-! ## Removal — fill in the bodies -/

/-- Remove the leftmost element (rebalance by reversing `right` when `left` is empty). -/
def popLeft (d : Deque' α) : Option (α × Deque' α) := sorry

/-- Remove the rightmost element (rebalance by reversing `left` when `right` is empty). -/
def popRight (d : Deque' α) : Option (α × Deque' α) := sorry

/-! ## Proofs — fill in the `sorry` tactics -/

section Proofs

/-! ### `empty` -/

@[simp] theorem empty_left  : (empty : Deque' α).left  = [] := by sorry
@[simp] theorem empty_right : (empty : Deque' α).right = [] := by sorry

@[simp] theorem empty_isEmpty : (empty : Deque' α).isEmpty = true := by sorry
@[simp] theorem empty_size    : (empty : Deque' α).size    = 0    := by sorry
@[simp] theorem empty_toList  : (empty : Deque' α).toList  = []   := by sorry

/-! ### `singleton` -/

@[simp] theorem singleton_size (x : α) : (singleton x).size = 1 := by sorry
@[simp] theorem singleton_toList (x : α) : (singleton x).toList = [x] := by sorry
@[simp] theorem singleton_not_isEmpty (x : α) : (singleton x).isEmpty = false := by sorry

/-! ### `size` -/

@[simp] theorem pushLeft_size (x : α) (d : Deque' α) :
    (d.pushLeft x).size = d.size + 1 := by sorry

@[simp] theorem pushRight_size (x : α) (d : Deque' α) :
    (d.pushRight x).size = d.size + 1 := by sorry

/-! ### `isEmpty` -/

@[simp] theorem pushLeft_not_isEmpty (x : α) (d : Deque' α) :
    (d.pushLeft x).isEmpty = false := by sorry

@[simp] theorem pushRight_not_isEmpty (x : α) (d : Deque' α) :
    (d.pushRight x).isEmpty = false := by sorry

theorem isEmpty_iff_size_zero (d : Deque' α) :
    d.isEmpty = true ↔ d.size = 0 := by sorry

theorem isEmpty_iff_toList_nil (d : Deque' α) :
    d.isEmpty = true ↔ d.toList = [] := by sorry

/-! ### `toList` -/

@[simp] theorem pushLeft_toList (x : α) (d : Deque' α) :
    (d.pushLeft x).toList = x :: d.toList := by sorry

@[simp] theorem pushRight_toList (x : α) (d : Deque' α) :
    (d.pushRight x).toList = d.toList ++ [x] := by sorry

/-! ### `popLeft` -/

@[simp] theorem popLeft_pushLeft (x : α) (d : Deque' α) :
    (d.pushLeft x).popLeft = some (x, d) := by sorry

@[simp] theorem popLeft_empty : (empty : Deque' α).popLeft = none := by sorry

theorem popLeft_toList {d : Deque' α} {x : α} {d' : Deque' α}
    (h : d.popLeft = some (x, d')) :
    x :: d'.toList = d.toList := by sorry

/-! ### `popRight` -/

@[simp] theorem popRight_pushRight (x : α) (d : Deque' α) :
    (d.pushRight x).popRight = some (x, d) := by sorry

@[simp] theorem popRight_empty : (empty : Deque' α).popRight = none := by sorry

theorem popRight_toList {d : Deque' α} {x : α} {d' : Deque' α}
    (h : d.popRight = some (x, d')) :
    d'.toList ++ [x] = d.toList := by sorry

/-! ### `peekLeft` / `peekRight` -/

@[simp] theorem peekLeft_empty  : (empty : Deque' α).peekLeft  = none := by sorry
@[simp] theorem peekRight_empty : (empty : Deque' α).peekRight = none := by sorry

@[simp] theorem peekLeft_pushLeft (x : α) (d : Deque' α) :
    (d.pushLeft x).peekLeft = some x := by sorry

@[simp] theorem peekRight_pushRight (x : α) (d : Deque' α) :
    (d.pushRight x).peekRight = some x := by sorry

end Proofs

end Deque'
