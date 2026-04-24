/-!
# Deque (Double-Ended Queue) in Lean 4

A deque implemented using two lists:
- `left`:  elements at the left end of the deque, in order
- `right`: elements at the right end of the deque, in *reverse* order

The logical sequence represented by a `Deque α` is `left ++ right.reverse`.
-/

universe u

/-- A double-ended queue (deque) backed by two lists. -/
structure Deque (α : Type u) where
  /-- Elements at the left end, head = leftmost element. -/
  left  : List α
  /-- Elements at the right end, stored in reverse (head = rightmost element). -/
  right : List α
  deriving Repr

namespace Deque

variable {α : Type u}

/-! ## Construction -/

/-- The empty deque. -/
def empty : Deque α := ⟨[], []⟩

/-- Create a singleton deque. -/
def singleton (x : α) : Deque α := ⟨[x], []⟩

/-! ## Basic predicates -/

/-- Returns `true` iff the deque contains no elements. -/
def isEmpty (d : Deque α) : Bool :=
  d.left.isEmpty && d.right.isEmpty

/-- The number of elements in the deque. -/
def size (d : Deque α) : Nat :=
  d.left.length + d.right.length

/-! ## Insertion -/

/-- Push an element onto the left end of the deque. -/
def pushLeft (x : α) (d : Deque α) : Deque α :=
  { d with left := x :: d.left }

/-- Push an element onto the right end of the deque. -/
def pushRight (x : α) (d : Deque α) : Deque α :=
  { d with right := x :: d.right }

/-! ## Inspection -/

/-- The logical list representation: `left ++ right.reverse`. -/
def toList (d : Deque α) : List α :=
  d.left ++ d.right.reverse

/-- Peek at the leftmost element without removing it. -/
def peekLeft (d : Deque α) : Option α :=
  match d.left, d.right with
  | x :: _, _  => some x
  | [],     [] => none
  | [],     r  => r.reverse.head?

/-- Peek at the rightmost element without removing it. -/
def peekRight (d : Deque α) : Option α :=
  match d.right, d.left with
  | x :: _, _  => some x
  | [],     [] => none
  | [],     l  => l.reverse.head?

/-! ## Removal -/

/-- Remove the leftmost element, returning it together with the remaining deque.
    When the left list is exhausted the right list is reversed and used as the
    new left (standard "two-list" rebalance). -/
def popLeft (d : Deque α) : Option (α × Deque α) :=
  match d.left, d.right with
  | x :: l', r => some (x, ⟨l', r⟩)
  | [],      [] => none
  | [],      r  =>
    match r.reverse with
    | []       => none   -- unreachable: r is non-empty
    | x :: l' => some (x, ⟨l', []⟩)

/-- Remove the rightmost element, returning it together with the remaining deque.
    When the right list is exhausted the left list is reversed and used as the
    new right. -/
def popRight (d : Deque α) : Option (α × Deque α) :=
  match d.right, d.left with
  | x :: r', l => some (x, ⟨l, r'⟩)
  | [],      [] => none
  | [],      l  =>
    match l.reverse with
    | []       => none   -- unreachable: l is non-empty
    | x :: r' => some (x, ⟨[], r'⟩)

/-! ## Proofs -/

section Proofs

/-! ### `empty` -/

@[simp] theorem empty_left  : (empty : Deque α).left  = [] := rfl
@[simp] theorem empty_right : (empty : Deque α).right = [] := rfl

@[simp] theorem empty_isEmpty : (empty : Deque α).isEmpty = true := rfl

@[simp] theorem empty_size : (empty : Deque α).size = 0 := rfl

@[simp] theorem empty_toList : (empty : Deque α).toList = [] := rfl

/-! ### `singleton` -/

@[simp] theorem singleton_size (x : α) : (singleton x).size = 1 := rfl

@[simp] theorem singleton_toList (x : α) : (singleton x).toList = [x] := rfl

@[simp] theorem singleton_not_isEmpty (x : α) : (singleton x).isEmpty = false := rfl

/-! ### `size` -/

@[simp] theorem pushLeft_size (x : α) (d : Deque α) :
    (d.pushLeft x).size = d.size + 1 := by
  simp [pushLeft, size]; omega

@[simp] theorem pushRight_size (x : α) (d : Deque α) :
    (d.pushRight x).size = d.size + 1 := by
  simp [pushRight, size]; omega

/-! ### `isEmpty` -/

@[simp] theorem pushLeft_not_isEmpty (x : α) (d : Deque α) :
    (d.pushLeft x).isEmpty = false := by
  simp [pushLeft, isEmpty]

@[simp] theorem pushRight_not_isEmpty (x : α) (d : Deque α) :
    (d.pushRight x).isEmpty = false := by
  simp [pushRight, isEmpty]

theorem isEmpty_iff_size_zero (d : Deque α) :
    d.isEmpty = true ↔ d.size = 0 := by
  simp only [isEmpty, size, Bool.and_eq_true, List.isEmpty_iff, ← List.length_eq_zero]
  constructor
  · intro ⟨h1, h2⟩; omega
  · intro h; exact ⟨by omega, by omega⟩

theorem isEmpty_iff_toList_nil (d : Deque α) :
    d.isEmpty = true ↔ d.toList = [] := by
  simp only [isEmpty, toList, Bool.and_eq_true, List.isEmpty_iff,
             List.append_eq_nil, List.reverse_eq_nil_iff]

/-! ### `toList` -/

@[simp] theorem pushLeft_toList (x : α) (d : Deque α) :
    (d.pushLeft x).toList = x :: d.toList := by
  simp [pushLeft, toList]

@[simp] theorem pushRight_toList (x : α) (d : Deque α) :
    (d.pushRight x).toList = d.toList ++ [x] := by
  simp [pushRight, toList]

/-! ### `popLeft` -/

/-- Popping the left end of a `pushLeft` recovers the pushed element and original deque. -/
@[simp] theorem popLeft_pushLeft (x : α) (d : Deque α) :
    (d.pushLeft x).popLeft = some (x, d) := by
  simp [pushLeft, popLeft]

/-- `popLeft` on the empty deque is `none`. -/
@[simp] theorem popLeft_empty : (empty : Deque α).popLeft = none := rfl

/-- If `popLeft` returns `some (x, d')`, then `x :: d'.toList = d.toList`. -/
theorem popLeft_toList {d : Deque α} {x : α} {d' : Deque α}
    (h : d.popLeft = some (x, d')) :
    x :: d'.toList = d.toList := by
  rcases d with ⟨_ | ⟨y, l'⟩, r⟩
  · -- d.left = []
    rcases r with _ | ⟨z, r'⟩
    · simp [popLeft] at h
    · -- d.right = z :: r'
      simp only [popLeft] at h
      rcases hr : (z :: r').reverse with _ | ⟨w, rest⟩
      · exact absurd hr (by simp [List.reverse_eq_nil_iff])
      · rw [hr] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [toList, List.nil_append, List.append_nil, List.reverse_nil]
        exact hr.symm
  · -- d.left = y :: l'
    simp only [popLeft] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [toList]

/-! ### `popRight` -/

/-- Popping the right end of a `pushRight` recovers the pushed element and original deque. -/
@[simp] theorem popRight_pushRight (x : α) (d : Deque α) :
    (d.pushRight x).popRight = some (x, d) := by
  simp [pushRight, popRight]

/-- `popRight` on the empty deque is `none`. -/
@[simp] theorem popRight_empty : (empty : Deque α).popRight = none := rfl

/-- If `popRight` returns `some (x, d')`, then `d'.toList ++ [x] = d.toList`. -/
theorem popRight_toList {d : Deque α} {x : α} {d' : Deque α}
    (h : d.popRight = some (x, d')) :
    d'.toList ++ [x] = d.toList := by
  rcases d with ⟨l, _ | ⟨z, r'⟩⟩
  · -- d.right = []
    rcases l with _ | ⟨y, l'⟩
    · simp [popRight] at h
    · -- d.left = y :: l'
      simp only [popRight] at h
      rcases hr : (y :: l').reverse with _ | ⟨w, rest⟩
      · exact absurd hr (by simp [List.reverse_eq_nil_iff])
      · rw [hr] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [toList, List.nil_append, List.append_nil, List.reverse_nil]
        have h3 := congrArg List.reverse hr
        simp [List.reverse_cons] at h3
        exact h3.symm
  · -- d.right = z :: r'
    simp only [popRight] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [toList]

/-! ### Push-pop round-trip -/

/-- Pushing to the left and immediately popping from the left is the identity. -/
theorem pushLeft_popLeft (x : α) (d : Deque α) :
    (d.pushLeft x).popLeft = some (x, d) := popLeft_pushLeft x d

/-- Pushing to the right and immediately popping from the right is the identity. -/
theorem pushRight_popRight (x : α) (d : Deque α) :
    (d.pushRight x).popRight = some (x, d) := popRight_pushRight x d

/-! ### `peekLeft` / `peekRight` -/

@[simp] theorem peekLeft_empty  : (empty : Deque α).peekLeft  = none := rfl
@[simp] theorem peekRight_empty : (empty : Deque α).peekRight = none := rfl

@[simp] theorem peekLeft_pushLeft (x : α) (d : Deque α) :
    (d.pushLeft x).peekLeft = some x := by
  simp [pushLeft, peekLeft]

@[simp] theorem peekRight_pushRight (x : α) (d : Deque α) :
    (d.pushRight x).peekRight = some x := by
  simp [pushRight, peekRight]

end Proofs

end Deque
