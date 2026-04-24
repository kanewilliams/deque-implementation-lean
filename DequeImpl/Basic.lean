/-!
# Deque (Double-Ended Queue) in Lean 4

A deque implemented using two lists:
- `front`: elements at the front of the deque, in order
- `back`:  elements at the back of the deque, in *reverse* order

The logical sequence represented by a `Deque α` is `front ++ back.reverse`.
-/

universe u

/-- A double-ended queue (deque) backed by two lists. -/
structure Deque (α : Type u) where
  /-- Elements at the front, head = deque front. -/
  front : List α
  /-- Elements at the back, stored in reverse (head = deque back). -/
  back  : List α
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
  d.front.isEmpty && d.back.isEmpty

/-- The number of elements in the deque. -/
def size (d : Deque α) : Nat :=
  d.front.length + d.back.length

/-! ## Insertion -/

/-- Push an element onto the front of the deque. -/
def pushFront (x : α) (d : Deque α) : Deque α :=
  { d with front := x :: d.front }

/-- Push an element onto the back of the deque. -/
def pushBack (x : α) (d : Deque α) : Deque α :=
  { d with back := x :: d.back }

/-! ## Inspection -/

/-- The logical list representation: `front ++ back.reverse`. -/
def toList (d : Deque α) : List α :=
  d.front ++ d.back.reverse

/-- Peek at the front element without removing it. -/
def peekFront (d : Deque α) : Option α :=
  match d.front, d.back with
  | x :: _, _  => some x
  | [],     [] => none
  | [],     b  => b.reverse.head?

/-- Peek at the back element without removing it. -/
def peekBack (d : Deque α) : Option α :=
  match d.back, d.front with
  | x :: _, _  => some x
  | [],     [] => none
  | [],     f  => f.reverse.head?

/-! ## Removal -/

/-- Remove the front element, returning it together with the remaining deque.
    When the front list is exhausted the back list is reversed and used as the
    new front (standard "two-list" rebalance). -/
def popFront (d : Deque α) : Option (α × Deque α) :=
  match d.front, d.back with
  | x :: f', b => some (x, ⟨f', b⟩)
  | [],      [] => none
  | [],      b  =>
    match b.reverse with
    | []       => none   -- unreachable: b is non-empty
    | x :: f' => some (x, ⟨f', []⟩)

/-- Remove the back element, returning it together with the remaining deque.
    When the back list is exhausted the front list is reversed and used as the
    new back. -/
def popBack (d : Deque α) : Option (α × Deque α) :=
  match d.back, d.front with
  | x :: b', f => some (x, ⟨f, b'⟩)
  | [],      [] => none
  | [],      f  =>
    match f.reverse with
    | []       => none   -- unreachable: f is non-empty
    | x :: b' => some (x, ⟨[], b'⟩)

/-! ## Proofs -/

section Proofs

/-! ### `empty` -/

@[simp] theorem empty_front : (empty : Deque α).front = [] := rfl
@[simp] theorem empty_back  : (empty : Deque α).back  = [] := rfl

@[simp] theorem empty_isEmpty : (empty : Deque α).isEmpty = true := rfl

@[simp] theorem empty_size : (empty : Deque α).size = 0 := rfl

@[simp] theorem empty_toList : (empty : Deque α).toList = [] := rfl

/-! ### `singleton` -/

@[simp] theorem singleton_size (x : α) : (singleton x).size = 1 := rfl

@[simp] theorem singleton_toList (x : α) : (singleton x).toList = [x] := rfl

@[simp] theorem singleton_not_isEmpty (x : α) : (singleton x).isEmpty = false := rfl

/-! ### `size` -/

@[simp] theorem pushFront_size (x : α) (d : Deque α) :
    (d.pushFront x).size = d.size + 1 := by
  simp [pushFront, size]; omega

@[simp] theorem pushBack_size (x : α) (d : Deque α) :
    (d.pushBack x).size = d.size + 1 := by
  simp [pushBack, size]; omega

/-! ### `isEmpty` -/

@[simp] theorem pushFront_not_isEmpty (x : α) (d : Deque α) :
    (d.pushFront x).isEmpty = false := by
  simp [pushFront, isEmpty]

@[simp] theorem pushBack_not_isEmpty (x : α) (d : Deque α) :
    (d.pushBack x).isEmpty = false := by
  simp [pushBack, isEmpty]

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

@[simp] theorem pushFront_toList (x : α) (d : Deque α) :
    (d.pushFront x).toList = x :: d.toList := by
  simp [pushFront, toList]

@[simp] theorem pushBack_toList (x : α) (d : Deque α) :
    (d.pushBack x).toList = d.toList ++ [x] := by
  simp [pushBack, toList]

/-! ### `popFront` -/

/-- Popping the front of a `pushFront` recovers the pushed element and original deque. -/
@[simp] theorem popFront_pushFront (x : α) (d : Deque α) :
    (d.pushFront x).popFront = some (x, d) := by
  simp [pushFront, popFront]

/-- `popFront` on the empty deque is `none`. -/
@[simp] theorem popFront_empty : (empty : Deque α).popFront = none := rfl

/-- If `popFront` returns `some (x, d')`, then `x :: d'.toList = d.toList`. -/
theorem popFront_toList {d : Deque α} {x : α} {d' : Deque α}
    (h : d.popFront = some (x, d')) :
    x :: d'.toList = d.toList := by
  rcases d with ⟨_ | ⟨y, f'⟩, b⟩
  · -- d.front = []
    rcases b with _ | ⟨z, b'⟩
    · simp [popFront] at h
    · -- d.back = z :: b'
      simp only [popFront] at h
      rcases hr : (z :: b').reverse with _ | ⟨w, rest⟩
      · exact absurd hr (by simp [List.reverse_eq_nil_iff])
      · rw [hr] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [toList, List.nil_append, List.append_nil, List.reverse_nil]
        exact hr.symm
  · -- d.front = y :: f'
    simp only [popFront] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [toList]

/-! ### `popBack` -/

/-- Popping the back of a `pushBack` recovers the pushed element and original deque. -/
@[simp] theorem popBack_pushBack (x : α) (d : Deque α) :
    (d.pushBack x).popBack = some (x, d) := by
  simp [pushBack, popBack]

/-- `popBack` on the empty deque is `none`. -/
@[simp] theorem popBack_empty : (empty : Deque α).popBack = none := rfl

/-- If `popBack` returns `some (x, d')`, then `d'.toList ++ [x] = d.toList`. -/
theorem popBack_toList {d : Deque α} {x : α} {d' : Deque α}
    (h : d.popBack = some (x, d')) :
    d'.toList ++ [x] = d.toList := by
  rcases d with ⟨f, _ | ⟨z, b'⟩⟩
  · -- d.back = []
    rcases f with _ | ⟨y, f'⟩
    · simp [popBack] at h
    · -- d.front = y :: f'
      simp only [popBack] at h
      rcases hr : (y :: f').reverse with _ | ⟨w, rest⟩
      · exact absurd hr (by simp [List.reverse_eq_nil_iff])
      · rw [hr] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [toList, List.nil_append, List.append_nil, List.reverse_nil]
        have h3 := congrArg List.reverse hr
        simp [List.reverse_cons] at h3
        exact h3.symm
  · -- d.back = z :: b'
    simp only [popBack] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [toList]

/-! ### Push-pop round-trip -/

/-- Pushing to the front and immediately popping from the front is the identity. -/
theorem pushFront_popFront (x : α) (d : Deque α) :
    (d.pushFront x).popFront = some (x, d) := popFront_pushFront x d

/-- Pushing to the back and immediately popping from the back is the identity. -/
theorem pushBack_popBack (x : α) (d : Deque α) :
    (d.pushBack x).popBack = some (x, d) := popBack_pushBack x d

/-! ### `peekFront` / `peekBack` -/

@[simp] theorem peekFront_empty : (empty : Deque α).peekFront = none := rfl
@[simp] theorem peekBack_empty  : (empty : Deque α).peekBack  = none := rfl

@[simp] theorem peekFront_pushFront (x : α) (d : Deque α) :
    (d.pushFront x).peekFront = some x := by
  simp [pushFront, peekFront]

@[simp] theorem peekBack_pushBack (x : α) (d : Deque α) :
    (d.pushBack x).peekBack = some x := by
  simp [pushBack, peekBack]

end Proofs

end Deque
