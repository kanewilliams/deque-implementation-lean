universe u

structure Deque (α : Type u) where
  left  : List α
  right : List α
  deriving Repr

namespace Deque

variable {α : Type u}

def empty : Deque α := ⟨[], []⟩

def singleton (x : α) : Deque α := ⟨[x], []⟩

def isEmpty (d : Deque α) : Bool :=
  d.left.isEmpty && d.right.isEmpty

def size (d : Deque α) : Nat :=
  d.left.length + d.right.length

def pushLeft (x : α) (d : Deque α) : Deque α :=
  { d with left := x :: d.left }

def pushRight (x : α) (d : Deque α) : Deque α :=
  { d with right := x :: d.right }

def toList (d : Deque α) : List α :=
  d.left ++ d.right.reverse

def peekLeft (d : Deque α) : Option α :=
  match d.left, d.right with
  | x :: _, _  => some x
  | [],     [] => none
  | [],     r  => r.reverse.head?

def peekRight (d : Deque α) : Option α :=
  match d.right, d.left with
  | x :: _, _  => some x
  | [],     [] => none
  | [],     l  => l.reverse.head?

def popLeft (d : Deque α) : Option (α × Deque α) :=
  match d.left, d.right with
  | x :: l', r => some (x, ⟨l', r⟩)
  | [],      [] => none
  | [],      r  =>
    match r.reverse with
    | []       => none
    | x :: l' => some (x, ⟨l', []⟩)

def popRight (d : Deque α) : Option (α × Deque α) :=
  match d.right, d.left with
  | x :: r', l => some (x, ⟨l, r'⟩)
  | [],      [] => none
  | [],      l  =>
    match l.reverse with
    | []       => none
    | x :: r' => some (x, ⟨[], r'⟩)

section Proofs

@[simp] theorem empty_left  : (empty : Deque α).left  = [] := rfl
@[simp] theorem empty_right : (empty : Deque α).right = [] := rfl

@[simp] theorem empty_isEmpty : (empty : Deque α).isEmpty = true := rfl

@[simp] theorem empty_size : (empty : Deque α).size = 0 := rfl

@[simp] theorem empty_toList : (empty : Deque α).toList = [] := rfl

@[simp] theorem singleton_size (x : α) : (singleton x).size = 1 := rfl

@[simp] theorem singleton_toList (x : α) : (singleton x).toList = [x] := rfl

@[simp] theorem singleton_not_isEmpty (x : α) : (singleton x).isEmpty = false := rfl

@[simp] theorem pushLeft_size (x : α) (d : Deque α) :
    (d.pushLeft x).size = d.size + 1 := by
  simp [pushLeft, size]; omega

@[simp] theorem pushRight_size (x : α) (d : Deque α) :
    (d.pushRight x).size = d.size + 1 := by
  simp [pushRight, size]; omega

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

@[simp] theorem pushLeft_toList (x : α) (d : Deque α) :
    (d.pushLeft x).toList = x :: d.toList := by
  simp [pushLeft, toList]

@[simp] theorem pushRight_toList (x : α) (d : Deque α) :
    (d.pushRight x).toList = d.toList ++ [x] := by
  simp [pushRight, toList]

@[simp] theorem popLeft_pushLeft (x : α) (d : Deque α) :
    (d.pushLeft x).popLeft = some (x, d) := by
  simp [pushLeft, popLeft]

@[simp] theorem popLeft_empty : (empty : Deque α).popLeft = none := rfl

theorem popLeft_toList {d : Deque α} {x : α} {d' : Deque α}
    (h : d.popLeft = some (x, d')) :
    x :: d'.toList = d.toList := by
  rcases d with ⟨_ | ⟨y, l'⟩, r⟩
  · rcases r with _ | ⟨z, r'⟩
    · simp [popLeft] at h
    · simp only [popLeft] at h
      rcases hr : (z :: r').reverse with _ | ⟨w, rest⟩
      · exact absurd hr (by simp [List.reverse_eq_nil_iff])
      · rw [hr] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [toList, List.nil_append, List.append_nil, List.reverse_nil]
        exact hr.symm
  · simp only [popLeft] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [toList]

@[simp] theorem popRight_pushRight (x : α) (d : Deque α) :
    (d.pushRight x).popRight = some (x, d) := by
  simp [pushRight, popRight]

@[simp] theorem popRight_empty : (empty : Deque α).popRight = none := rfl

theorem popRight_toList {d : Deque α} {x : α} {d' : Deque α}
    (h : d.popRight = some (x, d')) :
    d'.toList ++ [x] = d.toList := by
  rcases d with ⟨l, _ | ⟨z, r'⟩⟩
  · rcases l with _ | ⟨y, l'⟩
    · simp [popRight] at h
    · simp only [popRight] at h
      rcases hr : (y :: l').reverse with _ | ⟨w, rest⟩
      · exact absurd hr (by simp [List.reverse_eq_nil_iff])
      · rw [hr] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [toList, List.nil_append, List.append_nil, List.reverse_nil]
        have h3 := congrArg List.reverse hr
        simp [List.reverse_cons] at h3
        exact h3.symm
  · simp only [popRight] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [toList]

theorem pushLeft_popLeft (x : α) (d : Deque α) :
    (d.pushLeft x).popLeft = some (x, d) := popLeft_pushLeft x d

theorem pushRight_popRight (x : α) (d : Deque α) :
    (d.pushRight x).popRight = some (x, d) := popRight_pushRight x d

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
