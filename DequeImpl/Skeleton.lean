universe u

abbrev NodeId := Nat

structure Node (α : Type u) where
  val  : α
  prev : Option NodeId
  next : Option NodeId
  deriving Repr

structure Deque (α : Type u) where
  head : Option NodeId
  tail : Option NodeId
  deriving Repr

namespace Deque

variable {α : Type u}

def empty : Deque α := sorry

def singleton (x : α) : Deque α := sorry

def isEmpty (d : Deque α) : Bool := sorry

def size (d : Deque α) : Nat := sorry

def pushLeft (x : α) (d : Deque α) : Deque α := sorry

def pushRight (x : α) (d : Deque α) : Deque α := sorry

def toList (d : Deque α) : List α := sorry

def peekLeft (d : Deque α) : Option α := sorry

def peekRight (d : Deque α) : Option α := sorry

def popLeft (d : Deque α) : Option (α × Deque α) := sorry

def popRight (d : Deque α) : Option (α × Deque α) := sorry

section Proofs

@[simp] theorem empty_head : (empty : Deque α).head = none := by sorry
@[simp] theorem empty_tail : (empty : Deque α).tail = none := by sorry

@[simp] theorem empty_isEmpty : (empty : Deque α).isEmpty = true  := by sorry
@[simp] theorem empty_size    : (empty : Deque α).size    = 0     := by sorry
@[simp] theorem empty_toList  : (empty : Deque α).toList  = []    := by sorry

@[simp] theorem singleton_size (x : α) : (singleton x).size = 1           := by sorry
@[simp] theorem singleton_toList (x : α) : (singleton x).toList = [x]     := by sorry
@[simp] theorem singleton_not_isEmpty (x : α) : (singleton x).isEmpty = false := by sorry

@[simp] theorem pushLeft_size (x : α) (d : Deque α) :
    (d.pushLeft x).size = d.size + 1 := by sorry

@[simp] theorem pushRight_size (x : α) (d : Deque α) :
    (d.pushRight x).size = d.size + 1 := by sorry

@[simp] theorem pushLeft_not_isEmpty (x : α) (d : Deque α) :
    (d.pushLeft x).isEmpty = false := by sorry

@[simp] theorem pushRight_not_isEmpty (x : α) (d : Deque α) :
    (d.pushRight x).isEmpty = false := by sorry

theorem isEmpty_iff_size_zero (d : Deque α) :
    d.isEmpty = true ↔ d.size = 0 := by sorry

theorem isEmpty_iff_toList_nil (d : Deque α) :
    d.isEmpty = true ↔ d.toList = [] := by sorry

@[simp] theorem pushLeft_toList (x : α) (d : Deque α) :
    (d.pushLeft x).toList = x :: d.toList := by sorry

@[simp] theorem pushRight_toList (x : α) (d : Deque α) :
    (d.pushRight x).toList = d.toList ++ [x] := by sorry

@[simp] theorem popLeft_empty : (empty : Deque α).popLeft = none := by sorry

@[simp] theorem popLeft_pushLeft (x : α) (d : Deque α) :
    (d.pushLeft x).popLeft = some (x, d) := by sorry

theorem popLeft_toList {d : Deque α} {x : α} {d' : Deque α}
    (h : d.popLeft = some (x, d')) :
    x :: d'.toList = d.toList := by sorry

@[simp] theorem popRight_empty : (empty : Deque α).popRight = none := by sorry

@[simp] theorem popRight_pushRight (x : α) (d : Deque α) :
    (d.pushRight x).popRight = some (x, d) := by sorry

theorem popRight_toList {d : Deque α} {x : α} {d' : Deque α}
    (h : d.popRight = some (x, d')) :
    d'.toList ++ [x] = d.toList := by sorry

@[simp] theorem peekLeft_empty  : (empty : Deque α).peekLeft  = none := by sorry
@[simp] theorem peekRight_empty : (empty : Deque α).peekRight = none := by sorry

@[simp] theorem peekLeft_pushLeft (x : α) (d : Deque α) :
    (d.pushLeft x).peekLeft = some x := by sorry

@[simp] theorem peekRight_pushRight (x : α) (d : Deque α) :
    (d.pushRight x).peekRight = some x := by sorry

end Proofs

end Deque
