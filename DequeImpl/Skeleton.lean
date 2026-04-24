universe u

abbrev NodeId := Nat

structure Node (α : Type u) where
  val  : α
  prev : Option NodeId
  next : Option NodeId
  deriving Repr

structure LinkedDeque (α : Type u) where
  nodes : Array (Node α)
  head  : Option NodeId
  tail  : Option NodeId
  deriving Repr

namespace LinkedDeque

variable {α : Type u}

def empty : LinkedDeque α := sorry

def singleton (x : α) : LinkedDeque α := sorry

def isEmpty (d : LinkedDeque α) : Bool := sorry

def size (d : LinkedDeque α) : Nat := sorry

def pushLeft (x : α) (d : LinkedDeque α) : LinkedDeque α := sorry

def pushRight (x : α) (d : LinkedDeque α) : LinkedDeque α := sorry

def toList (d : LinkedDeque α) : List α := sorry

def peekLeft (d : LinkedDeque α) : Option α := sorry

def peekRight (d : LinkedDeque α) : Option α := sorry

def popLeft (d : LinkedDeque α) : Option (α × LinkedDeque α) := sorry

def popRight (d : LinkedDeque α) : Option (α × LinkedDeque α) := sorry

section Proofs

@[simp] theorem empty_head  : (empty : LinkedDeque α).head = none := by sorry
@[simp] theorem empty_tail  : (empty : LinkedDeque α).tail = none := by sorry
@[simp] theorem empty_nodes : (empty : LinkedDeque α).nodes = #[]  := by sorry

@[simp] theorem empty_isEmpty : (empty : LinkedDeque α).isEmpty = true  := by sorry
@[simp] theorem empty_size    : (empty : LinkedDeque α).size    = 0     := by sorry
@[simp] theorem empty_toList  : (empty : LinkedDeque α).toList  = []    := by sorry

@[simp] theorem singleton_size (x : α) : (singleton x).size = 1           := by sorry
@[simp] theorem singleton_toList (x : α) : (singleton x).toList = [x]     := by sorry
@[simp] theorem singleton_not_isEmpty (x : α) : (singleton x).isEmpty = false := by sorry

@[simp] theorem pushLeft_size (x : α) (d : LinkedDeque α) :
    (d.pushLeft x).size = d.size + 1 := by sorry

@[simp] theorem pushRight_size (x : α) (d : LinkedDeque α) :
    (d.pushRight x).size = d.size + 1 := by sorry

@[simp] theorem pushLeft_not_isEmpty (x : α) (d : LinkedDeque α) :
    (d.pushLeft x).isEmpty = false := by sorry

@[simp] theorem pushRight_not_isEmpty (x : α) (d : LinkedDeque α) :
    (d.pushRight x).isEmpty = false := by sorry

theorem isEmpty_iff_size_zero (d : LinkedDeque α) :
    d.isEmpty = true ↔ d.size = 0 := by sorry

theorem isEmpty_iff_toList_nil (d : LinkedDeque α) :
    d.isEmpty = true ↔ d.toList = [] := by sorry

@[simp] theorem pushLeft_toList (x : α) (d : LinkedDeque α) :
    (d.pushLeft x).toList = x :: d.toList := by sorry

@[simp] theorem pushRight_toList (x : α) (d : LinkedDeque α) :
    (d.pushRight x).toList = d.toList ++ [x] := by sorry

@[simp] theorem popLeft_empty : (empty : LinkedDeque α).popLeft = none := by sorry

@[simp] theorem popLeft_pushLeft (x : α) (d : LinkedDeque α) :
    (d.pushLeft x).popLeft = some (x, d) := by sorry

theorem popLeft_toList {d : LinkedDeque α} {x : α} {d' : LinkedDeque α}
    (h : d.popLeft = some (x, d')) :
    x :: d'.toList = d.toList := by sorry

@[simp] theorem popRight_empty : (empty : LinkedDeque α).popRight = none := by sorry

@[simp] theorem popRight_pushRight (x : α) (d : LinkedDeque α) :
    (d.pushRight x).popRight = some (x, d) := by sorry

theorem popRight_toList {d : LinkedDeque α} {x : α} {d' : LinkedDeque α}
    (h : d.popRight = some (x, d')) :
    d'.toList ++ [x] = d.toList := by sorry

@[simp] theorem peekLeft_empty  : (empty : LinkedDeque α).peekLeft  = none := by sorry
@[simp] theorem peekRight_empty : (empty : LinkedDeque α).peekRight = none := by sorry

@[simp] theorem peekLeft_pushLeft (x : α) (d : LinkedDeque α) :
    (d.pushLeft x).peekLeft = some x := by sorry

@[simp] theorem peekRight_pushRight (x : α) (d : LinkedDeque α) :
    (d.pushRight x).peekRight = some x := by sorry

end Proofs

end LinkedDeque
