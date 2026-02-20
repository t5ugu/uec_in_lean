
universe u v

class Unique (α : Sort u) extends Inhabited α where
  unique : ∀ x : α, x = default

def Unique.of_default_of_unique {α : Sort u} (default : α) (unique : ∀ x : α, x = default) : Unique α :=
  { default := default, unique := unique }

def Unique.of_default_of_allEq {α : Sort u} (default : α) (allEq : ∀ x y : α, x = y) : Unique α :=
  { default := default, unique := fun x => allEq x default }

namespace Unique
instance {α : Sort u} [h : Unique α] : Subsingleton α where
  allEq x y := by rw [h.unique x, ← h.unique y];

theorem allEq {α : Type u} [h : Unique α] (x y : α) : x = y := h.instSubsingleton.allEq x y
end Unique

namespace UecInLean.CategoryTheory

class UniqueUpTo (α : Type u) (rel : α → α → Sort v) extends Inhabited α where
  unique : ∀ x : α, rel x default

namespace UniqueUpTo
instance {α : Type u} [h : UniqueUpTo α Eq] : Subsingleton α where
  allEq x y := by rw [h.unique x, ← h.unique y];
