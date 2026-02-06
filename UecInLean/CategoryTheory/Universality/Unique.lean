import Mathlib.Logic.Unique

theorem Unique.allEq {α : Type*} [h : Unique α] (x y : α) : x = y := h.instSubsingleton.allEq x y

namespace UecInLean.CategoryTheory

universe u v

class UniqueUpTo (α : Type u) (rel : α → α → Sort v) extends Inhabited α where
  unique : ∀ x : α, rel x default

instance {α : Type u} [h : UniqueUpTo α Eq] : Subsingleton α where
  allEq x y := by rw [h.unique x, ← h.unique y];
