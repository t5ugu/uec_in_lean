import UecInLean.Category.Limit.Comma
import UecInLean.Category.Iso

namespace UecInLean

universe v u
variable {C : Type u} [Category.{v} C]

structure Slice (c : C) where
  obj : C
  f : obj ⟶ c

structure Slice.Hom {c : C} (X Y : Slice c) where
  g : X.obj ⟶ Y.obj
  comm : g ≫ Y.f = X.f

instance {c : C} : Category (Slice c) where
  hom := Slice.Hom
  id X := ⟨𝟙 _, by simp⟩
  comp := by {
    intro _ _ _ ⟨f, comm⟩ ⟨g, comm'⟩
    exact ⟨f ≫ g, by simp [comm', comm]⟩
  }
  comp_id _ := by simp
  id_comp _ := by simp
  comp_assoc _ _ _ := by simp

