import UecInLean.CategoryTheory.Category.Def
import UecInLean.CategoryTheory.Category.Opposite

namespace UecInLean.CategoryTheory

universe v u
variable {C : Type u} [Category.{v} C]

structure Slice.Struct (c : C) where
  obj : C
  f : obj ⟶ c

structure Slice.Hom {c : C} (X Y : Slice.Struct c) where
  g : X.obj ⟶ Y.obj
  comm : g ≫ Y.f = X.f

instance Category.Slice {c : C} : Category (Slice.Struct c) where
  hom := Slice.Hom
  id X := ⟨𝟙 _, by simp⟩
  comp := by {
    intro _ _ _ ⟨f, comm⟩ ⟨g, comm'⟩
    exact ⟨f ≫ g, by rw [Category.comp_assoc, comm', comm]⟩
  }
  comp_id _ := by simp
  id_comp _ := by simp
  comp_assoc _ _ _ := by simp

instance Category.Coslice {c : Cᵒᵖ} : Category (Slice.Struct c) where
  hom := Slice.Hom
  id X := ⟨𝟙 _, by simp⟩
  comp := by {
    intro _ _ _ ⟨f, comm⟩ ⟨g, comm'⟩
    exact ⟨f ≫ g, by rw [Category.comp_assoc, comm', comm]⟩
  }
  comp_id _ := by simp
  id_comp _ := by simp
  comp_assoc _ _ _ := by simp

end UecInLean.CategoryTheory
