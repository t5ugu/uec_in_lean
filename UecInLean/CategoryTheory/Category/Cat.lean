import UecInLean.CategoryTheory.Category.Def
import UecInLean.CategoryTheory.Functor.Def

namespace UecInLean.CategoryTheory.Category

universe v u

structure Cat where
  cat : Type u
  inst : Category.{v} cat

instance (C : Cat) : Category.{v} C.cat := C.inst
instance : CoeSort Cat (Type u) := ⟨Cat.cat⟩

instance : Category Cat where
  hom C D := C ⥤ D
  id C := Functor.id C
  comp := Functor.comp
  id_comp F := by rfl
  comp_id F := by rfl
  comp_assoc F G H := by rfl

@[simp]
theorem Cat.hom_def (C D : Cat) : C ⟶ D = (C ⥤ D) := rfl
@[simp]
theorem Cat.id_def (C : Cat) : 𝟙 C = Functor.id C := rfl
@[simp]
theorem Cat.comp_def {C D E : Cat} (F : C ⟶ D) (G : D ⟶ E) : F ≫ G = F ⋙ G := rfl
