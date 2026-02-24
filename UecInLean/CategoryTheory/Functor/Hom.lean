import UecInLean.CategoryTheory.Category.Set
import UecInLean.CategoryTheory.Functor.Def

namespace UecInLean.CategoryTheory.Functor
universe v u
variable {C : Type u} [Category.{v} C]

def Hom (a : C) : C ⥤ Type v where
  obj b := a ⟶ b
  map f g := g ≫ f
  map_id := by simp
  map_comp := by simp

@[simp]
theorem Hom.obj_def (a b : C) : (Hom a).obj b = (a ⟶ b) := rfl
@[simp]
theorem Hom.map_def {a b c : C} (f : b ⟶ c) (g : a ⟶ b) : (Hom a).map f g = g ≫ f := rfl

end UecInLean.CategoryTheory.Functor
