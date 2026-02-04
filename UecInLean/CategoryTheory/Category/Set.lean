import UecInLean.CategoryTheory.Category.Def

namespace UecInLean.CategoryTheory
universe u

instance Category.Set : Category.{u} (Type u) where
  hom A B := A → B
  id _ := _root_.id
  comp f g := fun x => g (f x)
  id_comp f := by rfl
  comp_id f := by rfl
  comp_assoc f g h := by rfl

@[simp, grind =]
theorem Category.Set_hom {A B : Type u} : A ⟶ B = (A → B) := rfl
@[simp, grind =]
theorem Category.Set_id {A : Type u} : 𝟙 A = _root_.id := rfl
@[simp, grind =]
theorem Category.Set_comp {A B C : Type u} (f : A ⟶ B) (g : B ⟶ C) : f ≫ g = fun x => g (f x) := rfl
