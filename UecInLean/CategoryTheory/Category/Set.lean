import UecInLean.CategoryTheory.Category.Def

namespace UecInLean.CategoryTheory.Category
universe u

instance Set : Category.{u} (Type u) where
  hom A B := A → B
  id _ := _root_.id
  comp f g := fun x => g (f x)
  id_comp f := by rfl
  comp_id f := by rfl
  comp_assoc f g h := by rfl

@[simp, grind =]
theorem Set.hom_def {A B : Type u} : A ⟶ B = (A → B) := rfl
@[simp, grind =]
theorem Set.id_def {A : Type u} : 𝟙 A = _root_.id := rfl
theorem Set.id_app {A : Type u} (x : A) : (𝟙 A) x = x := rfl
@[simp, grind =]
theorem Set.comp_def {A B C : Type u} (f : A ⟶ B) (g : B ⟶ C) : f ≫ g = fun x => g (f x) := rfl
theorem Set.comp_app {A B C : Type u} (f : A ⟶ B) (g : B ⟶ C) (x : A) : (f ≫ g) x = g (f x) := rfl

end UecInLean.CategoryTheory.Category
