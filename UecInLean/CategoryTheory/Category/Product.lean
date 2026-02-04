import UecInLean.CategoryTheory.Category.Def

namespace UecInLean.CategoryTheory

universe v v' u u'

instance Category.Product {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D] : Category (C × D) where
  hom X Y := (X.1 ⟶ Y.1) × (X.2 ⟶ Y.2)
  id X := (𝟙 X.1, 𝟙 X.2)
  comp f g := (f.1 ≫ g.1, f.2 ≫ g.2)
  id_comp f := by simp
  comp_id f := by simp
  comp_assoc f g h := by simp

@[simp, grind =]
theorem Category.Product_hom {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  (X Y : C × D) : X ⟶ Y = ((X.1 ⟶ Y.1) × (X.2 ⟶ Y.2)) := rfl
@[simp, grind =]
theorem Category.Product_id {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  (X : C × D) : 𝟙 X = (𝟙 X.1, 𝟙 X.2) := rfl
@[simp, grind =]
theorem Category.Product_comp {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  {X Y Z : C × D} (f : X ⟶ Y) (g : Y ⟶ Z) :
  f ≫ g = (f.1 ≫ g.1, f.2 ≫ g.2) := rfl
