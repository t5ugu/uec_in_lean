import UecInLean.CategoryTheory.Category.Def

namespace UecInLean.CategoryTheory.Category

universe v v' u u'

instance instProduct {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D] : Category (C × D) where
  hom X Y := (X.1 ⟶ Y.1) × (X.2 ⟶ Y.2)
  id X := (𝟙 X.1, 𝟙 X.2)
  comp f g := (f.1 ≫ g.1, f.2 ≫ g.2)
  id_comp := by simp
  comp_id := by simp
  comp_assoc := by simp

@[simp]
theorem Product.hom_def {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  (X Y : C × D) : X ⟶ Y = ((X.1 ⟶ Y.1) × (X.2 ⟶ Y.2)) := rfl

@[simp]
theorem Product.id_def {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  (X : C × D) : 𝟙 X = (𝟙 X.1, 𝟙 X.2) := rfl

@[simp]
theorem Product.comp_def {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  {X Y Z : C × D} (f : X ⟶ Y) (g : Y ⟶ Z) :
  f ≫ g = (f.1 ≫ g.1, f.2 ≫ g.2) := rfl
