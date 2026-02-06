import UecInLean.CategoryTheory.NatTrans

namespace UecInLean.CategoryTheory.Category

universe v v' u u'

instance (C : Type u) (D : Type u') [Category.{v} C] [Category.{v'} D] : Category (C ⥤ D) where
  hom := NatTrans
  id := .id
  comp := .vcomp
  id_comp _ := by ext; rw [NatTrans.vcomp_app, NatTrans.id_app, Category.id_comp]
  comp_id _ := by ext; rw [NatTrans.vcomp_app, NatTrans.id_app, Category.comp_id]
  comp_assoc _ _ _ := by ext; rw [NatTrans.vcomp_app, NatTrans.vcomp_app, NatTrans.vcomp_app, NatTrans.vcomp_app, Category.comp_assoc]

@[simp, grind =]
theorem Functor.hom_def {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  (F G : C ⥤ D) : F ⟶ G = F ⟹ G := rfl
@[simp, grind =]
theorem Functor.id_def {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  (F : C ⥤ D) : 𝟙 F = NatTrans.id F := rfl
@[simp, grind =]
theorem Functor.comp_def {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  {F G H : C ⥤ D} (η : F ⟶ G) (θ : G ⟶ H) : η ≫ θ = NatTrans.vcomp η θ := rfl

theorem Functor.id_app {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  (F : C ⥤ D) (X : C) : (𝟙 F).app X = 𝟙 (F.obj X) := rfl
theorem Functor.comp_app {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  {F G H : C ⥤ D} (η : F ⟶ G) (θ : G ⟶ H) (X : C) :
    (η ≫ θ).app X = η.app X ≫ θ.app X := rfl
