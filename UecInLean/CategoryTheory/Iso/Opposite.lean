import UecInLean.CategoryTheory.Category.Opposite
import UecInLean.CategoryTheory.Category.Functor
import UecInLean.CategoryTheory.Category.Set
import UecInLean.CategoryTheory.Iso.Def
import UecInLean.CategoryTheory.Functor.Opposite

namespace UecInLean.CategoryTheory
universe v v' u u'

def Iso.op {C : Type u} [Category.{v} C] {X Y : C} (i : X ≅ Y) : (⟨X⟩ : Cᵒᵖ) ≅ ⟨Y⟩ where
  hom := i.inv
  inv := i.hom
  hom_inv_id := i.hom_inv_id
  inv_hom_id := i.inv_hom_id

def Iso.unop {C : Type u} [Category.{v} C] {X Y : Cᵒᵖ} (i : X ≅ Y) : (X.unop ≅ Y.unop) where
  hom := i.inv
  inv := i.hom
  hom_inv_id := i.hom_inv_id
  inv_hom_id := i.inv_hom_id

def Iso.Functor_Opposite {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D] : (C ⥤ D) ≅ (Cᵒᵖ ⥤ Dᵒᵖ) where
  hom F := F.op
  inv F := F.unop
  hom_inv_id := by simp [Functor.op, Functor.unop]
  inv_hom_id := by {
    funext F
    simp only [Category.Set.comp_def, Category.Set.id_def, id_eq, Functor.op, Functor.unop]
  }

end UecInLean.CategoryTheory
