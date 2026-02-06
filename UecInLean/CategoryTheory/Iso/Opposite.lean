import UecInLean.CategoryTheory.Category.Opposite
import UecInLean.CategoryTheory.Category.Functor
import UecInLean.CategoryTheory.Category.Set
import UecInLean.CategoryTheory.Iso.Def

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
  hom F := {
    obj := fun ⟨x⟩ => ⟨F.obj x⟩
    map := fun f => F.map f
    map_id := fun x => F.map_id x.unop
    map_comp := fun f g => F.map_comp g f
  }
  inv F := {
    obj x := (F.obj ⟨x⟩).unop
    map f := F.map f
    map_id x := F.map_id ⟨x⟩
    map_comp f g := F.map_comp g f
  }
  hom_inv_id := by simp
  inv_hom_id := by {
    funext F
    simp only [Category.Set.comp_def, Category.Set.id_def, id_eq]
  }

end UecInLean.CategoryTheory
