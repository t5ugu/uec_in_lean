import UecInLean.CategoryTheory.Category.Opposite
import UecInLean.CategoryTheory.Category.Functor
import UecInLean.CategoryTheory.Category.Set
import UecInLean.CategoryTheory.Iso.Def

namespace UecInLean.CategoryTheory
universe v v' u u'

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
    simp only [Category.Set_comp, Category.Set_id, id_eq]
  }

end UecInLean.CategoryTheory
