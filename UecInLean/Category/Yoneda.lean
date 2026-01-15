import UecInLean.Category.Basic
import UecInLean.Category.Opposite

namespace UecInLean

universe v u

def yoneda (C : Type u) [Category.{v} C] : C ⥤ (Cᵒᵖ ⥤ Type v) := {
  obj a := {
    obj := fun ⟨y⟩ => y ⟶ a
    map f g := f ≫ g
    map_id := by intro ⟨y⟩; simp
    map_comp := by {
      intro ⟨y⟩ ⟨z⟩ ⟨w⟩ f g
      funext h
      simp only [Category.Opposite_hom, Category.Set_comp] at f g h ⊢
      exact Category.comp_assoc g f h
    }
  }
  map f := {
    app _ g := g ≫ f
    naturality := by simp_all
  }
  map_id x := by {
    apply NatTrans.ext
    simp only [Category.comp_id, Category.Fun_id, NatTrans.id_app]
    exact fun _ => rfl
  }
  map_comp f g := by {
    apply NatTrans.ext
    simp
  }
}
