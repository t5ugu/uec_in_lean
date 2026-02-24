import UecInLean.CategoryTheory.Category.Opposite
import UecInLean.CategoryTheory.Category.Product
import UecInLean.CategoryTheory.Category.Set
import UecInLean.CategoryTheory.Category.Functor
import UecInLean.CategoryTheory.Iso.Hom

namespace UecInLean.CategoryTheory.Functor
universe u

def Yoneda {C : Type u} [Category.{u} C] : C ⥤ (Cᵒᵖ ⥤ Type u) where
  obj a := Hom ⟨a⟩
  map f := {
    app s g := f ≫ g
    naturality := by simp [Hom]
  }
  map_id := fun _ => NatTrans.ext (by simp)
  map_comp := fun _ _ => NatTrans.ext (by simp)
