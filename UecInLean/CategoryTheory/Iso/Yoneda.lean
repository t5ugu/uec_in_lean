import UecInLean.CategoryTheory.Category.Set
import UecInLean.CategoryTheory.Category.Opposite
import UecInLean.CategoryTheory.Iso.NaturalIso

namespace UecInLean.CategoryTheory

universe v u

def hom_co {C : Type u} [Category.{u} C] (A : C) : C ⥤ (Type u) where
  obj B := A ⟶ B
  map f g := g ≫ f
  map_id := by simp
  map_comp := by simp

def yoneda_map {C : Type u} [Category.{u} C] (A : C) (F : C ⥤ Type u) : (hom_co A ⟹ F) ≅ F.obj A where
  hom τ := τ.app A (𝟙 A)
  inv a := {
    app B g := F.map g a
    naturality g := by {
      simp only [hom_co, Category.Set_comp]
      conv => {
        lhs
        intro x
        rw [F.map_comp, Category.Set_comp]
        simp only
      }
    }
  }
  hom_inv_id := by {
    funext τ; ext a; funext g
    have := funext_iff.mp (τ.naturality g) (𝟙 A)
    simp only [hom_co, Category.Set_comp, Category.id_comp] at this
    exact this.symm
  }
  inv_hom_id := by simp

def yoneda_embedding {C : Type u} [Category.{u} C] {A B : C} : (hom_co A ⟹ hom_co B) ≅ ((⟨A⟩ : Cᵒᵖ) ⟶ ⟨B⟩) := Iso.trans (yoneda_map A (hom_co B)) (Iso.of_eq rfl)
