import UecInLean.CategoryTheory.Iso.Def
import UecInLean.CategoryTheory.Category.Comma
import UecInLean.CategoryTheory.Category.Product
import UecInLean.CategoryTheory.Category.Cat
import UecInLean.CategoryTheory.Functor.Discrete

namespace UecInLean.CategoryTheory.Iso
open CategoryTheory.Category

universe v₀ v₁ v u₀ u₁ u
variable {C₀ : Type u₀} [Category.{v₀} C₀] {C₁ : Type u₁} [Category.{v₁} C₁] {D : Type u} [Category.{v} D]

def Comma_One_iso_Product {F : C₀ ⥤ DiscN 1} {G : C₁ ⥤ DiscN 1} : (⟨F ↓ G, instComma⟩ : Cat) ≅ (⟨C₀ × C₁, instProd⟩) where
  hom := {
    obj X := (X.c₀, X.c₁)
    map := fun ⟨f₀, f₁, _⟩ => (f₀, f₁)
  }
  inv := {
    obj := by {
      intro ⟨x₀, x₁⟩
      exact ⟨x₀, x₁, ⟨⟨by {
        rw [Functor.to_Disc1_obj, Functor.to_Disc1_obj]
      }⟩⟩⟩
    }
    map := by {
      intro ⟨x₀, x₁⟩ ⟨y₀, y₁⟩ ⟨f₀, f₁⟩
      exact ⟨f₀, f₁, by rfl⟩
    }
    map_id _ := by rfl
    map_comp _ _ := by rfl
  }
  hom_inv_id := Functor.eq_id_iff (fun _ => by simp; rfl) (by simp)
  inv_hom_id := Functor.eq_id_iff (fun _ => by simp) (by simp)
