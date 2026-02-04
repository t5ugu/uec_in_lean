import UecInLean.CategoryTheory.Category.Functor
import UecInLean.CategoryTheory.Category.Set
import UecInLean.CategoryTheory.Functor.Product
import UecInLean.CategoryTheory.Iso.Def

namespace UecInLean.CategoryTheory.Iso
universe u₀ u₁ u₂ v₀ v₁ v₂

variable {C : Type u₀} [Category.{v₀} C] {D : Type u₁} [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E]

def Product_swap : C × D ≅ D × C where
  hom := fun (x, y) => (y, x)
  inv := fun (y, x) => (x, y)
  hom_inv_id := by simp
  inv_hom_id := by simp

def Product_assoc : (C × D) × E ≅ C × D × E where
  hom := fun ((x, y), z) => (x, y, z)
  inv := fun (x, y, z) => ((x, y), z)
  hom_inv_id := by simp
  inv_hom_id := by simp
