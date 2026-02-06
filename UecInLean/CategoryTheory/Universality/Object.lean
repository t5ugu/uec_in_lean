import UecInLean.CategoryTheory.Category.Opposite
import UecInLean.CategoryTheory.Universality.Unique
import UecInLean.CategoryTheory.Iso.Opposite

namespace UecInLean.CategoryTheory

universe u v
variable {C : Type u} [Category.{v} C]

def IsTerminal (u : C) := ∀ v : C, Unique (v ⟶ u)

def IsTerminal.iso {t₁ t₂ : C} (h₁ : IsTerminal t₁) (h₂ : IsTerminal t₂) : t₁ ≅ t₂ := {
  hom := (h₂ t₁).default
  inv := (h₁ t₂).default
  hom_inv_id := (h₁ t₁).allEq _ _
  inv_hom_id := (h₂ t₂).allEq _ _
}

def IsInitial (u : C) := IsTerminal (⟨u⟩ : Cᵒᵖ)
def IsInitial.iso {i₁ i₂ : C} (h₁ : IsInitial i₁) (h₂ : IsInitial i₂) : i₁ ≅ i₂ := (IsTerminal.iso h₁ h₂).unop
