import UecInLean.CategoryTheory.Category.Def
import UecInLean.CategoryTheory.Universality.Unique
import UecInLean.CategoryTheory.Iso.Def

namespace UecInLean.CategoryTheory.Limit

universe v u
variable {C : Type u} [Category.{v} C]

structure Product (a b : C) where
  u : C
  p₀ : u ⟶ a
  p₁ : u ⟶ b

structure Product.Hom {a b : C} (p q : Product a b) where
  f : p.u ⟶ q.u
  comm₀ : f ≫ q.p₀ = p.p₀
  comm₁ : f ≫ q.p₁ = p.p₁

instance {a b : C} : Category (Product a b) where
  hom := Product.Hom
  id p := ⟨𝟙 _, by simp, by simp⟩
  comp f g := ⟨
    f.f ≫ g.f,
    by rw [Category.comp_assoc, g.comm₀, f.comm₀],
    by rw [Category.comp_assoc, g.comm₁, f.comm₁]
  ⟩
  comp_id _ := by simp
  id_comp _ := by simp
  comp_assoc _ _ _ := by simp

def IsProduct {a b : C} (p : Product a b) := ∀ (v : C) (q₀ : v ⟶ a) (q₁ : v ⟶ b), ∃! h : v ⟶ p.u, q₀ = h ≫ p.p₀ ∧ q₁ = h ≫ p.p₁
