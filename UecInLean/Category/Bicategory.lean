import UecInLean.Category.Basic
import UecInLean.Category.Prod
import UecInLean.Category.Iso

namespace UecInLean

universe w v u

class Bicategory (B : Type u) [Category.{v} B] where
  homCategory : ∀ a b : B, Category.{w} (a ⟶ b)
  M (a b c : B) : (a ⟶ b) × (b ⟶ c) ⥤ (a ⟶ c)

  associator {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : f ≫ (g ≫ h) ≅ (f ≫ g) ≫ h
  leftUnitor {a b : B} (f : a ⟶ b) : (Category.id a) ≫ f ≅ f
  rightUnitor {a b : B} (f : a ⟶ b) : f ≫ (Category.id b) ≅ f
end UecInLean
