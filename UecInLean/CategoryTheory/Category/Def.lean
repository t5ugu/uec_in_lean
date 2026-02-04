
namespace UecInLean.CategoryTheory

@[simp, grind =_]
theorem id_refl {α} : (fun x : α => x) = id := rfl

universe v u

class CategoryStruct (C : Type u) where
  hom : C → C → Type v
  id (x : C) : hom x x
  comp {x y z : C} : hom x y → hom y z → hom x z

class Category (C : Type u) extends CategoryStruct.{v} C where
  id_comp {x y : C} (f : hom x y) : comp (id x) f = f := by grind
  comp_id {x y : C} (f : hom x y) : comp f (id y) = f := by grind
  comp_assoc {w x y z : C} (f : hom x y) (g : hom y z) (h : hom z w) :
    comp (comp f g) h = comp f (comp g h) := by grind

infixr:80 " ⟶ " => CategoryStruct.hom
prefix:100 "𝟙 " => CategoryStruct.id
infixr:90 " ≫ " => CategoryStruct.comp

attribute [simp, grind =] Category.id_comp Category.comp_id Category.comp_assoc

def Category.eq_to_hom {C : Type u} [Category.{v} C] {x y : C} (h : x = y) : x ⟶ y := by {
  cases h
  exact 𝟙 x
}

theorem Category.comp_congr_left {C : Type u} [Category.{v} C] {x y z : C}
  {f₁ f₂ : x ⟶ y} (hf : f₁ = f₂) (g : y ⟶ z) :
  f₁ ≫ g = f₂ ≫ g := by {
  rw [hf]
}

theorem Category.comp_congr_right {C : Type u} [Category.{v} C] {x y z : C}
  (f : x ⟶ y) {g₁ g₂ : y ⟶ z} (hg : g₁ = g₂) :
  f ≫ g₁ = f ≫ g₂ := by {
  rw [hg]
}
