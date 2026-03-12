
namespace UecInLean.CategoryTheory

@[simp, grind =_]
theorem id_refl {α} : (fun x : α => x) = id := rfl

universe v u

class CategoryStruct (C : Type u) where
  hom : C → C → Type v
  id (x : C) : hom x x
  comp {x y z : C} : hom x y → hom y z → hom x z

infixr:80 " ⟶ " => CategoryStruct.hom
prefix:100 "𝟙 " => CategoryStruct.id
infixr:90 " ≫ " => CategoryStruct.comp

class Category (C : Type u) extends CategoryStruct.{v} C where
  id_comp {x y : C} (f : x ⟶ y) : 𝟙 x ≫ f = f
  comp_id {x y : C} (f : x ⟶ y) : f ≫ 𝟙 y = f
  comp_assoc {w x y z : C} (f : x ⟶ y) (g : y ⟶ z) (h : z ⟶ w) :
    (f ≫ g) ≫ h = f ≫ (g ≫ h)

namespace Category

attribute [simp, grind =] id_comp comp_id comp_assoc

def eq_to_hom {C : Type u} [Category.{v} C] {x y : C} (h : x = y) : x ⟶ y := h ▸ 𝟙 x

@[simp, grind =]
theorem eq_to_hom_refl {C : Type u} [Category.{v} C] {x : C} : eq_to_hom (rfl : x = x) = 𝟙 x := by rfl

@[simp]
theorem eq_to_hom_trans {C : Type u} [Category.{v} C] {x y z : C}
  (h₁ : x = y) (h₂ : y = z) :
  eq_to_hom (h₁.trans h₂) = eq_to_hom h₁ ≫ eq_to_hom h₂ := by
  subst h₁; subst h₂; simp

@[simp]
theorem eq_to_hom_comp {C : Type u} [Category.{v} C] {x y z : C}
  (h : x = y) (f : y ⟶ z) :
  eq_to_hom h ≫ f = h ▸ f := by
  cases h; simp [eq_to_hom]

@[simp]
theorem comp_eq_to_hom {C : Type u} [Category.{v} C] {x y z : C}
  (f : x ⟶ y) (h : y = z) :
  f ≫ eq_to_hom h = h ▸ f := by
  cases h; simp [eq_to_hom]

@[grind .]
theorem congr_comp {C : Type u} [Category.{v} C] {x y z : C}
  {f₁ f₂ : x ⟶ y} (hf : f₁ = f₂) {g₁ g₂ : y ⟶ z} (hg : g₁ = g₂) :
  f₁ ≫ g₁ = f₂ ≫ g₂ := by rw [hf, hg]

@[grind .]
theorem congr_comp_left {C : Type u} [Category.{v} C] {x y z : C}
  {f₁ f₂ : x ⟶ y} (hf : f₁ = f₂) (g : y ⟶ z) :
  f₁ ≫ g = f₂ ≫ g := congr_comp hf rfl

@[grind .]
theorem congr_comp_right {C : Type u} [Category.{v} C] {x y z : C}
  (f : x ⟶ y) {g₁ g₂ : y ⟶ z} (hg : g₁ = g₂) :
  f ≫ g₁ = f ≫ g₂ := congr_comp rfl hg
