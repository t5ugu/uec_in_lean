import UecInLean.Category.Basic

namespace UecInLean

universe u u' v v'

structure Iso {C : Type u} [Category.{v} C] (x y : C) where
  hom : x ⟶ y
  inv : y ⟶ x
  hom_inv_id : hom ≫ inv = 𝟙 x := by grind
  inv_hom_id : inv ≫ hom = 𝟙 y := by grind
infix:25 " ≅ " => Iso

attribute [simp, grind =] Iso.hom_inv_id Iso.inv_hom_id

namespace Iso

variable {C : Type u} [Category.{v} C]

@[ext 2000, grind ext]
theorem ext {x y : C} (f g : x ≅ y) (h : f.hom = g.hom) : f = g := by {
  suffices f.inv = g.inv by { cases f; cases g; congr }
  rw [← Category.comp_id f.inv, ← g.hom_inv_id, ← h, ← Category.comp_assoc, f.inv_hom_id, Category.id_comp]
}

def refl (x : C) : x ≅ x where
  hom := 𝟙 x
  inv := 𝟙 x
  hom_inv_id := by rw [Category.id_comp]
  inv_hom_id := by rw [Category.id_comp]

def symm {x y : C} (f : x ≅ y) : y ≅ x where
  hom := f.inv
  inv := f.hom
  hom_inv_id := f.inv_hom_id
  inv_hom_id := f.hom_inv_id

def trans {x y z : C} (f : x ≅ y) (g : y ≅ z) : x ≅ z where
  hom := f.hom ≫ g.hom
  inv := g.inv ≫ f.inv
  hom_inv_id := by rw [Category.comp_assoc, ← Category.comp_assoc g.hom]; grind
  inv_hom_id := by rw [Category.comp_assoc, ← Category.comp_assoc f.inv]; grind
