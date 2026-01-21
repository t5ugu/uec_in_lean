import UecInLean.Category.Basic

namespace UecInLean

universe u u' v v'

class IsIso {C : Type u} [Category.{v} C] {x y : C} (f : x ⟶ y) where
  iso : ∃ g : y ⟶ x, (f ≫ g = 𝟙 x) ∧ (g ≫ f = 𝟙 y)

structure Iso {C : Type u} [Category.{v} C] (x y : C) where
  hom : x ⟶ y
  inv : y ⟶ x
  hom_inv_id : hom ≫ inv = 𝟙 x := by grind
  inv_hom_id : inv ≫ hom = 𝟙 y := by grind
infix:25 " ≅ " => Iso
attribute [simp, grind =] Iso.hom_inv_id Iso.inv_hom_id

theorem Iso.isIso {C : Type u} [Category.{v} C] {x y : C} (h : x ≅ y) : IsIso h.hom := ⟨h.inv, h.hom_inv_id, h.inv_hom_id⟩

namespace Iso

variable {C : Type u} [Category.{v} C]

@[ext 2000, grind ext]
theorem ext {x y : C} (f g : x ≅ y) (h : f.hom = g.hom) : f = g := by {
  suffices f.inv = g.inv by {
    obtain ⟨fh, fi, hfhi, hifh⟩ := f
    obtain ⟨gh, gi, hghi, high⟩ := g
    cases this; cases h; congr
  }
  rw [← Category.comp_id f.inv, ← g.hom_inv_id, ← h, ← Category.comp_assoc, f.inv_hom_id, Category.id_comp]
}

def refl (x : C) : x ≅ x := .mk (𝟙 x) (𝟙 x) (by rw [Category.id_comp]) (by rw [Category.id_comp])

def symm {x y : C} (f : x ≅ y) : y ≅ x := .mk f.inv f.hom f.inv_hom_id f.hom_inv_id

def trans {x y z : C} (f : x ≅ y) (g : y ≅ z) : x ≅ z := .mk
  (f.hom ≫ g.hom)
  (g.inv ≫ f.inv)
  (by rw [Category.comp_assoc, ← Category.comp_assoc g.hom, g.hom_inv_id, Category.id_comp, f.hom_inv_id])
  (by rw [Category.comp_assoc, ← Category.comp_assoc f.inv, f.inv_hom_id, Category.id_comp, g.inv_hom_id])

def map {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (F : C ⥤ D) {x y : C} (f : x ≅ y) : F.obj x ≅ F.obj y := by {
  apply Iso.mk (F.map f.hom) (F.map f.inv) _ _
  · rw [← F.map_comp, Iso.hom_inv_id, F.map_id]
  · rw [← F.map_comp, Iso.inv_hom_id, F.map_id]
}

end Iso

end UecInLean
