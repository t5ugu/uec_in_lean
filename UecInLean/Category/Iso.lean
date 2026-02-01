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

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
namespace Iso

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

theorem symm_inv {x y : C} (f : x ≅ y) : f.symm.inv = f.hom := rfl
theorem symm_hom {x y : C} (f : x ≅ y) : f.symm.hom = f.inv := rfl

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

def of_eq {C : Type u} [Category.{v} C] {x y : C} (h : x = y) : x ≅ y := by {
  cases h
  exact refl x
}

theorem comp_hom_inj {w x y : C} (α : x ≅ y) (f g : w ⟶ x) : f ≫ α.hom = g ≫ α.hom ↔ f = g := by {
  constructor
  · intro h
    rw [← Category.comp_id f, ← α.hom_inv_id, ← Category.comp_assoc, h, Category.comp_assoc, α.hom_inv_id, Category.comp_id]
  · intro h
    rw [h]
}

theorem comp_inv_inj {x y z : C} (α : x ≅ y) (f g : z ⟶ y) : f ≫ α.inv = g ≫ α.inv ↔ f = g := by {
  constructor
  · intro h
    rw [← Category.comp_id f, ← α.inv_hom_id, ← Category.comp_assoc, h, Category.comp_assoc, α.inv_hom_id, Category.comp_id]
  · intro h
    rw [h]
}

theorem hom_comp_inj {x y z : C} (α : x ≅ y) (f g : y ⟶ z) : α.hom ≫ f = α.hom ≫ g ↔ f = g := by {
  constructor
  · intro h
    rw [← Category.id_comp f, ← α.inv_hom_id, Category.comp_assoc, h, ← Category.comp_assoc, α.inv_hom_id, Category.id_comp]
  · intro h
    rw [h]
}

theorem inv_comp_inj {w x y : C} (α : x ≅ y) (f g : x ⟶ w) : α.inv ≫ f = α.inv ≫ g ↔ f = g := by {
  constructor
  · intro h
    rw [← Category.id_comp f, ← α.hom_inv_id, Category.comp_assoc, h, ← Category.comp_assoc, α.hom_inv_id, Category.id_comp]
  · intro h
    rw [h]
}

noncomputable def NaturalIso_mk {F G : C ⥤ D} (α : F ⟹ G) (h : ∀ x, IsIso (α.app x)) : F ≅ G := by {
  apply Iso.mk α _ _ _
  {
    rw [Category.Fun_hom]
    exact ⟨by {
      intro x
      exact Classical.choose (h x).iso
    }, by {
      intro x y f
      have ⟨_,hrx⟩ := Classical.choose_spec (h x).iso
      have ⟨hly,_⟩ := Classical.choose_spec (h y).iso
      conv => {
        lhs
        rw [← Category.id_comp (G.map f), ← hrx, Category.comp_assoc _ _ (G.map f), ← α.naturality, Category.comp_assoc, Category.comp_assoc, hly, Category.comp_id]
      }
    }⟩
  }
  {
    rw [Category.Fun_id, Category.Fun_comp]
    apply NatTrans.ext
    intro c
    rw [NatTrans.id_app]
    simp only [eq_mpr_eq_cast, cast_eq, NatTrans.vcomp_app]
    exact (Classical.choose_spec (h c).iso).1
  }
  {
    rw [Category.Fun_id, Category.Fun_comp]
    apply NatTrans.ext
    intro c
    rw [NatTrans.id_app]
    simp only [eq_mpr_eq_cast, cast_eq, NatTrans.vcomp_app]
    exact (Classical.choose_spec (h c).iso).2
  }
}

noncomputable def NaturalIso_mk' {F G : C ⥤ D} (appiso : ∀ x, F.obj x ≅ G.obj x) (naturality : ∀ {x y : C} (f : x ⟶ y), F.map f ≫ (appiso y).hom = (appiso x).hom ≫ G.map f) : F ≅ G := by {
  apply NaturalIso_mk {
    app := by {
      intro x
      exact (appiso x).hom
    }
    naturality := by {
      intro x y f
      exact naturality f
    }
  } (fun _ => Iso.isIso (appiso _))
}

theorem vcomp_hom_inv {F G : C ⥤ D} (α : F ≅ G) : α.hom ≫ α.inv = NatTrans.id F := by {
  obtain ⟨h, i, hi, ih⟩ := α
  simp only [Category.Fun_comp, Category.Fun_hom]
  ext c
  rw [Category.Fun_comp] at hi
  rw [hi, Category.Fun_id]
}

theorem vcomp_inv_hom {F G : C ⥤ D} (α : F ≅ G) : α.inv ≫ α.hom = NatTrans.id G := by {
  obtain ⟨h, i, hi, ih⟩ := α
  simp only [Category.Fun_comp, Category.Fun_hom]
  ext c
  rw [Category.Fun_comp] at ih
  rw [ih, Category.Fun_id]
}

@[simp, grind =]
theorem hom_app_comp_inv_app {F G : C ⥤ D} (α : F ≅ G) (c : C) : α.hom.app c ≫ α.inv.app c = 𝟙 (F.obj c) := by {
  rw [← NatTrans.vcomp_app, ← Category.Fun_comp, vcomp_hom_inv α, NatTrans.id_app]
}

@[simp, grind =]
theorem inv_app_comp_hom_app {F G : C ⥤ D} (α : F ≅ G) (c : C) : α.inv.app c ≫ α.hom.app c = 𝟙 (G.obj c) := by {
  rw [← NatTrans.vcomp_app, ← Category.Fun_comp, vcomp_inv_hom α, NatTrans.id_app]
}

def obj {F G : C ⥤ D} (α : F ≅ G) (c : C) : F.obj c ≅ G.obj c := Iso.mk (α.hom.app c) (α.inv.app c) (by {
  rw [← NatTrans.vcomp_app, ← Category.Fun_comp, vcomp_hom_inv, NatTrans.id_app]
}) (by {
  rw [← NatTrans.vcomp_app, ← Category.Fun_comp, vcomp_inv_hom, NatTrans.id_app]
})

def id_obj (x : C) : (Functor.id C).obj x ≅ x := Iso.mk (𝟙 x) (𝟙 x) (by simp) (by rw [Category.id_comp])

theorem naturality {F G : C ⥤ D} (α : F ≅ G) {x y : C} (f : x ⟶ y) : F.map f ≫ α.hom.app y = α.hom.app x ≫ G.map f := by {
  obtain ⟨h, i, hi, ih⟩ := α
  simp only [NatTrans.naturality]
}

theorem NaturalIso_hom_app_comp_inj {F G : C ⥤ D} (α : F ≅ G) {x y : C} (f g : G.obj x ⟶ G.obj y) : α.hom.app x ≫ f = α.hom.app x ≫ g ↔ f = g := by {
  constructor
  · intro h
    rw [← Category.id_comp f, ← α.inv_app_comp_hom_app, Category.comp_assoc, h, ← Category.comp_assoc, α.inv_app_comp_hom_app, Category.id_comp]
  · intro h
    rw [h]
}

theorem NaturalIso_inv_app_comp_inj {F G : C ⥤ D} (α : F ≅ G) {x y : C} (f g : F.obj x ⟶ F.obj y) : α.inv.app x ≫ f = α.inv.app x ≫ g ↔ f = g := by {
  constructor
  · intro h
    rw [← Category.id_comp f, ← α.hom_app_comp_inv_app, Category.comp_assoc, h, ← Category.comp_assoc, α.hom_app_comp_inv_app, Category.id_comp]
  · intro h
    rw [h]
}

theorem NaturalIso_comp_hom_app_inj {F G : C ⥤ D} (α : F ≅ G) {x y : C} (f g : G.obj y ⟶ F.obj x) : f ≫ α.hom.app x = g ≫ α.hom.app x ↔ f = g := by {
  constructor
  · intro h
    rw [← Category.comp_id f, ← α.symm.inv_app_comp_hom_app, symm_inv, ← Category.comp_assoc, h, Category.comp_assoc, ← α.symm_inv, α.symm.inv_app_comp_hom_app, Category.comp_id]
  · intro h
    rw [h]
}

theorem NaturalIso_comp_inv_app_inj {F G : C ⥤ D} (α : F ≅ G) {x y : C} (f g : F.obj y ⟶ G.obj x) : f ≫ α.inv.app x = g ≫ α.inv.app x ↔ f = g := by {
  constructor
  · intro h
    rw [← Category.comp_id f, ← α.symm.hom_app_comp_inv_app, symm_hom, ← Category.comp_assoc, h, Category.comp_assoc, ← α.symm_hom, α.symm.hom_app_comp_inv_app, Category.comp_id]
  · intro h
    rw [h]
}

theorem NaturalIso_map_left_eq_conj_right {F G : C ⥤ D} (α : F ≅ G) {x y : C} (f : x ⟶ y) : F.map f = α.hom.app x ≫ G.map f ≫ α.inv.app y := by {
  rw [← Category.id_comp (G.map f), ← α.inv_app_comp_hom_app, Category.comp_assoc (α.inv.app x), ← α.naturality, Category.comp_assoc, Category.comp_assoc, α.hom_app_comp_inv_app, Category.comp_id, ← Category.comp_assoc, α.hom_app_comp_inv_app, Category.id_comp]
}

theorem NaturalIso_map_right_eq_conj_left {F G : C ⥤ D} (α : F ≅ G) {x y : C} (f : x ⟶ y) : G.map f = α.inv.app x ≫ F.map f ≫ α.hom.app y := by {
  rw [← Category.comp_id (F.map f), ← α.hom_app_comp_inv_app, ← Category.comp_assoc (F.map f), α.naturality, Category.comp_assoc, Category.comp_assoc, α.inv_app_comp_hom_app, Category.comp_id, ← Category.comp_assoc, α.inv_app_comp_hom_app, Category.id_comp]
}

end Iso
end UecInLean
