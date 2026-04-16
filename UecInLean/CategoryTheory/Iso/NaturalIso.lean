import UecInLean.CategoryTheory.Category.Functor
import UecInLean.CategoryTheory.Iso.Def
import UecInLean.CategoryTheory.NatTrans.Whiskering

namespace UecInLean.CategoryTheory.Iso

universe u u' u'' u''' v v' v'' v'''
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E] {B : Type u'''} [Category.{v'''} B]

noncomputable def NaturalIso.mk {F G : C ⥤ D} (α : F ⟹ G) (h : ∀ x, IsIso (α.app x)) : F ≅ G := by {
  apply Iso.mk α _ _ _
  {
    rw [Category.Functor.hom_def]
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
    rw [Category.Functor.id_def, Category.Functor.comp_def]
    apply NatTrans.ext
    intro c
    rw [NatTrans.id_app]
    simp only [eq_mpr_eq_cast, cast_eq, NatTrans.vcomp_app]
    exact (Classical.choose_spec (h c).iso).1
  }
  {
    rw [Category.Functor.id_def, Category.Functor.comp_def]
    apply NatTrans.ext
    intro c
    rw [NatTrans.id_app]
    simp only [eq_mpr_eq_cast, cast_eq, NatTrans.vcomp_app]
    exact (Classical.choose_spec (h c).iso).2
  }
}

def NaturalIso.ofComponents {F G : C ⥤ D} (appiso : ∀ x, F.obj x ≅ G.obj x) (naturality : ∀ {x y : C} (f : x ⟶ y), F.map f ≫ (appiso y).hom = (appiso x).hom ≫ G.map f) : F ≅ G := Iso.mk {
  app x := (appiso x).hom, naturality
} ({
  app x := (appiso x).inv, naturality := by {
    intro x y f
    rw [← Category.comp_id (F.map f), ← (appiso y).hom_inv_id, ← Category.comp_assoc (F.map f), naturality f, Category.comp_assoc, ← Category.comp_assoc, (appiso x).inv_hom_id, Category.id_comp]
  }
}) (by {
  apply NatTrans.ext
  intro c
  rw [Category.Functor.id_app, Category.Functor.comp_app, Iso.hom_inv_id]
}) (by {
  apply NatTrans.ext
  intro c
  rw [Category.Functor.id_app, Category.Functor.comp_app, Iso.inv_hom_id]
})

def obj {F G : C ⥤ D} (α : F ≅ G) (c : C) : F.obj c ≅ G.obj c := Iso.mk (α.hom.app c) (α.inv.app c) (by {
  rw [← NatTrans.vcomp_app, ← Category.Functor.comp_def, α.hom_inv_id, Category.Functor.id_def, NatTrans.id_app]
}) (by {
  rw [← NatTrans.vcomp_app, ← Category.Functor.comp_def, α.inv_hom_id, Category.Functor.id_def, NatTrans.id_app]
})

@[simp]
theorem hom_app {F G : C ⥤ D} (α : F ≅ G) (x : C) : α.hom.app x = (α.obj x).hom := rfl
@[simp]
theorem inv_app {F G : C ⥤ D} (α : F ≅ G) (x : C) :  α.inv.app x = (α.obj x).inv := rfl

@[simp, grind =]
theorem hom_app_comp_inv_app {F G : C ⥤ D} (α : F ≅ G) (c : C) : α.hom.app c ≫ α.inv.app c = 𝟙 (F.obj c) := by rw [hom_app, inv_app, (α.obj c).hom_inv_id]

@[simp, grind =]
theorem inv_app_comp_hom_app {F G : C ⥤ D} (α : F ≅ G) (c : C) : α.inv.app c ≫ α.hom.app c = 𝟙 (G.obj c) := by rw [inv_app, hom_app, (α.obj c).inv_hom_id]

def id_obj (x : C) : (Functor.id C).obj x ≅ x := Iso.mk (𝟙 x) (𝟙 x) (by simp) (by rw [Category.id_comp])

theorem naturality {F G : C ⥤ D} (α : F ≅ G) {x y : C} (f : x ⟶ y) : F.map f ≫ α.hom.app y = α.hom.app x ≫ G.map f := by {
  obtain ⟨h, i, hi, ih⟩ := α
  simp only [NatTrans.naturality]
}

def NaturalIso.comp_id (F : C ⥤ D) : F ⋙ Functor.id D ≅ F := {
  hom := {
    app x := 𝟙 (F.obj x),
    naturality := by {
      intro x y f
      rw [Functor.comp_map, Functor.id_map, Category.comp_id (F.map f), Category.id_comp (F.map f)]
    }
  },
  inv := {
    app x := 𝟙 (F.obj x),
    naturality := by {
      intro x y f
      rw [Functor.comp_map, Functor.id_map, Category.comp_id (F.map f), Category.id_comp (F.map f)]
    }
  },
  hom_inv_id := NatTrans.ext (by simp),
  inv_hom_id := NatTrans.ext (by simp)
}

def NaturalIso.id_comp (F : C ⥤ D) : Functor.id C ⋙ F ≅ F := {
  hom := {
    app x := 𝟙 (F.obj x),
    naturality := by {
      intro x y f
      rw [Functor.comp_map, Functor.id_map, Category.comp_id (F.map f), Category.id_comp (F.map f)]
    }
  },
  inv := {
    app x := 𝟙 (F.obj x),
    naturality := by {
      intro x y f
      rw [Functor.comp_map, Functor.id_map, Category.comp_id (F.map f), Category.id_comp (F.map f)]
    }
  },
  hom_inv_id := NatTrans.ext (by simp),
  inv_hom_id := NatTrans.ext (by simp)
}

def NaturalIso.comp_assoc (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ B) : (F ⋙ G) ⋙ H ≅ F ⋙ (G ⋙ H) := {
  hom := {
    app x := 𝟙 ((F ⋙ G ⋙ H).obj x),
    naturality := by simp
  },
  inv := {
    app x := 𝟙 ((F ⋙ G ⋙ H).obj x),
    naturality := by simp
  },
  hom_inv_id := NatTrans.ext (by simp),
  inv_hom_id := NatTrans.ext (by simp)
}

def NaturalIso.comp_congr_right {F₁ F₂ : C ⥤ D} (α : F₁ ≅ F₂) (G : D ⥤ E) : (F₁ ⋙ G) ≅ (F₂ ⋙ G)
:= {
  hom := NatTrans.whiskerLeft α.hom G,
  inv := NatTrans.whiskerLeft α.inv G,
  hom_inv_id := by {
    apply NatTrans.ext
    intro c
    simp only [NatTrans.whiskerLeft, hom_app, inv_app, Category.Functor.comp_def, NatTrans.vcomp_app, Category.Functor.id_def, NatTrans.id_app, Functor.comp_obj]
    rw [← G.map_comp, (α.obj c).hom_inv_id, G.map_id]
  }
  inv_hom_id := by {
    apply NatTrans.ext
    intro c
    simp only [NatTrans.whiskerLeft, hom_app, inv_app, Category.Functor.comp_def, NatTrans.vcomp_app, Category.Functor.id_def, NatTrans.id_app, Functor.comp_obj]
    rw [← G.map_comp, (α.obj c).inv_hom_id, G.map_id]
    }
}

def NaturalIso.comp_congr_left (F : C ⥤ D) {G₁ G₂ : D ⥤ E} (α : G₁ ≅ G₂) : (F ⋙ G₁) ≅ (F ⋙ G₂)
:= {
  hom := NatTrans.whiskerRight F α.hom,
  inv := NatTrans.whiskerRight F α.inv,
  hom_inv_id := by {
    apply NatTrans.ext
    intro c
    simp only [NatTrans.whiskerRight, hom_app, inv_app, Category.Functor.comp_def, NatTrans.vcomp_app, Category.Functor.id_def, NatTrans.id_app, Functor.comp_obj]
    rw [← (α.obj (F.obj c)).hom_inv_id]
  }
  inv_hom_id := by {
    apply NatTrans.ext
    intro c
    simp only [NatTrans.whiskerRight, hom_app, inv_app, Category.Functor.comp_def, NatTrans.vcomp_app, Category.Functor.id_def, NatTrans.id_app, Functor.comp_obj]
    rw [← (α.obj (F.obj c)).inv_hom_id]
  }
}
