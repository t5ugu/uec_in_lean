import UecInLean.CategoryTheory.Category.Set
import UecInLean.CategoryTheory.Functor.Hom
import UecInLean.CategoryTheory.Functor.toSet
import UecInLean.CategoryTheory.Iso.NaturalIso

namespace UecInLean.CategoryTheory.Iso

universe u v

open Functor

def Yoneda_lemma {C : Type u} [Category.{max u v} C] (a : C) (P : C ⥤ Type (max u v)) : (Hom a ⟶ P) ≅ P.obj a := {
  hom θ := θ.app a (𝟙 a)
  inv x := {
    app s f := (P.map f) x
    naturality {s t} f := by {
      funext g
      exact Functor.toSet_map_comp P g f x
    }
  }
  hom_inv_id := by {
    funext θ
    apply NatTrans.ext
    intro s
    funext f
    have h := congrArg (fun k => k (𝟙 a)) (θ.naturality f)
    simpa [Hom] using h.symm
  }
}

def Hom_inj {C : Type u} [Category.{v} C] {a b : C} (h : Hom a ≅ Hom b) : a ≅ b := {
  hom := h.inv.app b (𝟙 b)
  inv := h.hom.app a (𝟙 a)
  hom_inv_id := by {
    have := congrFun (h.symm.naturality (h.hom.app a (𝟙 a))).symm (𝟙 b)
    simp only [Category.Set.comp_app, Hom.map_def, Category.id_comp, symm_hom] at this
    rw [this, ← Category.Set.comp_app (h.hom.app a) (h.inv.app a), h.hom_app_comp_inv_app, Category.Set.id_app]
  }
  inv_hom_id := by {
    have := congrFun (h.naturality (h.inv.app b (𝟙 b))).symm (𝟙 a)
    simp only [Category.Set.comp_app, Hom.map_def, Category.id_comp] at this
    rw [this, ← Category.Set.comp_app (h.inv.app b) (h.hom.app b), h.inv_app_comp_hom_app, Category.Set.id_app]
  }
}
