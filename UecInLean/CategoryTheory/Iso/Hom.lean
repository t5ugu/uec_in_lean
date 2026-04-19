import UecInLean.CategoryTheory.Category.Set
import UecInLean.CategoryTheory.Functor.Hom
import UecInLean.CategoryTheory.Functor.toSet
import UecInLean.CategoryTheory.Iso.NaturalIso

namespace UecInLean.CategoryTheory.Iso

universe u v w

open Functor

def Yoneda_lemma {C : Type u} [Category.{max u v} C] (a : C) (P : C ⥤ Type (max u v)) : (Hom a ⟶ P) ≅ P.obj a := {
  hom θ := θ.app a ⟨𝟙 a⟩
  inv x := {
    app s f := (P.map f.down) x
    naturality {s t} f := by {
      funext g
      exact P.toSet_map_comp g.down f x
    }
  }
  hom_inv_id := by {
    funext θ
    simp only [Category.Functor.hom_def]; ext s
    funext f
    have h := congrArg (fun k => k ⟨𝟙 a⟩) (θ.naturality f.down)
    simpa [Hom] using h.symm
  }
  inv_hom_id := by simp
}

theorem comp_Hom_map_app_cancel {C : Type u} [Category.{v} C] {α : Type (max v w)} {a b : C} (F : α → ULift.{w} (b ⟶ a)) (f : a ⟶ b) (g : α)
  : (F ≫ (Hom b).map f) g = ⟨(F g).down ≫ f⟩
:= by simp

theorem Hom_comp_app_id {C : Type u} [Category.{v} C] {α : Type (max v w)} {a b : C} (F : ULift (a ⟶ b) → α) (f : a ⟶ b)
  : ((Hom a).map f ≫ F) ⟨𝟙 a⟩ = F ⟨f⟩
:= by simp

def Hom_inj {C : Type u} [Category.{v} C] {a b : C} (h : Hom a ≅ Hom b) : a ≅ b := {
  hom := h.inv.app b ⟨𝟙 b⟩ |>.down
  inv := h.hom.app a ⟨𝟙 a⟩ |>.down
  hom_inv_id := by {
    have := congrFun (h.symm.naturality (h.hom.app a ⟨𝟙 a⟩).down).symm ⟨𝟙 b⟩
    rw [symm_hom, comp_Hom_map_app_cancel, Hom_comp_app_id, ULift.up_down (h.hom.app a _), ← Category.Set.comp_app (h.hom.app a) (h.inv.app a), h.hom_app_comp_inv_app, Category.Set.id_app] at this
    exact congrArg ULift.down this
  }
  inv_hom_id := by {
    have := congrFun (h.naturality (h.inv.app b ⟨𝟙 b⟩).down).symm ⟨𝟙 a⟩
    rw [comp_Hom_map_app_cancel, Hom_comp_app_id, ULift.up_down (h.inv.app b _), ← Category.Set.comp_app (h.inv.app b) (h.hom.app b), h.inv_app_comp_hom_app, Category.Set.id_app] at this
    exact congrArg ULift.down this
  }
}
