import UecInLean.CategoryTheory.Iso.NaturalIso

namespace UecInLean.CategoryTheory
open Iso

universe u u' u'' u''' v v' v'' v'''

structure Equiv (A : Type u) [Category.{v} A] (B : Type u') [Category.{v'} B] where
  fore : A ⥤ B
  back : B ⥤ A
  fore_back_id : fore ⋙ back ≅ Functor.id A
  back_fore_id : back ⋙ fore ≅ Functor.id B
infix:25 " ≃ " => Equiv

def Equiv.refl (A : Type u) [Category.{v} A] : A ≃ A := {
  fore := Functor.id A,
  back := Functor.id A,
  fore_back_id := NaturalIso.id_comp _,
  back_fore_id := NaturalIso.id_comp _
}

def Equiv.symm {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B] (e : A ≃ B) : B ≃ A := {
  fore := e.back,
  back := e.fore,
  fore_back_id := e.back_fore_id,
  back_fore_id := e.fore_back_id
}

def Equiv.trans {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B] {C : Type u''} [Category.{v''} C]
  (e₁ : A ≃ B) (e₂ : B ≃ C) : A ≃ C := {
  fore := e₁.fore ⋙ e₂.fore,
  back := e₂.back ⋙ e₁.back,
  fore_back_id := by {
    apply Iso.trans (NaturalIso.comp_assoc _ _ _)
    apply Iso.trans (NaturalIso.comp_congr_left e₁.fore (by {
      show e₂.fore ⋙ e₂.back ⋙ e₁.back ≅ e₁.back
      apply NaturalIso.comp_congr_right e₂.fore_back_id e₁.back
    }))
    apply e₁.fore_back_id
  }
  back_fore_id := by {
    apply Iso.trans (NaturalIso.comp_assoc _ _ _)
    apply Iso.trans (NaturalIso.comp_congr_left e₂.back (NaturalIso.comp_congr_right e₁.back_fore_id e₂.fore))
    apply e₂.back_fore_id
  }
}
