import UecInLean.CategoryTheory.Universality.Object

namespace UecInLean.CategoryTheory.Limit

universe v u
variable {C : Type u} [Category.{v} C]

/-- 等化子がなす圏。その終対象が等化子。 -/
structure Equalizer {a b : C} (f g : a ⟶ b) where
  pt : C
  fork : pt ⟶ a
  comm : fork ≫ f = fork ≫ g

namespace Equalizer

structure Hom {a b : C} {f g : a ⟶ b}
  (e₁ e₂ : Equalizer f g) where
  hom : e₁.pt ⟶ e₂.pt
  comm : hom ≫ e₂.fork = e₁.fork

instance {a b : C} {f g : a ⟶ b} : Category (Equalizer f g) where
  hom := Equalizer.Hom
  id e := ⟨𝟙 _, by simp⟩
  comp e₁ e₂ := ⟨
    e₁.hom ≫ e₂.hom,
    by rw [Category.comp_assoc, e₂.comm, e₁.comm]
  ⟩
  comp_id := by simp
  id_comp := by simp
  comp_assoc := by simp

def isLimit {a b : C} {f g : a ⟶ b} (e : Equalizer f g) := IsTerminal e

def iso {C : Type u} [Category.{v} C] {a b : C} {f g : a ⟶ b}
  {e₁ e₂ : Equalizer f g} (he₁ : e₁.isLimit) (he₂ : e₂.isLimit) : e₁ ≅ e₂ := IsTerminal.iso he₁ he₂

theorem Hom_eq_iff {a b : C} {f g : a ⟶ b} {p q : Equalizer f g} (h₁ h₂ : Hom p q) :
  h₁ = h₂ ↔ h₁.hom = h₂.hom := by {
  constructor
  · intro h; rw [h]
  · intro h; cases h₁; subst h; rfl
}

end Equalizer

class HasEqualizer (C : Type u) [Category.{v} C] where
  equalizer {a b : C} (f g : a ⟶ b) : Equalizer f g
  isEqualizer {a b : C} (f g : a ⟶ b) : (equalizer f g).isLimit

def Coequalizer {a b : C} (f g : a ⟶ b) := @Equalizer Cᵒᵖ _ ⟨b⟩ ⟨a⟩ f g

namespace Coequalizer

def mk {a b : C} {f g : a ⟶ b} (pt : C) (fork : b ⟶ pt) (comm : f ≫ fork = g ≫ fork) : Coequalizer f g := ⟨⟨pt⟩, fork, comm⟩

instance {a b : C} {f g : a ⟶ b} : Category (Coequalizer f g) := by {
  unfold Coequalizer
  infer_instance
}

def isColimit {a b : C} {f g : a ⟶ b} (e : Coequalizer f g) := IsInitial e

def iso {C : Type u} [Category.{v} C] {a b : C} {f g : a ⟶ b}
  {e₁ e₂ : Coequalizer f g} (he₁ : e₁.isColimit) (he₂ : e₂.isColimit) : e₁ ≅ e₂ := IsInitial.iso he₁ he₂

end Coequalizer

class HasCoequalizer (C : Type u) [Category.{v} C] where
  coequalizer {a b : C} (f g : a ⟶ b) : Coequalizer f g
  isCoequalizer {a b : C} (f g : a ⟶ b) : (coequalizer f g).isColimit
