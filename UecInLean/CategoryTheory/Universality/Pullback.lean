import UecInLean.CategoryTheory.Universality.Object

namespace UecInLean.CategoryTheory.Limit

universe v u
variable {C : Type u} [Category.{v} C]

/-- 引き戻し対象がなす圏。その終対象が引き戻し。 ⨯c (`\X c`)-/
structure Pullback {a b c : C} (f : a ⟶ c) (g : b ⟶ c) where
  pt : C
  fst : pt ⟶ a
  snd : pt ⟶ b
  comm : fst ≫ f = snd ≫ g

namespace Pullback

variable {a b c : C} {f : a ⟶ c} {g : b ⟶ c}

structure Hom (p q : Pullback f g) where
  hom : p.pt ⟶ q.pt
  comm_fst : hom ≫ q.fst = p.fst
  comm_snd : hom ≫ q.snd = p.snd

instance : Category (Pullback f g) where
  hom := Pullback.Hom
  id p := ⟨𝟙 _, by simp, by simp⟩
  comp p q := ⟨
    p.hom ≫ q.hom,
    by rw [Category.comp_assoc, q.comm_fst, p.comm_fst],
    by rw [Category.comp_assoc, q.comm_snd, p.comm_snd]
  ⟩
  comp_id := by simp
  id_comp := by simp
  comp_assoc := by simp

def isLimit (p : Pullback f g) := IsTerminal p

def iso {p q : Pullback f g} (hp : p.isLimit) (hq : q.isLimit) : p ≅ q := IsTerminal.iso hp hq

theorem Hom_eq_iff {p q : Pullback f g} (h₁ h₂ : Hom p q) :
  h₁ = h₂ ↔ h₁.hom = h₂.hom := by {
  constructor
  · intro h; rw [h]
  · intro h; cases h₁; subst h; rfl
}

end Pullback

class HasPullback (C : Type u) [Category.{v} C] where
  pullback {a b c : C} (f : a ⟶ c) (g : b ⟶ c) : Pullback f g
  isPullback {a b c : C} (f : a ⟶ c) (g : b ⟶ c) : (pullback f g).isLimit
infixr:1000 " ⨯c " => HasPullback.pullback

/-- 押し出しのなす圏。その始対象が押し出し。 ⨿c (`\coprod c`) -/
def Pushout {a b c : C} (f : c ⟶ a) (g : c ⟶ b) := @Pullback Cᵒᵖ _ ⟨a⟩ ⟨b⟩ ⟨c⟩ f g

namespace Pushout
def mk {a b c : C} {f : c ⟶ a} {g : c ⟶ b} (pt : C) (inl : a ⟶ pt) (inr : b ⟶ pt) (comm : f ≫ inl = g ≫ inr) : Pushout f g :=
  ⟨⟨pt⟩, inl, inr, comm⟩

instance {a b c : C} {f : c ⟶ a} {g : c ⟶ b} : Category (Pushout f g) := by {
  unfold Pushout
  infer_instance
}

def isColimit {a b c : C} {f : c ⟶ a} {g : c ⟶ b} (p : Pushout f g) := IsInitial p

def iso {C : Type u} [Category.{v} C] {a b c : C} {f : c ⟶ a} {g : c ⟶ b}
  {p q : Pushout f g} (hp : p.isColimit) (hq : q.isColimit) : p ≅ q := IsInitial.iso hp hq

end Pushout

class HasPushout (C : Type u) [Category.{v} C] where
  pushout {a b c : C} (f : c ⟶ a) (g : c ⟶ b) : Pushout f g
  isPushout {a b c : C} (f : c ⟶ a) (g : c ⟶ b) : (pushout f g).isColimit
infixr:1000 " ⨿c " => HasPushout.pushout
