import UecInLean.CategoryTheory.Universality.Object

namespace UecInLean.CategoryTheory.Limit

universe v u u'
variable {C : Type u} [Category.{v} C]

/-- 直積対象の候補がなす圏。その終対称が直積。 ⨯ (`\X`) -/
structure Product (a b : C) where
  pt : C
  fst : pt ⟶ a
  snd : pt ⟶ b

namespace Product

structure Hom {a b : C} (p q : Product a b) where
  hom : p.pt ⟶ q.pt
  comm₀ : hom ≫ q.fst = p.fst
  comm₁ : hom ≫ q.snd = p.snd

instance {a b : C} : Category (Product a b) where
  hom := Product.Hom
  id p := ⟨𝟙 _, by simp, by simp⟩
  comp f g := ⟨
    f.hom ≫ g.hom,
    by rw [Category.comp_assoc, g.comm₀, f.comm₀],
    by rw [Category.comp_assoc, g.comm₁, f.comm₁]
  ⟩
  comp_id := by simp
  id_comp := by simp
  comp_assoc := by simp

theorem id_def {a b : C} (p : Product a b) : 𝟙 p = ⟨𝟙 _, by simp, by simp⟩ := rfl
theorem id_hom_eq {a b : C} (p : Product a b) : (𝟙 p).hom = 𝟙 p.pt := rfl
theorem comp_def {a b : C} {p q r : Product a b} (f : p ⟶ q) (g : q ⟶ r) : (f ≫ g) = ⟨
    f.hom ≫ g.hom,
    by rw [Category.comp_assoc, g.comm₀, f.comm₀],
    by rw [Category.comp_assoc, g.comm₁, f.comm₁]
  ⟩ := rfl
theorem comp_hom_eq {a b : C} {p q r : Product a b} (f : p ⟶ q) (g : q ⟶ r) : (f ≫ g).hom = f.hom ≫ g.hom := rfl

def isLimit {a b : C} (p : Product a b) := IsTerminal p

def iso {C : Type u} [Category.{v} C] {a b : C} {p q : Product a b} (hp : p.isLimit) (hq : q.isLimit) : p ≅ q := IsTerminal.iso hp hq

theorem Hom_eq_iff {a b : C} {p q : Product a b} (h₁ h₂ : Hom p q) :
  h₁ = h₂ ↔ h₁.hom = h₂.hom := by {
  constructor
  · intro h; rw [h]
  · intro h; cases h₁; subst h; rfl
}

end Product

class HasProduct (C : Type u) [Category.{v} C] where
  prod (a b : C) : Product a b
  isProd (a b : C) : (prod a b).isLimit
infixr:1000 " ⨯ " => HasProduct.prod

def Product.universality {C : Type u} [Category.{v} C] [HasProduct C] {a b : C} (q : Product a b) : Unique (q ⟶ a ⨯ b) :=
  HasProduct.isProd a b q

def Product.univHom {C : Type u} [Category.{v} C] [HasProduct C] {a b : C} (q : Product a b) : q ⟶ a ⨯ b := q.universality.default

theorem Product.univHom_self_eq_id {C : Type u} [Category.{v} C] [HasProduct C] {a b : C} :
  (a ⨯ b).univHom = 𝟙 (a ⨯ b) := by {
  apply (a ⨯ b).universality.allEq
}

/-- 余直積対象のなす圏。その始対象が余直積。 ⨿ (`\coprod`) -/
def Coproduct (a b : C) := Product (⟨a⟩ : Cᵒᵖ) (⟨b⟩ : Cᵒᵖ)

namespace Coproduct

def mk {a b : C} (p : C) (inl : a ⟶ p) (inr : b ⟶ p) : Coproduct a b := ⟨⟨p⟩, inl, inr⟩

instance {a b : C} : Category (Coproduct a b) := by {
  unfold Coproduct
  infer_instance
}

def isColimit {a b : C} (p : Coproduct a b) := IsInitial p

def iso {C : Type u} [Category.{v} C] {a b : C} {p q : Coproduct a b} (hp : p.isColimit) (hq : q.isColimit) : p ≅ q := IsInitial.iso hp hq

end Coproduct

class HasCoproduct (C : Type u) [Category.{v} C] where
  coprod (a b : C) : Coproduct a b
  isCoprod (a b : C) : (coprod a b).isColimit
infixr:1000 " ⨿ " => HasCoproduct.coprod

structure Pi {J : Type u'} (a : J → C) where
  pt : C
  proj (j : J) : pt ⟶ a j

namespace Pi

structure Hom {J : Type u'} {a : J → C} (p q : Pi a) where
  hom : p.pt ⟶ q.pt
  comm (j : J) : hom ≫ q.proj j = p.proj j

instance {J : Type u'} {a : J → C} : Category (Pi a) where
  hom := Pi.Hom
  id p := ⟨𝟙 _, by simp⟩
  comp f g := ⟨
    f.hom ≫ g.hom,
    fun j => by rw [Category.comp_assoc, g.comm j, f.comm j]
  ⟩
  comp_id := by simp
  id_comp := by simp
  comp_assoc := by simp

def isLimit {J : Type u'} {a : J → C} (p : Pi a) := IsTerminal p

def iso {C : Type u} [Category.{v} C] {J : Type u'} {a : J → C} {p q : Pi a} (hp : p.isLimit) (hq : q.isLimit) : p ≅ q := IsTerminal.iso hp hq

end Pi

class HasPi (C : Type u) [Category.{v} C] where
  pi {J : Type u'} (a : J → C) : Pi a
  isPi {J : Type u'} (a : J → C) : (pi a).isLimit
notation "∏ " => HasPi.pi
