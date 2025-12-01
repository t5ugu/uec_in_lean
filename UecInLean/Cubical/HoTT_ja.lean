import Mathlib.Tactic.Use

-- https://uemurax.github.io/pdfs/hott-intro-ja.pdf

universe u v
variable {A : Type u}

inductive Path : A → A → Type u
  | refl (x : A) : Path x x
infix:50 " ≡ " => Path

def Path.of_eq {x y : A} : x = y → x ≡ y
  | Eq.refl _ => Path.refl _

def refl (x : A) : x ≡ x := Path.refl x

def Path.symm {x y : A} : x ≡ y → y ≡ x
  | Path.refl _ => Path.refl _
postfix:100 "⁻¹ " => Path.symm

def Path.trans {x y z : A} : x ≡ y → y ≡ z → x ≡ z
  | Path.refl _, q => q
infixr:90 " • " => Path.trans

def trans_refl {x y : A} (p : x ≡ y) : p • refl y ≡ p := by {
  cases p
  exact .refl _
}

def refl_trans {x y : A} (p : x ≡ y) : refl x • p ≡ p := by {
  cases p
  exact .refl _
}

def symm_trans {x y : A} (p : x ≡ y) : p⁻¹ • p ≡ refl y := by {
  cases p
  exact .refl _
}

def trans_symm {x y : A} (p : x ≡ y) : p • p⁻¹ ≡ refl x := by {
  cases p
  exact .refl _
}

def symm_symm {x y : A} (p : x ≡ y) : p⁻¹⁻¹ ≡ p := by {
  cases p
  exact .refl _
}

def trans_assoc {w x y z : A} (p : w ≡ x) (q : x ≡ y) (r : y ≡ z) : (p • q) • r ≡ p • q • r := by {
  cases p
  exact .refl _
}

def ap {B : Type v} {x y : A} (f : A → B) : x ≡ y → f x ≡ f y
  | Path.refl _ => Path.refl _

def ap_refl {x : A} (f : A → A) : ap f (refl x) ≡ refl (f x) := .refl _

def ap_trans {B : Type v} {x y z : A} (f : A → B) (p : x ≡ y) (q : y ≡ z) : ap f (p • q) = (ap f p) • (ap f q) := by {
  cases p
  exact .refl _
}

def ap_symm {B : Type v} {x y : A} (f : A → B) (p : x ≡ y) : ap f (p⁻¹) ≡ (ap f p)⁻¹ := by {
  cases p
  exact .refl _
}

def transport (C : A → Type u) {x y : A} : x ≡ y → C x → C y
  | .refl _, u => u

def transport_refl (C : A → Type u) {x : A} : transport C (refl x) ≡ id := .refl _

def lift {C : A → Type u} {x y : A} (u : C x) (p : x ≡ y) : (⟨x, u⟩ : (x:A) × C x) ≡ ⟨y, transport C p u⟩ := by {
  cases p
  exact .refl _
}

def IsFibration {E : Type u} {B : Type v} (P : E → B)
  := ∀ (X : E) {J : B} (f : P X ≡ J), ∃ X', (h : P X' = J) → ∃ f' : X ≡ X', ap P f' = (by cases h; exact f)

example {C : A → Type u} : IsFibration (@Sigma.fst A (fun x => C x)) := by {
  intro ⟨x, u⟩ y p
  use ⟨y, transport C p u⟩
  intro h
  use lift u p
  cases p
  rfl
}

def Homotopy {B : Type v} (f g : A → B) := ∀ x : A, f x = g x
infixr:50 " ~ " => Homotopy

def Homotopy.symm {B : Type v} {f g : A → B} (p : f ~ g) : g ~ f := by {
  intro x
  exact (p x).symm
}

def Homotopy.trans {B : Type v} {f g h : A → B} (p : f ~ g) (q : g ~ h) : f ~ h := by {
  intro x
  exact (p x).trans (q x)
}

def Homotopy.comp_right {B X : Type v} {f g : A → B} (p : f ~ g) (h : X → A) : (f ∘ h) ~ (g ∘ h) := by {
  intro x
  congr
  funext y
  exact p y
}

def Homotopy.comp_left {B C : Type v} {f g : A → B} (p : f ~ g) (h : B → C) : (h ∘ f) ~ (h ∘ g) := by {
  intro x
  simp [p x]
}

variable {B : Type u}

structure IsEquiv (f : A → B) where
  linv : (g : B → A) ×' (g ∘ f ~ id)
  rinv : (h : B → A) ×' (f ∘ h ~ id)
attribute [ext] IsEquiv

structure Equiv (A B : Type u) : Type (u + 1) where
  f : A → B
  eqv : IsEquiv f
infixr:50 " ≃ " => Equiv
attribute [ext] Equiv

def equivalence (f : A → B) := Inhabited (IsEquiv f)
def equivalent (A B : Type u) := Inhabited (A ≃ B)

def idEquiv (A : Type u) : A ≃ A := ⟨id, ⟨id, fun _ => .refl _⟩, ⟨id, fun _ => .refl _⟩⟩

def idToEquiv (A B : Type u) : A ≡ B → A ≃ B
  | .refl _ => idEquiv A

axiom univalence.{w} (A B : Type w) : IsEquiv (idToEquiv A B)

noncomputable def equiv_equiv_eq : (A ≡ B) ≃ (A ≃ B) := {
  f := idToEquiv A B,
  eqv := univalence A B
}

inductive DependentPath (B : A → Type u) {x y : A} (p : x ≡ y) (u : B x) : B y → Type u
  | transport (v : B y) : DependentPath B p u v

notation u " ≡[" B "," p "] " v => DependentPath B p u v
