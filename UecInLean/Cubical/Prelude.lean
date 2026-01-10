import Aesop

class BoundedDistributiveLattice (I : Type) where
  bot : I
  top : I

  meet : I → I → I -- ⊓
  meet_comm : ∀ x y, meet x y = meet y x
  meet_assoc : ∀ x y z, meet (meet x y) z = meet x (meet y z)
  meet_bot : ∀ x, meet x bot = bot
  meet_top : ∀ x, meet x top = x

  join : I → I → I -- ⊔
  join_comm : ∀ x y, join x y = join y x
  join_assoc : ∀ x y z, join (join x y) z = join x (join y z)
  join_eq_top : ∀ x y, join x y = top → x = top ∨ y = top

  meet_join_distr : ∀ x y z, meet x (join y z) = join (meet x y) (meet x z)
  join_meet_distr : ∀ x y z, join x (meet y z) = meet (join x y) (join x z)

  meet_join_cancel : ∀ x y, meet x (join x y) = x
  join_meet_cancel : ∀ x y, join x (meet x y) = x

namespace BoundedDistributiveLattice
attribute [simp] meet_comm meet_assoc meet_bot meet_top join_comm join_assoc join_eq_top meet_join_distr join_meet_distr meet_join_cancel join_meet_cancel

variable {I : Type} [BoundedDistributiveLattice I]

instance : OfNat I 0 := ⟨bot⟩
instance : OfNat I 1 := ⟨top⟩

infixr:70 " ⊓ " => meet
infixr:70 " ⊔ " => join

@[simp] theorem meet_zero (x : I) : x ⊓ 0 = 0 := meet_bot x
@[simp] theorem zero_meet (x : I) : 0 ⊓ x = 0 := by rw [meet_comm, meet_zero x]
@[simp] theorem meet_one (x : I) : x ⊓ 1 = x := meet_top x
@[simp] theorem one_meet (x : I) : 1 ⊓ x = x := by rw [meet_comm, meet_one x]
@[simp] theorem join_zero (x : I) : x ⊔ 0 = x := by rw [← meet_zero x, join_meet_cancel]
@[simp] theorem zero_join (x : I) : 0 ⊔ x = x := by rw [join_comm, join_zero x]
@[simp] theorem join_one (x : I) : x ⊔ 1 = 1 := by rw [← meet_one x, join_comm, meet_comm, join_meet_cancel]
@[simp] theorem one_join (x : I) : 1 ⊔ x = 1 := by rw [join_comm, join_one x]
theorem join_eq_one (x y : I) : join x y = 1 → x = 1 ∨ y = 1 := join_eq_top x y

end BoundedDistributiveLattice

class DeMorganAlgebra (I : Type) extends BoundedDistributiveLattice I where
  symm : I → I -- ~
  symm_symm : ∀ x, symm (symm x) = x
  symm_meet : ∀ x y, symm (meet x y) = join (symm x) (symm y)

namespace DeMorganAlgebra
attribute [simp] symm_symm symm_meet
open BoundedDistributiveLattice

variable {I : Type} [DeMorganAlgebra I]

prefix:75 "~" => symm

@[simp] theorem symm_join (x y : I) : ~(x ⊔ y) = ~x ⊓ ~y := by
  rw [← symm_symm (~x ⊓ ~y), symm_meet, symm_symm, symm_symm]
@[simp] theorem symm_inj {x y : I} : ~x = ~y ↔ x = y := by
  constructor
  · intro h; rw [← symm_symm x, h, symm_symm]
  · intro h; rw [h]
@[simp] theorem symm_one : ~(1 : I) = 0 := by
  rw [← join_zero (~1), ← symm_symm 0, ← symm_meet, one_meet]
@[simp] theorem symm_zero : ~(0 : I) = 1 := by
  rw [← meet_one (~0), ← symm_symm 1, ← symm_join, zero_join]
end DeMorganAlgebra

universe u v

instance : DeMorganAlgebra Bool where
  bot := false
  top := true
  meet := Bool.and
  meet_comm := Bool.and_comm
  meet_assoc := Bool.and_assoc
  meet_bot := fun x => by cases x <;> rfl
  meet_top := fun x => by cases x <;> rfl
  join := Bool.or
  join_comm := Bool.or_comm
  join_assoc := Bool.or_assoc
  join_eq_top x y := (Bool.or_eq_true x y).mp
  meet_join_distr := fun x y z => by cases x <;> rfl
  join_meet_distr := fun x y z => by cases x <;> rfl
  meet_join_cancel := fun x y => by cases x <;> rfl
  join_meet_cancel := fun x y => by cases x <;> rfl
  symm := Bool.not
  symm_symm := Bool.not_not
  symm_meet := Bool.not_and

abbrev I := Bool

inductive IsOne : I → Prop
  | itIs : IsOne 1
  | max_left (i j : I) : IsOne i → IsOne (i ⊔ j)
  | max_right (i j : I) : IsOne j → IsOne (i ⊔ j)

def 𝔽 := { i : I // IsOne i }

def Partial (i : I) (A : Type u) := IsOne i → A

inductive PartialP : (i : I) → (Partial i (Type u)) → Prop
  | isOneEmpty {A : Partial 0 (Type u)} : PartialP 0 A
  | or (i j : I) {A : Partial (i ⊔ j) (Type u)} : (PartialP i (fun z => A (IsOne.max_left i j z))) → (PartialP j (fun z => A (IsOne.max_right i j z))) → PartialP (i ⊔ j) A

axiom transp (A : I → Type u) (φ : I) (a : A 0) : A 1

def hcomp {A : Type u} (φ : I) (u : I → Partial φ A) (a : A) : A := by {
  cases φ
  exact a
  exact u 1 .itIs
}

noncomputable def comp (A : I → Type u) (φ : I) (_u : ∀ i, Partial φ (A i)) (a : A 0) : A 1 := transp A φ a

-- ^ Agda.Primitive.Cubical
-- v Agda.Builtin.Cubical.Sub

inductive Sub' : (A : Type u) → (φ : I) → Partial φ A → Type u
  | inS {A : Type u} {φ : I} (x : A) : Sub' A φ (fun _ => x)
notation A "[ " φ " ↦ " u " ]" => Sub' A φ u

def inS {A : Type u} {φ : I} (u : A) : A [ φ ↦ (fun _ => u) ] := Sub'.inS u

def outS {A : Type u} {φ : I} {u : Partial φ A} : Sub' A φ u → A
  | ⟨x⟩ => x

theorem outS_inS {A : Type u} {φ : I} (a : A) : outS (@inS _ φ a) = a := by rfl
theorem outS_one {A : Type u} {u} (h : Sub' A 1 u) : outS h = u .itIs := by cases h; rfl

-- ^ Agda.Builtin.Cubical.Sub

structure PathP (A : I → Type u) (a : A 0) (b : A 1) where
  app : (i : I) → A i
  app_zero : app 0 = a := by aesop
  app_one : app 1 = b := by aesop
attribute [simp] PathP.app_zero PathP.app_one

@[ext, aesop safe]
def PathP.ext {A : I → Type u} {a : A 0} {b : A 1} (p q : PathP A a b) (h₀ : p.app 0 = q.app 0) (h₁ : p.app 1 = q.app 1) : p = q := by {
  cases p; cases q; congr; funext i;
  cases i
  · exact h₀
  · exact h₁
}

def PathP.hext {A : I → Type u} {a a' : A 0} {b b' : A 1} (p : PathP A a b) (q : PathP A a' b') (ha : a = a') (hb : b = b') (h : ∀ i, p.app i = q.app i) : p ≍ q := by {
  cases p; cases q; cases ha; cases hb; congr; funext i; exact h i
}

def Path (A : Type u) (a b : A) := PathP (fun _ => A) a b
notation a " ≡ " b => Path _ a b

def refl {A : Type u} {a : A} : a ≡ a := .mk (fun _ => a)

-- v Agda.Builtin.Cubical.HCompU

def hfill {A : Type u} {φ : I} (u : I → Partial φ A) (u0 : A [ φ ↦ u 0 ]) (i : I) : A
:= hcomp φ (by {
  intro j k
  cases φ
  · cases i
    · exact outS u0
    · exact u 0 k
  · exact u (i ⊓ j) IsOne.itIs
}) (outS u0)

def isContr (A : Type u) := Σ (x : A), ∀ y, x ≡ y

def fiber {A : Type u} {B : Type v} (f : A → B) (y : B) := Σ x, f x ≡ y

def transpProof {e : I → Type u} (φ : I) (a : Partial φ (e 0)) (b : (e 1) [ φ ↦ (fun o => transp e 0 (a o))]) : fiber (transp e 0) (outS b) := by {

}
where
  b' := @outS _ _ (fun o => transp e 0 (a o)) b
  f : e 0 := @comp (fun i => e (~i)) φ (fun i => by {
    cases φ
    {
      exact transp (fun j => e (~j ∨ ~i)) (~i) b'
    }
    {
      exact transp (fun j => e (j ∧ ~i)) i (a .itIs)
    }
  }) b'

def truePath : true ≡ true := refl

def notK (b : Bool) : (not (not b)) ≡ b := .mk (fun _ => b)

def cong {A B : Type u} (f : A → B) {a b : A} (p : a ≡ b) : f a ≡ f b := .mk (fun i => f (p.app i))

def congbin (A B C : Type u) (f : A → B → C) (a a' : A) (b b' : B) (p : a ≡ a') (q : b ≡ b') : f a b ≡ f a' b'
  := .mk (fun i => f (p.app i) (q.app i))

def funExt (A B : Type u) (f g : A → B) (p : (x : A) → f x ≡ g x) : f ≡ g := .mk (fun i a => (p a).app i)

def funExtDep (A : Type u) (B : A → Type u) (f g : (x : A) → B x) (p : (x : A) → f x ≡ g x) : f ≡ g := .mk (fun i a => (p a).app i)

def funExt2 (A B C : Type u) (f g : A → B → C) (p : (x : A) → (y : B) → f x y ≡ g x y) : f ≡ g := .mk (fun i a b => (p a b).app i)

def notK' : (not ∘ not) ≡ id := .mk (fun i b => (notK b).app i)

def contrSingl (A : Type u) (a b : A) (p : Path A a b) : Path ((x : A) × (Path A a x)) ⟨a, refl⟩ ⟨b, p⟩
:= {
  app i := ⟨p.app i, .mk fun j => p.app (i ⊓ j)⟩,
  app_zero := by {
    ext
    · simp only [p.app_zero]
    · apply PathP.hext _ _ rfl p.app_zero
      simp only [DeMorganAlgebra.zero_meet, p.app_zero, refl, implies_true]
  },
  app_one := by {
    ext
    · simp only [p.app_one]
    · apply PathP.hext _ _ rfl p.app_one
      simp only [DeMorganAlgebra.one_meet, implies_true]
  }
}

def Square {A : Type u} {x0 x1 y0 y1 : A} (p: x0 ≡ x1) (q : y0 ≡ y1) (r : x0 ≡ y0) (s : x1 ≡ y1) := PathP (λ i => p.app i ≡ q.app i) (by {
  simp only [p.app_zero, q.app_zero]
  exact r
}) (by {
  simp only [p.app_one, q.app_one]
  exact s
})

def sym {A : Type u} {a b : A} (p : a ≡ b) : b ≡ a := .mk fun i => p.app (~i)

def symInv {A : Type u} {a b : A} (p : a ≡ b) : sym (sym p) ≡ p := {
  app := fun i => p,
  app_zero := by {
    apply PathP.ext <;> rfl
  },
  app_one := by rfl
}

def congId (A : Type u) (a b : A) (p : a ≡ b) : cong id p ≡ p := refl

def congComp (A B C : Type u) (f : B → C) (g : A → B) {a b : A} (p : a ≡ b) : cong (f ∘ g) p ≡ cong f (cong g p) := refl

noncomputable def transport {A B : Type u} (p : A ≡ B) (a : A) : B := by {
  rw [← p.app_one]
  rw [← p.app_zero] at a
  apply transp (fun i => p.app i) 0 a
}
