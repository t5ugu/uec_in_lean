import Init.WF

namespace UecInLean.TaPL

class Derivable (T : Type) where
  derivable : T -> T -> Prop
infix:100 " ⟶ " => Derivable.derivable

section NormalForm

variable {T : Type} [Derivable T]

def isNormalForm (t : T) := ∀ t', ¬ t ⟶ t'

/-- 定義 3.5.6 -/
theorem isNormalForm_iff (t : T) : isNormalForm t ↔ ¬ ∃ t', t ⟶ t' := by rw [isNormalForm, not_exists]

theorem isNormalForm_not_iff (t : T) : ¬ isNormalForm t ↔ ∃ t', t ⟶ t' := by simp only [isNormalForm, Classical.not_forall, Classical.not_not]

theorem contra_of_isNormalForm_of_deriv {t t' : T} (h : isNormalForm t) (h' : t ⟶ t') : False := h t' h'

theorem isNormalForm_of_pre {τ : T -> T} (hτ : ∀ {s s'}, s ⟶ s' -> τ s ⟶ τ s') {t : T} (ht : isNormalForm (τ t)) : isNormalForm t := by {
  intro t' h
  exact ht (τ t') (hτ h)
}

end NormalForm

class HasValue (T : Type) where
  isValue : T -> Prop

section MultiStepDeriv

/-- 定義 3.5.9 -/
inductive MultiStepDeriv {T : Type} [Derivable T] (t : T) : T -> Prop
  | refl : MultiStepDeriv t t
  | step {t' t''} : t'' ⟶ t' -> MultiStepDeriv t t' -> MultiStepDeriv t t''
notation:100 a:100 " ⟶* " b:100 => MultiStepDeriv b a

variable {T : Type} [Derivable T]

theorem MultiStepDeriv.lift {t t' : T} (h : t ⟶ t') : t ⟶* t' := .step h .refl

instance {t t' : T} : Coe (t ⟶ t') (t ⟶* t') := ⟨MultiStepDeriv.lift⟩

theorem MultiStepDeriv.append {t t' t'' : T} (h : t ⟶* t') (h' : t' ⟶* t'') : t ⟶* t'' := by {
  induction h with
  | refl => exact h'
  | step h hs ih => exact .step h ih
}

theorem MultiStepDeriv.two {t t' t'' : T} (h : t ⟶ t') (h' : t' ⟶ t'') : t ⟶* t'' := by {
  exact MultiStepDeriv.append (.lift h) (.lift h')
}

theorem MultiStepDeriv.inherit {τ : T -> T} (hτ : ∀ {s s'}, s ⟶ s' -> τ s ⟶ τ s') : ∀ {t₁ t₁'}, t₁ ⟶* t₁' -> τ t₁ ⟶* τ t₁' := by {
  intro _ _ h
  induction h with
  | refl => exact .refl
  | step h _ ih => exact .step (hτ h) ih
}

end MultiStepDeriv

section Halting

class Halting (T : Type) [Derivable T] where
  measure : T -> Nat
  ordering {t t' : T} : t ⟶ t' → measure t' < measure t

variable {T : Type} [Derivable T] [Halting T]

instance : WellFoundedRelation T := measure Halting.measure

/-- 定理 3.5.12 -/
theorem evaluation_halting (t : T) : ∃ t', isNormalForm t' ∧ t ⟶* t' := by {
  rcases Classical.em (isNormalForm t) with h | h
  {
    exact ⟨t, h, .refl⟩
  }
  {
    rw [isNormalForm_not_iff] at h
    rcases h with ⟨t', ht⟩
    have := Halting.ordering ht
    have ⟨t'', ht'', h''⟩ := evaluation_halting t'
    exact ⟨t'', ht'', .step ht h''⟩
  }
}
termination_by Halting.measure t

end Halting

section Arithmetic

class Arithmetic (T : Type) extends Derivable T, HasValue T, Halting T where
  /-- 定理 3.5.4 -/
  determination {t t' t'' : T} : t ⟶ t' → (t ⟶ t'') → t' = t''
  /-- 定理 3.5.7 -/
  isNormalForm_of_isValue (t : T) : isValue t → isNormalForm t

variable {T : Type} [inst : Arithmetic T]

/-- 定理 3.5.11 -/
theorem NormalForm_unique {t u u' : T} (hu : isNormalForm u) (hu' : isNormalForm u') (h : t ⟶* u) (h' : t ⟶* u') : u = u' := by {
  induction h with
  | refl => {
    cases h' with
    | refl => rfl
    | step h' => exact absurd h' (hu _)
  }
  | step h hs ih => {
    cases h' with
    | refl => exact absurd h (hu' _)
    | step h' hs' => {
      rw [← inst.determination h h'] at hs'
      exact ih hs'
    }
  }
}

end Arithmetic

def isDeadlock {T : Type} [Derivable T] [HasValue T] (t : T) : Prop := isNormalForm t ∧ ¬ HasValue.isValue t
