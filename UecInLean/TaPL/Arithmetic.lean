import Init.WF

namespace UecInLean.TaPL

class Derivable (T : Type) where
  derivable : T -> T -> Prop
infix:100 " ⟶ " => Derivable.derivable

section NormalForm

variable {T : Type} {E : T -> T -> Prop} [Derivable T]

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

theorem MultiStepDeriv.push {t t' t'' : T} (h : t ⟶* t') (h' : t' ⟶ t'') : t ⟶* t'' := by {
  exact MultiStepDeriv.append h (.lift h')
}

theorem MultiStepDeriv.inherit {τ : T -> T} (hτ : ∀ {s s'}, s ⟶ s' -> τ s ⟶ τ s') : ∀ {t₁ t₁'}, t₁ ⟶* t₁' -> τ t₁ ⟶* τ t₁' := by {
  intro _ _ h
  induction h with
  | refl => exact .refl
  | step h _ ih => exact .step (hτ h) ih
}

theorem MultiStepDeriv.ne_refl {t t' : T} (h : t ⟶* t') (hne : t ≠ t') :
  ∃ v', t ⟶ v' ∧ v' ⟶* t' := by {
  cases h with
  | refl => contradiction
  | step h_step h_rest => exact ⟨_, h_step, h_rest⟩
}

theorem contra_of_isNormalForm_of_evals {r s : T} (hr : isNormalForm r) (rEs : r ⟶* s) (h : r ≠ s) : False := by {
  cases rEs with
  | refl => exact h rfl
  | step e _ => exact hr _ e
}

end MultiStepDeriv

section Halting

/-- 評価規則が違えば停止性も変わるため、`extends` ではない -/
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

section Determinancy

class OneStepDeterminancy (T : Type) [Derivable T] where
  /-- 定理 3.5.4 -/
  determinacy {t t' t'' : T} : t ⟶ t' → (t ⟶ t'') → t' = t''

class MultiStepDeterminancy (T : Type) [Derivable T] where
  /-- 定理 3.5.11 -/
  isNormalForm_unique {t u u' : T} (hu : isNormalForm u) (hu' : isNormalForm u') : t ⟶* u → t ⟶* u' → u = u'

/-- 定理 3.5.11 -/
instance {T : Type} [Derivable T] [inst : OneStepDeterminancy T] : MultiStepDeterminancy T := ⟨by {
  intro t t' t'' hu hu' h h'
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
      rw [← inst.determinacy h h'] at hs'
      exact ih hs'
    }
  }
}⟩

end Determinancy

section Diamond

class Diamond (T : Type) [Derivable T] where
  /-- 補題 A.1 -/
  diamond_property {r s t : T} (hrs : r ⟶ s) (hrt : r ⟶ t) (hst : s ≠ t) : s ⟶ t ∨ t ⟶ s ∨ ∃ u, s ⟶ u ∧ t ⟶ u

variable {T : Type} [Derivable T] [inst : Diamond T]

-- rEt₁ の eval2 は、どの Derivable インスタンスを使うか明示するためのもの。
/-- t側が1ステップの場合についての補題 -/
theorem one_side_diamond {r s t₁ : T} (rEs : r ⟶* s) (rEt₁ : r ⟶ t₁) (ht₁Es : ¬ t₁ ⟶* s) : ∃ u, s ⟶ u ∧ t₁ ⟶* u := by {
  induction rEs generalizing t₁ with
  | refl => exact ⟨t₁, rEt₁, .refl⟩
  | step rEs₁ s₁Es ih => {
    rename_i s₁ r
    rcases Classical.em (s₁ = t₁) with rfl | hs₁t₁
    { contradiction }
    { -- s₁ ≠ t₁ の場合
      obtain s₁Et₁ | t₁Es₁ | ⟨u, s₁Eu, t₁Eu⟩ := inst.diamond_property rEs₁ rEt₁ hs₁t₁
      { exact ih s₁Et₁ ht₁Es }
      {
        have t₁Es : t₁ ⟶* s := .step t₁Es₁ s₁Es
        contradiction
      }
      {
        have ⟨u', sEu', uEu'⟩ := ih s₁Eu (by {
          intro uEs
          have t₁Es : t₁ ⟶* s := .step t₁Eu uEs
          contradiction
        })
        exact ⟨u', sEu', .step t₁Eu uEu'⟩
      }
    }
  }
}

/-- ダイヤモンド性を組み合わせて、大きなダイヤモンドを構成する -/
theorem diamonds {r s t : T} (rEs : r ⟶* s) (rEt : r ⟶* t) (hst : s ≠ t) : s ⟶* t ∨ t ⟶* s ∨ ∃ u, s ⟶* u ∧ t ⟶* u := by {
  induction rEt generalizing s with
  | refl => right; left; exact rEs
  | step rEt₁ t₁Et ih => {
    cases rEs with
    | refl => left; exact .step rEt₁ t₁Et
    | step rEs₁ s₁Es => {
      rename_i t₁ r s₁
      rcases Classical.em (t₁ ⟶* s) with ht₁s | ht₁s
      · exact ih ht₁s hst
      {
        have ⟨u, sEu, t₁Eu⟩ := one_side_diamond (.step rEs₁ s₁Es) rEt₁ ht₁s
        rcases Classical.em (u = t) with rfl | hu
        · left; exact .lift sEu
        {
          obtain uEt | tEu | ⟨u', uEu', tEu'⟩ := ih t₁Eu hu
          · left; exact .step sEu uEt
          · right; right; exact ⟨u, sEu, tEu⟩
          · right; right; exact ⟨u', .step sEu uEu', tEu'⟩
        }
      }
    }
  }
}

instance {T : Type} [Derivable T] [inst : Diamond T] : MultiStepDeterminancy T := ⟨by {
  intro r s t hs ht rEs rEt
  apply Classical.byContradiction
  intro hst -- `s ≠ t` と仮定すればダイヤモンド性を使える
  obtain sEt | tEs | ⟨u, sEu, tEu⟩ := diamonds rEs rEt hst
  · exact contra_of_isNormalForm_of_evals hs sEt hst
  · exact contra_of_isNormalForm_of_evals ht tEs (Ne.symm hst)
  {
    cases tEu with
    | refl => exact contra_of_isNormalForm_of_evals hs sEu hst
    | step e _ => exact ht _ e
  }
}⟩

end Diamond

class Arithmetic (T : Type) [Derivable T] extends HasValue T, Halting T, MultiStepDeterminancy T where
  /-- 定理 3.5.7 -/
  isNormalForm_of_isValue {t : T} : isValue t → isNormalForm t

def isDeadlock {T : Type} [Derivable T] [HasValue T] (t : T) : Prop := isNormalForm t ∧ ¬ HasValue.isValue t
