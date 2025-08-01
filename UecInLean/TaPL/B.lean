import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Use

import UecInLean.TaPL.Notation

namespace UecInLean.TaPL

/-- 図 3-1 -/
inductive B
  | true
  | false
  | If (c t e : B)

namespace B

/-- 定義 3.5.3 -/
inductive eval : B -> B -> Prop
  | E_IfTrue (t₂ t₃ : B) : eval (If true t₂ t₃) t₂
  | E_IfFalse (t₂ t₃ : B) : eval (If false t₂ t₃) t₃
  | E_If (c c' t e : B) : eval c c' → eval (If c t e) (If c' t e)

instance : Derivable B := ⟨eval⟩

open eval

def s := If true false false
def t := If s true true
def u := If false true true

example : If t false false ⟶ If u false false := by {
  apply E_If
  apply E_If
  apply E_IfTrue
}

/-- 定理 3.5.4 -/
theorem determination {t t' t'' : B} : t ⟶ t' → t ⟶ t'' → t' = t'' := by {
  intro h₁ h₂
  cases h₁ with
  | E_IfTrue =>
    cases h₂ with
    | E_IfTrue => rfl
    -- | E_IfFalse _ _ => 条件部が `true` なので、この場合分けは不要
    | E_If => contradiction
  | E_IfFalse =>
    cases h₂ with
    -- | E_IfTrue _ _ => sorry
    | E_IfFalse => rfl
    | E_If => contradiction
  | E_If t₁ t₁' t₂ t₃ h1 => {
    cases h₂ with
    | E_IfTrue => contradiction
    | E_IfFalse => contradiction
    | E_If _ t₁'' _ _ h2 => {
      rw [determination h1 h2]
    }
  }
}

-- 演習 3.5.5 は定式化が難しいので保留。induction t などを使用のこと。
-- theorem induction_of_subDeriv {P : B → Prop} (h : ∀t₁, P t₁) : ∀ t, P t := sorry

def isValue (t : B) : Prop := match t with
  | true => True
  | false => True
  | If _ _ _ => False

theorem isValue_true : isValue true := by trivial
theorem isValue_false : isValue false := by trivial

theorem isValue_or_not (t : B) : t = true ∨ t = false ∨ ¬ isValue t := by {
  cases t with
  | true => left; trivial
  | false => right; left; trivial
  | If => right; right; intro h; cases h
}

/-- 定理 3.5.7 -/
theorem isNormalForm_of_isValue (t : B) : isValue t → isNormalForm t := by {
  intro h ⟨t', ht'⟩
  cases t with
  | true => contradiction -- true は正規形
  | false => contradiction -- false は正規形
  | If => exact h
}

theorem isValue_iff (t : B) : isValue t ↔ t = true ∨ t = false := by cases t <;> simp [isValue]

theorem not_isValue_iff (t : B) : ¬ isValue t ↔ (∃ t₁ t₂ t₃, t = If t₁ t₂ t₃) := by cases t <;> simp [isValue]

/-- 定理 3.5.8 -/
theorem isValue_of_isNormalForm (t : B) : isNormalForm t → isValue t := by {
  contrapose -- 対偶を示す。
  intro h
  rw [not_isNormalForm_iff] -- 今後扱いやすくするための変形
  induction t with
  | true => simp [isValue] at h -- 値ではないという仮定に矛盾
  | false => simp [isValue] at h -- 値ではないという仮定に矛盾
  | If t₁ t₂ t₃ ih => { -- 条件節 `t₁` に着目する。
    rcases isValue_or_not t₁ with rfl | rfl | h
    · exact ⟨_, E_IfTrue _ _⟩ -- `t₁` が `true` なら `E_IfTrue` で簡約可能
    · exact ⟨_, E_IfFalse _ _⟩ -- `t₁` が `false` なら `E_IfFalse` で簡約可能
    { -- `t₁` が値でない場合、帰納法の仮定から、簡約ステップが存在する。つまり、`E_If`で簡約可能
      have ⟨t₁', ht₁'⟩ := ih h
      exact ⟨_, E_If t₁ t₁' t₂ t₃ ht₁'⟩
    }
  }
}

theorem NormalForm_is_Value (t : B) : isNormalForm t ↔ isValue t := by {
  exact ⟨isValue_of_isNormalForm t, isNormalForm_of_isValue t⟩
}

theorem MultiStepDeriv.Es_If {t₁ t₁' t₂ t₃} : t₁ ⟶* t₁' -> (If t₁ t₂ t₃) ⟶* (If t₁' t₂ t₃) := by {
  intro h
  induction h with
  | refl => exact .refl
  | step h hs ih => exact MultiStepDeriv.step (E_If _ _ _ _ h) ih
}

def termSize : B -> Nat
  | true => 1
  | false => 1
  | If t₁ t₂ t₃ => 1 + termSize t₁ + termSize t₂ + termSize t₃

instance : Halting B where
  termSize
  termSize_ordering h := by induction h <;> simp only [termSize] <;> linarith

instance : Arithmetic B {true, false} eval := {
  determination,
  isValue,
  isNormalForm_of_isValue
}

-- 演習 3.5.12 (i)
namespace Funny1

inductive eval1 : B -> B -> Prop where
  | E_IfTrue (t₂ t₃) : eval1 (If true t₂ t₃) t₂
  | E_IfFalse (t₂ t₃) : eval1 (If false t₂ t₃) t₃
  | E_If (c c' t e) : eval1 c c' → eval1 (If c t e) (If c' t e)
  | E_Funny1 (t₂ t₃) : eval1 (If true t₂ t₃) t₃
open eval1

instance instDerivable1 : Derivable B := ⟨eval1⟩

instance instHalting1 : @Halting B instDerivable1 where
  termSize := termSize
  termSize_ordering h := by induction h <;> simp only [termSize] <;> linarith

theorem determination {t u u' : B} : t ⟶ u -> t ⟶ u' -> u = u'
  | .E_IfTrue _ _, .E_IfTrue _ _ => by trivial
  | .E_IfTrue _ _, .E_If _ _ _ _ _ => by trivial
  | .E_IfTrue _ _, .E_Funny1 _ _ => sorry
  | .E_IfFalse _ _, .E_IfFalse _ _ => by trivial
  | .E_IfFalse _ _, .E_If _ _ _ _ _ => by trivial
  | .E_If _ _ _ _ _, .E_IfTrue _ _ => by trivial
  | .E_If _ _ _ _ _, .E_IfFalse _ _ => by trivial
  | .E_If _ _ _ _ h, .E_If _ _ _ _ h' => by rw [determination h h']
  | .E_If _ _ _ _ _, .E_Funny1 _ _ => sorry
  | .E_Funny1 _ _, .E_IfTrue _ _ => sorry
  | .E_Funny1 _ _, .E_If _ _ _ _ _ => by trivial
  | .E_Funny1 _ _, .E_Funny1 _ _ => by trivial

end Funny1

namespace Funny2

inductive eval2 : B -> B -> Prop where
  | E_IfTrue (t₂ t₃) : eval2 (If true t₂ t₃) t₂
  | E_IfFalse (t₂ t₃) : eval2 (If false t₂ t₃) t₃
  | E_If (c c' t e) : eval2 c c' → eval2 (If c t e) (If c' t e)
  | E_Funny2 (t₁ t₂ t₂' t₃) : eval2 t₂ t₂' → eval2 (If t₁ t₂ t₃) (If t₁ t₂' t₃)
open eval2

instance instDerivable2 : Derivable B := ⟨eval2⟩

instance instHalting2 : @Halting B instDerivable2 where
  termSize := termSize
  termSize_ordering h := by induction h <;> simp only [termSize] <;> linarith

theorem determination {t u u' : B} : t ⟶ u -> t ⟶ u' -> u = u'
  | .E_IfTrue _ _, .E_IfTrue _ _ => by trivial
  | .E_IfTrue _ _, .E_If _ _ _ _ _ => by trivial
  | .E_IfTrue _ _, .E_Funny2 _ _ _ _ _ => sorry
  | .E_IfFalse _ _, .E_IfFalse _ _ => by trivial
  | .E_IfFalse _ _, .E_If _ _ _ _ _ => by trivial
  | .E_IfFalse _ _, .E_Funny2 _ _ _ _ _ => sorry
  | .E_If _ _ _ _ _, .E_IfTrue _ _ => by trivial
  | .E_If _ _ _ _ _, .E_IfFalse _ _ => by trivial
  | .E_If _ _ _ _ h, .E_If _ _ _ _ h' => by rw [determination h h']
  | .E_If _ _ _ _ _, .E_Funny2 _ _ _ _ _ => sorry
  | .E_Funny2 _ _ _ _ _, .E_IfTrue _ _ => sorry
  | .E_Funny2 _ _ _ _ _, .E_IfFalse _ _ => sorry
  | .E_Funny2 _ _ _ _ _, .E_If _ _ _ _ _ => sorry
  | .E_Funny2 _ _ _ _ h, .E_Funny2 _ _ _ _ h' => by rw [determination h h']

end Funny2
