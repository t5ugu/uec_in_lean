import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Use

import UecInLean.TaPL.Arithmetic

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
  intro h t' ht'
  cases t with
  | true => contradiction -- true は正規形
  | false => contradiction -- false は正規形
  | If => exact h
}

/-- 定理 3.5.8 -/
theorem isValue_of_isNormalForm (t : B) : isNormalForm t → isValue t := by {
  contrapose -- 対偶を示す。
  intro h
  rw [isNormalForm_not_iff] -- 今後扱いやすくするための変形
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

def termSize : B -> Nat
  | true => 1
  | false => 1
  | If t₁ t₂ t₃ => 1 + termSize t₁ + termSize t₂ + termSize t₃

instance : Halting B where
  measure := termSize
  ordering h := by induction h <;> simp only [termSize] <;> linarith

instance : OneStepDeterminancy B := ⟨determination⟩

instance : Arithmetic B := {
  isValue,
  isNormalForm_of_isValue := isNormalForm_of_isValue _
}

namespace Funny1 -- 演習 3.5.13 (1)

inductive eval1 : B -> B -> Prop where
  | E_IfTrue (t₂ t₃) : eval1 (If true t₂ t₃) t₂
  | E_IfFalse (t₂ t₃) : eval1 (If false t₂ t₃) t₃
  | E_If (c c' t e) : eval1 c c' → eval1 (If c t e) (If c' t e)
  | E_Funny1 (t₂ t₃) : eval1 (If true t₂ t₃) t₃
open eval1

instance instDerivable1 : Derivable B := ⟨eval1⟩

-- 定理 3.5.4 は成り立たない
-- theorem determination {t u u' : B} : t ⟶ u -> t ⟶ u' -> u = u'

/-- 定理 3.5.7 は成り立つ -/
theorem isNormalForm_of_isValue (t : B) : isValue t → isNormalForm t := by {
  intro h t' ht'
  cases t with
  | true => contradiction
  | false => contradiction
  | If => exact h
}

/-- 定理 3.5.8 は成り立つ -/
theorem isValue_of_isNormalForm (t : B) : isNormalForm t → isValue t := by {
  contrapose
  intro h
  rw [isNormalForm_not_iff]
  induction t with
  | true => simp [isValue] at h
  | false => simp [isValue] at h
  | If t₁ _ _ ih => {
    rcases isValue_or_not t₁ with rfl | rfl | h
    · exact ⟨_, E_IfTrue _ _⟩
    · exact ⟨_, E_IfFalse _ _⟩
    {
      have ⟨t₁', ht₁'⟩ := ih h
      exact ⟨_, E_If t₁ t₁' _ _ ht₁'⟩
    }
  }
}

-- 定理 3.5.11 は成り立たない
-- theorem NormalForm_unique {t u u' : T} (hu : isNormalForm u) (hu' : isNormalForm u') (h : t ⟶* u) (h' : t ⟶* u') : u = u'

-- このインスタンス化に誘導されて、定理 3.5.12 は成り立つ
instance : @Halting B instDerivable1 where
  measure := termSize
  ordering h := by induction h <;> simp only [termSize] <;> linarith

-- isNormalForm_unique が示せないので、Arithmetic のインスタンス化はできない。

end Funny1

namespace Funny2 -- 演習 3.5.13 (2)

inductive eval2 : B -> B -> Prop where
  | E_IfTrue (t₂ t₃) : eval2 (If true t₂ t₃) t₂
  | E_IfFalse (t₂ t₃) : eval2 (If false t₂ t₃) t₃
  | E_If (c c' t e) : eval2 c c' → eval2 (If c t e) (If c' t e)
  | E_Funny2 (t₁ t₂ t₂' t₃) : eval2 t₂ t₂' → eval2 (If t₁ t₂ t₃) (If t₁ t₂' t₃)
open eval2

instance instDerivable2 : Derivable B := ⟨eval2⟩

instance instHalting2 : @Halting B instDerivable2 where
  measure := termSize
  ordering h := by induction h <;> simp only [termSize] <;> linarith

-- 定理 3.5.4 は成り立たない
-- theorem determination {t u u' : B} : t ⟶ u -> t ⟶ u' -> u = u'

/-- 定理 3.5.7 -/
theorem isNormalForm_of_isValue {t : B} : isValue t → isNormalForm t := by {
  intro h t' ht'
  cases t with
  | true => contradiction
  | false => contradiction
  | If => exact h
}

/-- 定理 3.5.8 -/
theorem isValue_of_isNormalForm (t : B) : isNormalForm t → isValue t := by {
  contrapose
  intro h
  rw [isNormalForm_not_iff]
  induction t with
  | true => simp [isValue] at h
  | false => simp [isValue] at h
  | If t₁ _ _ ih => {
    rcases isValue_or_not t₁ with rfl | rfl | h
    · exact ⟨_, E_IfTrue _ _⟩
    · exact ⟨_, E_IfFalse _ _⟩
    {
      have ⟨t₁', ht₁'⟩ := ih h
      exact ⟨_, E_If t₁ t₁' _ _ ht₁'⟩
    }
  }
}

/-- 補題 A.1 -/
theorem diamond_property {r s t : B} (hrs : r ⟶ s) (hrt : r ⟶ t) (hst : s ≠ t) : s ⟶ t ∨ t ⟶ s ∨ ∃ u, s ⟶ u ∧ t ⟶ u := by {
  obtain ⟨r₁, r₂, r₃, rfl⟩ : ∃ r₁ r₂ r₃, r = If r₁ r₂ r₃ := by {
    cases r with
    | true => cases hrs
    | false => cases hrs
    | If r₁ r₂ r₃ => exact ⟨r₁, r₂, r₃, rfl⟩
  }
  match hrs, hrt with
  | .E_IfTrue _ _, .E_IfTrue _ _ => contradiction
  | .E_IfTrue _ _, .E_If _ _ _ _ h => cases h
  | .E_IfTrue _ _, .E_Funny2 _ _ r₂' _ h => right; right; exact ⟨r₂', h, .E_IfTrue _ _⟩
  | .E_IfFalse _ _, .E_IfFalse _ _ => contradiction
  | .E_IfFalse _ _, .E_If _ _ _ _ h => cases h
  | .E_IfFalse _ _, .E_Funny2 _ _ r₂' _ h => right; left; exact .E_IfFalse _ _
  | .E_If _ _ _ _ h, .E_IfTrue _ _ => cases h
  | .E_If _ _ _ _ h, .E_IfFalse _ _ => cases h
  | .E_If _ _ _ _ h, .E_If _ _ _ _ h' => {
    simp at hst
    obtain ih | ih | ⟨i, ih₁, ih₂⟩ := diamond_property h h' hst
    { left; exact .E_If _ _ _ _ ih }
    { right; left; exact .E_If _ _ _ _ ih }
    { right; right; exact ⟨.If i _ _, .E_If _ _ _ _ ih₁, .E_If _ _ _ _ ih₂⟩ }
  }
  | .E_If _ r₁' _ _ h, .E_Funny2 _ _ r₂' _ h' => {
    right; right; exact ⟨.If r₁' r₂' r₃, .E_Funny2 _ _ _ _ h', .E_If _ _ _ _ h⟩
  }
  | .E_Funny2 _ _ r₂' _ h, .E_IfTrue _ _ => right; right; exact ⟨r₂', .E_IfTrue _ _, h⟩
  | .E_Funny2 _ _ _ _ h, .E_IfFalse _ _ => left; exact .E_IfFalse _ _
  | .E_Funny2 _ _ r₂' _ h, .E_If _ r₁' _ _ h' => {
    right; right; exact ⟨.If r₁' r₂' r₃, .E_If _ _ _ _ h', .E_Funny2 _ _ _ _ h⟩
  }
  | .E_Funny2 _ _ _ _ h, .E_Funny2 _ _ _ _ h' => {
    simp at hst
    obtain ih | ih | ⟨i, ih₁, ih₂⟩ := diamond_property h h' hst
    { left; exact .E_Funny2 _ _ _ _ ih }
    { right; left; exact .E_Funny2 _ _ _ _ ih }
    { right; right; exact ⟨.If r₁ i r₃, .E_Funny2 _ _ _ _ ih₁, .E_Funny2 _ _ _ _ ih₂⟩ }
  }
}

-- このインスタンス化に誘導されて 定理 3.5.11 は成り立つ
instance : Diamond B := ⟨diamond_property⟩

instance : @Arithmetic B instDerivable2 where
  isNormalForm_of_isValue

end Funny2
