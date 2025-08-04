import Mathlib.Data.Set.Defs
import Mathlib.Tactic.Linarith

import UecInLean.TaPL.Arithmetic

namespace UecInLean.TaPL

namespace NB

/-- 公理2.4.2 -/
theorem complete_induction (P : Nat -> Prop) (h : ∀ n, (∀ i, i < n -> P i) -> P n) (n) : P n := Nat.lt_wfRel.wf.induction n h

/-- 3章 -/
inductive T : Type
  | true
  | false
  | If (c t e : T) -- `if` はキーワードなので使えない
  | zero
  | succ (n : T)
  | pred (n : T)
  | iszero (n : T)
deriving DecidableEq

def ofNat : Nat -> T
  | 0 => T.zero
  | n + 1 => T.succ (ofNat n)

instance {n} : OfNat T n := ⟨ofNat n⟩
@[simp]
theorem zero_eq_zero : 0 = T.zero := rfl

def s : Nat -> Set T
  | 0 => ∅
  | n + 1 =>
    { .true, .false, 0 }
    ∪ { .succ t | t ∈ s n }
    ∪ { .pred t | t ∈ s n }
    ∪ { .iszero t | t ∈ s n }
    ∪ { .If c t e | (c ∈ s n) (t ∈ s n) (e ∈ s n) }

theorem s0_elms : s 0 = ∅ := by rfl
theorem s1_elms : s 1 = { T.true, T.false, 0 } := by simp [s]
theorem sn_has_true (n) : T.true ∈ s (n + 1) := by simp [s]
theorem sn_has_false (n) : T.false ∈ s (n + 1) := by simp [s]
theorem sn_has_zero (n) : 0 ∈ s (n + 1) := by simp [s]
theorem sn_has_succ (n t) : t ∈ s n ↔ .succ t ∈ s (n + 1) := by simp [s]
theorem sn_has_pred (n t) : t ∈ s n ↔ .pred t ∈ s (n + 1) := by simp [s]
theorem sn_has_iszero (n t) : t ∈ s n ↔ .iszero t ∈ s (n + 1) := by simp [s]
theorem sn_has_if (n c t e) : (c ∈ s n ∧ t ∈ s n ∧ e ∈ s n) ↔ .If c t e ∈ s (n + 1) := by simp [s]

/-- 定義3.2.3 -/
def S := ⋃ i, s i

def count_si : Nat -> Nat
  | 0 => 0
  | n + 1 =>
    let si := count_si n
    3 + si + si + si + (si * si * si)

-- 演習3.2.4
#eval count_si 3

/-- 演習3.2.5 -/
theorem sn_accumulation (n) : s n ⊆ s (n + 1) := by
  induction n with
  | zero => simp [s]
  | succ n ih => {
    intro x hx
    rcases hx with ⟨⟨⟨⟨hco⟩ | ⟨hsu⟩⟩ | ⟨hpr⟩⟩ | ⟨hiz⟩⟩ | ⟨hif⟩
    {
      left; left; left; left
      exact hco
    }
    {
      left; left; left; right
      have ⟨t, ht, htx⟩ := hsu
      exact ⟨t, ih ht, htx⟩
    }
    {
      left; left; right
      have ⟨t, ht, htx⟩ := hpr
      exact ⟨t, ih ht, htx⟩
    }
    {
      left; right
      have ⟨t, ht, htx⟩ := hiz
      exact ⟨t, ih ht, htx⟩
    }
    {
      right
      have ⟨c, hc, t, ht, e, he, hcx⟩ := hif
      exact ⟨c, ih hc, t, ih ht, e, ih he, hcx⟩
    }
  }

theorem sn_has_pre_succ {n t} (h : .succ t ∈ s n) : t ∈ s n := by
  rw [sn_has_succ]; apply sn_accumulation; assumption


theorem sn_has_pre_pred {n t} (h : .pred t ∈ s n) : t ∈ s n := by
  rw [sn_has_pred]; apply sn_accumulation; assumption

theorem sn_has_pre_iszero {n t} (h : .iszero t ∈ s n) : t ∈ s n := by
  rw [sn_has_iszero]; apply sn_accumulation; assumption

theorem sn_has_pre_if {n c t e} (h : .If c t e ∈ s n) : c ∈ s n ∧ t ∈ s n ∧ e ∈ s n := by
  rw [sn_has_if]; apply sn_accumulation; assumption

theorem sn_accumulation' {m n} (h : m ≤ n) : s m ⊆ s n := by {
  set t := n - m with ht
  rw [show n = m + t by rw [ht, Nat.add_sub_cancel' h]]
  induction t with
  | zero => rw [Nat.add_zero]
  | succ n ih => {
    rw [← Nat.add_assoc]
    exact subset_trans ih <| sn_accumulation (m + n)
  }
}

theorem sn_sub_S (n) : s n ⊆ S := by {
  intro y hy
  unfold S
  rw [Set.mem_iUnion]
  use n
}

/-- 命題3.2.6 (a) SはTのなすものの一例である -/
theorem T_is_S : S = Set.univ := by {
  unfold S
  rw [Set.iUnion_eq_univ_iff]
  intro t
  induction t with
  | true | false | zero => use 1; simp [s1_elms]
  | succ n ih | pred n ih | iszero n ih => {
    rcases ih with ⟨i, hi⟩
    use i + 1
    simp [s, hi]
  }
  | If c t e ihc iht ihe => {
    rcases ihc with ⟨ic, hic⟩
    rcases iht with ⟨it, hit⟩
    rcases ihe with ⟨ie, hie⟩
    use max (max ic it) ie + 1
    simp [s]

    constructor <;> (try constructor) <;> {
      -- `sn_accumulation' _` 部で `s ic ⊆ s (max ic it ie)` を適用する。
      -- その後、`hic` などを適用すれば、証明できる。
      apply sn_accumulation' _ (by assumption)
      -- この `simp` は、ic ≤ max ic it ie などについて、すべきことが分かってから適用する
      simp only [le_sup_left, le_sup_right, le_sup_iff, or_true]
    }
  }
}

/-- 命題3.2.6 (b) Sは最小の集合である
  「最小の集合」として定義したつもりはないので、TaPLの証明もよくわかってない
-/
theorem S_is_least : ∀ S', S' = Set.univ -> S ⊆ S' := by {
  intro S' hS'
  rw [hS', T_is_S]
}

def Consts : T -> List T
  | T.true => [T.true]
  | T.false => [T.false]
  | T.zero => [T.zero]
  | T.succ n => Consts n
  | T.pred n => Consts n
  | T.iszero n => Consts n
  | T.If c t e => Consts c ++ Consts t ++ Consts e

def subterm : T -> List T
  | T.true => []
  | T.false => []
  | T.zero => []
  | T.succ n => subterm n
  | T.pred n => subterm n
  | T.iszero n => subterm n
  | T.If c t e => subterm c ++ subterm t ++ subterm e

def size : T -> Nat
  | T.true => 1
  | T.false => 1
  | T.zero => 1
  | T.succ n => size n + 1
  | T.pred n => size n + 1
  | T.iszero n => size n + 1
  | T.If c t e => size c + size t + size e + 1

def depth : T -> Nat
  | T.true => 1
  | T.false => 1
  | T.zero => 1
  | T.succ n => depth n + 1
  | T.pred n => depth n + 1
  | T.iszero n => depth n + 1
  | T.If c t e => max (max (depth c) (depth t)) (depth e) + 1

theorem lt_max_iff_or {a b c : Nat} (h : a < max b c) : a < b ∨ a < c := by {
  rw [Nat.max_def] at h
  rcases Nat.lt_or_ge c b with hbc | hbc
  · rw [lt_iff_not_ge] at hbc
    rw [if_neg hbc] at h
    left; assumption
  · rw [if_pos hbc] at h
    right; assumption
}

theorem eq_max_iff_or {a b c : Nat} (h : a = max b c) : a = b ∨ a = c := by {
  rw [Nat.max_def] at h
  rcases Nat.lt_or_ge c b with hbc | hbc
  · rw [lt_iff_not_ge] at hbc
    rw [if_neg hbc] at h
    left; assumption
  · rw [if_pos hbc] at h
    right; assumption
}

theorem t_is_in_least_depth_t (t : T) : t ∈ s (depth t) ∧ (∀ i < depth t, t ∉ s i) := by {
  constructor
  · induction t with
    | true | false | zero => simp [depth, s1_elms]
    | succ n ih | pred n ih | iszero n ih => simp [depth, s, ih]
    | If c t e ihc iht ihe => {
      apply Set.mem_union_right
      simp only [Set.mem_setOf_eq, T.If.injEq, existsAndEq, and_true]
      constructor <;> (try constructor) <;> {
        apply sn_accumulation' _ (by assumption)
        simp
      }
    }
  · intro i hi ht
    induction t generalizing i with
    | true | false | zero => {
      rw [depth, Nat.lt_one_iff] at hi
      rw [hi, s0_elms] at ht
      exact ht -- ∅ に属することはない
    }
    | succ n ih | pred n ih | iszero n ih => {
      induction i with
      | zero => exact ht
      | succ i _  => {
        rw [depth, add_lt_add_iff_right] at hi
        apply ih i hi
        -- 同様に...と言いたいだけ
        try rw [sn_has_succ]; exact ht
        try rw [sn_has_pred]; exact ht
        try rw [sn_has_iszero]; exact ht
      }
    }
    | If c t e ihc iht ihe => {
      induction i with
      | zero => exact ht
      | succ i hi' => {
        rw [← sn_has_if] at ht
        rw [depth, add_lt_add_iff_right] at hi
        rcases lt_max_iff_or hi with hct | hel
        · rcases lt_max_iff_or hct with hco | hth
          exact ihc i hco ht.1
          exact iht i hth ht.2.1
        · exact ihe i hel ht.2.2
      }
    }
}

theorem depth_positive (t : T) : depth t > 0 := by
  induction t with
  | true | false | zero => simp [depth]
  | succ n ih | pred n ih | iszero n ih => simp [depth, ih]
  | If c t e ihc iht ihe => simp [depth, ihc, iht, ihe]

theorem depth_nonzero {t : T} : depth t ≠ 0 := Nat.ne_of_gt (depth_positive t)

theorem size_nonzero {t : T} : size t ≠ 0 := by
  induction t with
  | true | false | zero => simp [size]
  | succ n ih | pred n ih | iszero n ih => simp [size, ih]
  | If c t e ihc iht ihe => simp [size, ihc, iht, ihe]

/-- 補題3.3.3 -/
theorem consts_le_size (t : T) : (Consts t).length ≤ size t := by
  induction t with
  | true | false | zero => simp [Consts, size]
  | succ n ih | pred n ih | iszero n ih => simp [Consts, size]; linarith
  | If c t e ihc iht ihe => simp [Consts, size]; linarith

instance instDepthWF : WellFoundedRelation T := measure depth

/-- 定理3.3.4 深さに関する帰納法 -/
theorem induction_by_depth (P : T -> Prop) (h : ∀s, (∀ r, depth r < depth s -> P r) -> P s) (s) : P s := by {
  apply h
  intro r hr
  induction s with
  | true | false | zero => {
    rw [depth, Nat.lt_one_iff] at hr
    have : False := depth_nonzero hr
    contradiction
  }
  | succ t ih | pred t ih | iszero t ih => {
    rw [depth] at hr
    rcases Nat.lt_or_eq_of_le <| Nat.le_of_lt_succ hr with hr | hr
    exact ih hr
    -- t と同じ depth で、t に関係ない r についても P r を言わないといけない。depth が Nat への写像ゆえの整礎性を使った。
    exact induction_by_depth P h r
  }
  | If c t e ihc iht ihe => {
    rw [depth, Nat.lt_succ_iff] at hr
    rcases Nat.lt_or_eq_of_le hr with hr | hr
    · rcases lt_max_iff_or hr with hr | he
      rcases lt_max_iff_or hr with hc | ht
      exact ihc hc
      exact iht ht
      exact ihe he
    · exact induction_by_depth P h r
  }
}
termination_by depth s

instance instSizeWF : WellFoundedRelation T := measure size

/-- 定理3.3.4 サイズに関する帰納法 -/
theorem induction_by_size (P : T -> Prop) (h : ∀ s, (∀ r, size r < size s -> P r) -> P s) (s) : P s := by {
  let Q (n : Nat) := ∀ s, size s = n -> P s
  have := complete_induction Q (by {
    intro n hn s hs
    apply h s
    intro r hr
    rw [hs] at hr
    exact hn (size r) hr r rfl
  })
  exact this (size s) s rfl
}

/-- 定理3.3.4 構造的帰納法 -/
theorem induction_by_structure (P : T -> Prop) (h : ∀ s, (∀ r, r ∈ subterm s -> P r) -> P s) : ∀ s, P s := by {
  intro s
  apply h
  intro r hr
  induction s with
  | true | false | zero => rw [subterm] at hr; contradiction
  | succ t ih | pred t ih | iszero t ih => rw [subterm] at hr; exact ih hr
  | If c t e ihc iht ihe => {
    rw [subterm, List.mem_append, List.mem_append] at hr
    rcases hr with ⟨hr | hr⟩ | hr
    exact ihc hr
    exact iht hr
    exact ihe hr
  }
}

inductive isNat : T -> Prop
  | zero : isNat 0
  | succ (n : T) : isNat n -> isNat (.succ n)

inductive isValue : T -> Prop
  | true : isValue T.true
  | false : isValue T.false
  | nat {n : T} : isNat n -> isValue n

inductive eval : T -> T -> Prop where
  | E_IfTrue {t₂ t₃} : eval (.If .true t₂ t₃) t₂
  | E_IfFalse {t₂ t₃} : eval (.If .false t₂ t₃) t₃
  | E_If {t₁ t₁' t₂ t₃} : eval t₁ t₁' -> eval (.If t₁ t₂ t₃) (.If t₁' t₂ t₃)
  | E_Succ {t₁ t₁'} : eval t₁ t₁' -> eval (.succ t₁) (.succ t₁')
  | E_PredZero : eval (.pred 0) 0
  | E_PredSucc {nv₁} (_ : isNat nv₁) : eval (.pred <| .succ nv₁) nv₁
  | E_Pred {t₁ t₁'} : eval t₁ t₁' -> eval (.pred t₁) (.pred t₁')
  | E_IszeroZero : eval (.iszero 0) .true
  | E_IszeroSucc {nv₁} (_ : isNat nv₁) : eval (.iszero <| .succ nv₁) .false
  | E_Iszero {t₁ t₁'} : eval t₁ t₁' -> eval (.iszero t₁) (.iszero t₁')

instance : Derivable T := ⟨eval⟩

open eval

@[simp] theorem isValue_true : isValue T.true := isValue.true
@[simp] theorem isValue_false : isValue T.false := isValue.false
@[simp] theorem isValue_zero : isValue T.zero := isValue.nat .zero
@[simp] theorem isValue_of_isNat {n : T} (hn : isNat n) : isValue n := isValue.nat hn
@[simp]
theorem isValue_not_If {c t e : T} : ¬ isValue (.If c t e) := by {
  intro h; cases h with | nat hn => cases hn
}
theorem isValue_succ {n : T} : isNat n ↔ isValue n.succ := by {
  constructor
  · intro h; exact isValue.nat h.succ
  · intro h; rcases h with _ | _ | ⟨⟨_⟩⟩; assumption
}

theorem isValue_not_pred {n : T} : ¬ isValue (.pred n) := by {
  intro h; cases h with | nat hn => cases hn
}
theorem isValue_not_iszero {n : T} : ¬ isValue (.iszero n) := by {
  intro h; cases h with | nat hn => cases hn
}

theorem isNormalForm_of_isValue (v : T) (hv : isValue v) : isNormalForm v := by {
  intro _ h
  cases hv with
  | true | false => cases h
  | nat hv =>
    cases hv with
    | zero => cases h
    | succ _ hv =>
      cases h with
      | E_Succ h' => exact isNormalForm_of_isValue _ (isValue_of_isNat hv) _ h'
}

theorem isNormalForm_of_isNat {n : T} (hn : isNat n) : isNormalForm n := isNormalForm_of_isValue _ (isValue_of_isNat hn)

/-- 演習 3.5.14 -/
theorem determination {t u u' : T} : t ⟶ u → t ⟶ u' → u = u'
  | .E_IfTrue, .E_IfTrue => by rfl
  | .E_IfFalse, .E_IfFalse => by rfl
  | .E_If h, .E_If h' => by rw [determination h h']
  | .E_Succ h, .E_Succ h' => by rw [determination h h']
  | .E_PredZero, .E_PredZero => by rfl
  | .E_PredSucc _, .E_PredSucc _ => by rfl
  | .E_PredSucc hu, .E_Pred (.E_Succ h') => by
    exact absurd h' (isNormalForm_of_isNat hu _)
  | .E_Pred (.E_Succ h), .E_PredSucc hu' => by
    exact absurd h (isNormalForm_of_isNat hu' _)
  | .E_Pred h, .E_Pred h' => by rw [determination h h']
  | .E_IszeroZero, .E_IszeroZero => by rfl
  | .E_IszeroSucc _, .E_IszeroSucc _ => by rfl
  | .E_IszeroSucc hu, .E_Iszero (E_Succ h') => by
    exact absurd h' (isNormalForm_of_isNat hu _)
  | .E_Iszero (E_Succ h), .E_IszeroSucc hu' => by
    exact absurd h (isNormalForm_of_isNat hu' _)
  | .E_Iszero h, .E_Iszero h' => by rw [determination h h']

instance : Arithmetic T := {
  isValue, measure := size,
  ordering h := by induction h <;> simp [size] <;> linarith
  determination, isNormalForm_of_isValue
}

end NB

namespace NBw  -- 演習 3.5.16

inductive T : Type
  | true
  | false
  | If (c t e : T)
  | zero
  | succ (n : T)
  | pred (n : T)
  | iszero (n : T)
  | wrong
open T

def size : T -> Nat
  | .true => 1
  | .false => 1
  | .If c t e => size c + size t + size e + 1
  | .zero => 1
  | .succ n => size n + 1
  | .pred n => size n + 1
  | .iszero n => size n + 1
  | .wrong => 0

def subterm : T -> List T
  | .true => []
  | .false => []
  | .zero => []
  | .succ n => subterm n
  | .pred n => subterm n
  | .iszero n => subterm n
  | .If c t e => subterm c ++ subterm t ++ subterm e
  | .wrong => [.wrong]

inductive isNat : T -> Prop
  | zero : isNat zero
  | succ (n : T) : isNat n -> isNat (succ n)

inductive isBadNat : T -> Prop
  | wrong : isBadNat wrong
  | true : isBadNat true
  | false : isBadNat false

inductive isBadBool : T -> Prop
  | wrong : isBadBool wrong
  | nat {n : T} : isNat n -> isBadBool n

inductive isValue : T -> Prop
  | true : isValue true
  | false : isValue false
  | nat {n : T} : isNat n -> isValue n

inductive eval : T -> T -> Prop where
  | E_IfTrue {t₂ t₃} : eval (If true t₂ t₃) t₂
  | E_IfFalse {t₂ t₃} : eval (If false t₂ t₃) t₃
  | E_If {t₁ t₁' t₂ t₃} : eval t₁ t₁' -> eval (If t₁ t₂ t₃) (If t₁' t₂ t₃)
  | E_Succ {t₁ t₁'} : eval t₁ t₁' -> eval (succ t₁) (succ t₁')
  | E_PredZero : eval (pred zero) zero
  | E_PredSucc {nv₁} (_ : isNat nv₁) : eval (pred (succ nv₁)) nv₁
  | E_Pred {t₁ t₁'} : eval t₁ t₁' -> eval (pred t₁) (pred t₁')
  | E_IszeroZero : eval (iszero zero) true
  | E_IszeroSucc {nv₁} (_ : isNat nv₁) : eval (iszero (succ nv₁)) false
  | E_Iszero {t₁ t₁'} : eval t₁ t₁' -> eval (iszero t₁) (iszero t₁')
  | E_If_Wrong {bb t₂ t₃} : isBadBool bb -> eval (If bb t₂ t₃) wrong
  | E_Succ_Wrong {bn} : isBadNat bn -> eval (succ bn) wrong
  | E_Pred_Wrong {bn} : isBadNat bn -> eval (pred bn) wrong
  | E_Iszero_Wrong {bn} : isBadNat bn -> eval (iszero bn) wrong

instance : Derivable T := ⟨eval⟩

theorem isNormalForm_of_isValue (v : T) (hv : isValue v) : isNormalForm v := by {
  intro _ h
  cases hv with
  | true | false => cases h
  | nat hv =>
    cases hv with
    | zero => cases h
    | succ _ hv =>
      cases h with
      | E_Succ h' => exact isNormalForm_of_isValue _ (isValue.nat hv) _ h'
      | E_Succ_Wrong h => cases hv <;> cases h
}

theorem isNormalForm_of_isNat {n : T} (hn : isNat n) : isNormalForm n := isNormalForm_of_isValue _ (isValue.nat hn)

-- 正直、これで場合が尽くされているかすこし疑問
theorem determination {t u u' : T} : t ⟶ u → t ⟶ u' → u = u'
  | .E_IfTrue, .E_IfTrue => by rfl
  | .E_IfFalse, .E_IfFalse => by rfl
  | .E_If h, .E_If h' => by rw [determination h h']
  | .E_If h, .E_If_Wrong (.nat h') => by exact absurd h (isNormalForm_of_isNat h' _)
  | .E_If_Wrong .wrong, .E_If h => by cases h
  | .E_If_Wrong (.nat h), .E_If h' => by exact absurd h' (isNormalForm_of_isNat h _)
  | .E_If_Wrong _, .E_If_Wrong _ => by rfl
  | .E_Succ h, .E_Succ h' => by rw [determination h h']
  | .E_Succ h, .E_Succ_Wrong .wrong => by cases h
  | .E_Succ_Wrong .wrong, .E_Succ h' => by cases h'
  | .E_Succ_Wrong _, .E_Succ_Wrong _ => by rfl
  | .E_PredZero, .E_PredZero => by rfl
  | .E_PredSucc _, .E_PredSucc _ => by rfl
  | .E_PredSucc h, .E_Pred (.E_Succ h') => by exact absurd h' (isNormalForm_of_isNat h _)
  | .E_PredSucc h, .E_Pred (.E_Succ_Wrong h') => by cases h <;> cases h'
  | .E_Pred h, .E_Pred h' => by rw [determination h h']
  | .E_Pred (.E_Succ h), .E_PredSucc h' => by exact absurd h (isNormalForm_of_isNat h' _)
  | .E_Pred (.E_Succ_Wrong h), .E_PredSucc h' => by cases h <;> cases h'
  | .E_Pred_Wrong .wrong, .E_Pred h' => by cases h'
  | .E_Pred_Wrong _, .E_Pred_Wrong _ => by rfl
  | .E_IszeroZero, .E_IszeroZero => by rfl
  | .E_IszeroSucc _, .E_IszeroSucc _ => by rfl
  | .E_IszeroSucc h, .E_Iszero (.E_Succ_Wrong h') => by cases h <;> cases h'
  | .E_Iszero h, .E_Iszero h' => by rw [determination h h']
  | .E_Iszero (.E_Succ h), .E_IszeroSucc h' => by exact absurd h (isNormalForm_of_isNat h' _)
  | .E_Iszero (.E_Succ_Wrong h), .E_IszeroSucc h' => by cases h <;> cases h'
  | .E_IszeroSucc h, .E_Iszero (.E_Succ h') => by exact absurd h' (isNormalForm_of_isNat h _)
  | .E_Iszero_Wrong _, .E_Iszero_Wrong _ => by rfl
  | .E_Iszero_Wrong .true, .E_Iszero nf => by cases nf

instance : Arithmetic T := {
  isValue, measure := size,
  ordering h := by induction h <;> simp [size] <;> linarith
  determination, isNormalForm_of_isValue
}

theorem Es_If {t t' t₂ t₃} : t ⟶* t' → (If t t₂ t₃) ⟶* (If t' t₂ t₃) := @MultiStepDeriv.inherit NBw.T inferInstance (fun t => .If t t₂ t₃) .E_If _ _

theorem Es_Succ {t t'} : t ⟶* t' → (succ t) ⟶* (succ t') := @MultiStepDeriv.inherit NBw.T inferInstance (fun t => .succ t) .E_Succ _ _

theorem Es_Pred {t t'} : t ⟶* t' → (pred t) ⟶* (pred t') := @MultiStepDeriv.inherit NBw.T inferInstance (fun t => .pred t) .E_Pred _ _

theorem Es_Iszero {t t'} : t ⟶* t' → (iszero t) ⟶* (iszero t') := @MultiStepDeriv.inherit NBw.T inferInstance (fun t => .iszero t) .E_Iszero _ _

def lift : NB.T -> NBw.T
  | .true => NBw.T.true
  | .false => NBw.T.false
  | .If c t e => NBw.T.If (lift c) (lift t) (lift e)
  | .zero => NBw.T.zero
  | .succ n => NBw.T.succ (lift n)
  | .pred n => NBw.T.pred (lift n)
  | .iszero n => NBw.T.iszero (lift n)

instance : CoeSort NB.T NBw.T := ⟨lift⟩

theorem lift_is_not_wrong {t : NB.T} : lift t ≠ NBw.T.wrong := by {
  intro h
  induction t <;> simp [lift] at h
}

theorem lift_injective : Function.Injective lift := by {
  intro g v h
  match g, v with
  | .true, .true => rfl
  | .false, .false => rfl
  | .zero, .zero => rfl
  | .succ _, .succ _ => rw [lift_injective (NBw.T.succ.inj h)]
  | .pred _, .pred _ => rw [lift_injective (NBw.T.pred.inj h)]
  | .iszero _, .iszero _ => rw [lift_injective (NBw.T.iszero.inj h)]
  | .If c t e, .If c' t' e' => {
    rw [NB.T.If.injEq]
    have ⟨hc, ht, he⟩ := NBw.T.If.inj h
    exact ⟨lift_injective hc, lift_injective ht, lift_injective he⟩
  }
}

open NB.eval NBw.eval MultiStepDeriv

theorem isNat_lift {v : NB.T} : NB.isNat v → NBw.isNat (lift v) := by {
  intro hv
  induction hv with
  | zero => exact .zero
  | succ _ _ ih => exact .succ _ ih
}

theorem isNat_descend {v : NB.T} : NBw.isNat (lift v) → NB.isNat v := by {
  intro hv
  cases v with
  | true | false | If | pred | iszero => {
    cases hv
  }
  | zero => exact .zero
  | succ => {
    cases hv with
    | succ _ h => {
      exact .succ _ (isNat_descend h)
    }
  }
}

@[cases_eliminator]
theorem casesOn_lift_eval {motive : (t : NB.T) -> (t' : NBw.T) -> (lift t) ⟶ t' -> Prop}
  (E_IfTrue : ∀ {t₂ t₃}, motive (.If .true t₂ t₃) t₂ .E_IfTrue)
  (E_IfFalse : ∀ {t₂ t₃}, motive (.If .false t₂ t₃) t₃ .E_IfFalse)
  (E_If : ∀ {t₁ t₁' t₂ t₃} (ih : lift t₁ ⟶ t₁'), motive (.If t₁ t₂ t₃) (.If t₁' t₂ t₃) (.E_If ih))
  (E_If_Wrong : ∀ {bb t₂ t₃} (ih : NB.isNat bb), motive (.If bb t₂ t₃) .wrong (.E_If_Wrong (.nat <| isNat_lift ih)))
  (E_Succ : ∀ {t₁ t₁'} (ih : lift t₁ ⟶ t₁'), motive t₁.succ t₁'.succ (.E_Succ ih))
  (E_Succ_Wrong_True : motive (.succ .true) .wrong (.E_Succ_Wrong .true))
  (E_Succ_Wrong_False : motive (.succ .false) .wrong (.E_Succ_Wrong .false))
  (E_PredZero : motive (.pred 0) .zero .E_PredZero)
  (E_PredSucc : ∀ {nv₁} (ih : NB.isNat nv₁), motive nv₁.succ.pred nv₁ (.E_PredSucc (isNat_lift ih)))
  (E_Pred : ∀ {t₁ t₁'} (ih : lift t₁ ⟶ t₁'), motive t₁.pred t₁'.pred (.E_Pred ih))
  (E_Pred_Wrong_True : motive (.pred .true) .wrong (.E_Pred_Wrong .true))
  (E_Pred_Wrong_False : motive (.pred .false) .wrong (.E_Pred_Wrong .false))
  (E_IszeroZero : motive (.iszero 0) .true (.E_IszeroZero))
  (E_IszeroSucc : ∀ {nv₁} (ih : NB.isNat nv₁), motive (.iszero (.succ nv₁)) .false (.E_IszeroSucc (isNat_lift ih)))
  (E_Iszero : ∀ {t₁ t₁'} (ih : lift t₁ ⟶ t₁'), motive (.iszero t₁) (.iszero t₁') (.E_Iszero ih))
  (E_Iszero_Wrong_True : motive (.iszero .true) .wrong (.E_Iszero_Wrong .true))
  (E_Iszero_Wrong_False : motive (.iszero .false) .wrong (.E_Iszero_Wrong .false))
  {g t} (h : lift g ⟶ t) : motive g t h := by {
  match g, h with
  | .If .true _ _, .E_IfTrue => exact E_IfTrue
  | .If .false _ _, .E_IfFalse => exact E_IfFalse
  | .If _ _ _, .E_If h => exact E_If h
  | .If _ _ _, .E_If_Wrong (.nat h) => exact E_If_Wrong (isNat_descend h)
  | .succ _, .E_Succ h => exact E_Succ h
  | .succ .true, .E_Succ_Wrong .true => exact E_Succ_Wrong_True
  | .succ .false, .E_Succ_Wrong .false => exact E_Succ_Wrong_False
  | .pred .zero, .E_PredZero => exact E_PredZero
  | .pred (NB.T.succ nv₁), .E_PredSucc h => exact E_PredSucc (isNat_descend h)
  | .pred _, .E_Pred h => exact E_Pred h
  | .pred .true, .E_Pred_Wrong .true => exact E_Pred_Wrong_True
  | .pred .false, .E_Pred_Wrong .false => exact E_Pred_Wrong_False
  | .iszero .zero, .E_IszeroZero => exact E_IszeroZero
  | .iszero (NB.T.succ nv₁), .E_IszeroSucc h => exact E_IszeroSucc (isNat_descend h)
  | .iszero _, .E_Iszero h => exact E_Iszero h
  | .iszero .true, .E_Iszero_Wrong .true => exact E_Iszero_Wrong_True
  | .iszero .false, .E_Iszero_Wrong .false => exact E_Iszero_Wrong_False
}

theorem isBadBool_lift_iff {v : NB.T} : NBw.isBadBool (lift v) ↔ NB.isNat v := by {
  constructor
  {
    intro h
    cases v with
    | true | false | If | iszero => { rcases h with _ | ⟨_ | _⟩ }
    | zero => exact .zero
    | succ | pred => cases h with | nat h => exact isNat_descend h
  }
  {
    intro h
    exact .nat (isNat_lift h)
  }
}

theorem eval_lift {g v : NB.T} (h : g ⟶ v) : lift g ⟶ lift v := by {
  induction h using NB.eval.recOn with
  | E_IfTrue => exact .E_IfTrue
  | E_IfFalse => exact .E_IfFalse
  | E_If _ ih => exact .E_If ih
  | E_Succ _ ih => exact .E_Succ ih
  | E_PredZero => exact .E_PredZero
  | E_PredSucc ih => exact .E_PredSucc (isNat_lift ih)
  | E_Pred _ ih => exact .E_Pred ih
  | E_IszeroZero => exact .E_IszeroZero
  | E_IszeroSucc ih => exact .E_IszeroSucc (isNat_lift ih)
  | E_Iszero _ ih => exact .E_Iszero ih
}

theorem evals_lift (g v : NB.T) : g ⟶* v → lift g ⟶* lift v := by {
  intro h
  induction h with
  | refl => exact .refl
  | step h hs ih => exact .step (eval_lift h) ih
}

/-- 補題 A.3 -/
theorem eval_unique {g g'} (h : g ⟶ g') : ∀ g'' ≠ lift g', ¬ (lift g) ⟶ g'' := by {
  intro g'' hne h'
  exact hne (NBw.determination (eval_lift h) h').symm
}

/-- 補題 A.4 -/
theorem deadlock_to_wrong (g : NB.T) : isDeadlock g → lift g ⟶* NBw.T.wrong := by {
  intro ⟨hnf, hnv⟩
  induction g with
  | true | false | zero => simp [HasValue.isValue] at hnv
  | If g₁ g₂ g₃ ih₁ _ _ => {
    cases Classical.em (isNormalForm g₁) with
    | inr h => {
      rw [isNormalForm_not_iff] at h
      rcases h with ⟨g₁', h⟩
      exact absurd (.E_If h) (hnf <| .If g₁' g₂ g₃)
    }
    | inl h => {
      cases g₁ with
      | true => exact absurd (.E_IfTrue) (hnf _)
      | false => exact absurd (.E_IfFalse) (hnf _)
      | If _ _ _ => {
        -- g₁ ⟶* wrong
        have := ih₁ h NB.isValue_not_If
        -- g = if g₁ _ _ ⟶* if wrong _ _ ⟶* wrong
        exact (NBw.Es_If this).append (MultiStepDeriv.lift <| .E_If_Wrong .wrong)
      }
      | zero => exact MultiStepDeriv.lift <| .E_If_Wrong (.nat .zero)
      | succ g₁₁ => {
        cases Classical.em (NB.isNat g₁₁) with
        | inl hg => { -- g₁₁ が数値なら g₁ = succ g₁₁ は badbool
          have hg : NBw.isBadBool (.succ g₁₁) := .nat (.succ _ (isNat_lift hg))
          exact MultiStepDeriv.lift (.E_If_Wrong hg)
        }
        | inr hg => {
          have := ih₁ h (by { -- 数値でないなら Value でない
            intro h
            cases h with
            | nat h =>
              cases h with
              | succ => contradiction
          })
          exact (NBw.Es_If this).append (MultiStepDeriv.lift <| NBw.eval.E_If_Wrong .wrong)
        }
      }
      | pred g₁₁ => { -- 流れは succ と同じ
        cases Classical.em (NB.isNat g₁₁) with
        | inl hg => {
          have hg : NBw.isBadBool (.pred g₁₁) := by {
            cases hg with
            | zero => exact absurd (.E_PredZero) (h _)
            | succ _ hg => exact absurd (.E_PredSucc hg) (h _)
          }
          apply MultiStepDeriv.lift (NBw.eval.E_If_Wrong hg)
        }
        | inr hg => {
          have := ih₁ h (by intro h; rcases h with _ | _ | ⟨⟨_⟩⟩)
          exact (NBw.Es_If this).append (MultiStepDeriv.lift <| NBw.eval.E_If_Wrong .wrong)
        }
      }
      | iszero g₁₁ => {
        cases Classical.em (NB.isNat g₁₁) with
        | inl hg => {
          have hg : NBw.isBadBool (.iszero g₁₁) := by {
            cases hg with
            | zero => exact absurd (.E_IszeroZero) (h _)
            | succ _ hg => exact absurd (.E_IszeroSucc hg) (h _)
          }
          exact MultiStepDeriv.lift (NBw.eval.E_If_Wrong hg)
        }
        | inr hg => {
          have := ih₁ h (by intro h; rcases h with _ | _ | ⟨⟨h⟩⟩)
          exact (NBw.Es_If this).append (MultiStepDeriv.lift <| NBw.eval.E_If_Wrong .wrong)
        }
      }
    }
  }
  | succ g₁ ih => {
    have : (g₁ = .true ∨ g₁ = .false) ∨ isDeadlock g₁ := by {
      simp only [HasValue.isValue, ← NB.isValue_succ] at hnv
      have hnf : isNormalForm g₁ := isNormalForm_of_pre NB.eval.E_Succ hnf
      cases Classical.em (NB.isValue g₁) with
      | inl h => {
        cases h with
        | true => left; left; rfl
        | false => left; right; rfl
        | nat h => contradiction
      }
      | inr h => right; exact ⟨hnf, h⟩
    }
    rcases this with ⟨h | h⟩ | ⟨hnf, hnv⟩
    {
      rw [h]
      exact MultiStepDeriv.lift <| NBw.eval.E_Succ_Wrong .true
    }
    {
      rw [h]
      exact MultiStepDeriv.lift <| NBw.eval.E_Succ_Wrong .false
    }
    {
      have := ih hnf hnv
      exact (NBw.Es_Succ this).append (MultiStepDeriv.lift <| NBw.eval.E_Succ_Wrong .wrong)
    }
  }
  | pred g₁ ih => {
    cases Classical.em (NB.isValue g₁) with
    | inl hg => {
      cases hg with
      | true => exact MultiStepDeriv.lift <| .E_Pred_Wrong .true
      | false => exact MultiStepDeriv.lift <| .E_Pred_Wrong .false
      | nat hg => {
        cases hg with
        | zero => exact absurd (.E_PredZero) (hnf _)
        | succ _ hg => exact absurd (.E_PredSucc hg) (hnf _)
      }
    }
    | inr hg => {
      exact (NBw.Es_Pred (ih (isNormalForm_of_pre NB.eval.E_Pred hnf) hg)).append (MultiStepDeriv.lift <| .E_Pred_Wrong .wrong)
    }
  }
  | iszero g₁ ih => {
    cases Classical.em (NB.isValue g₁) with
    | inl hg => {
      cases hg with
      | true => exact MultiStepDeriv.lift <| .E_Iszero_Wrong .true
      | false => exact MultiStepDeriv.lift <| .E_Iszero_Wrong .false
      | nat hg => {
        cases hg with
        | zero => exact absurd (.E_IszeroZero) (hnf _)
        | succ _ hg => exact absurd (.E_IszeroSucc hg) (hnf _)
      }
    }
    | inr hg => {
      exact (NBw.Es_Iszero (ih (isNormalForm_of_pre NB.eval.E_Iszero hnf) hg)).append (MultiStepDeriv.lift <| .E_Iszero_Wrong .wrong)
    }
  }
}

theorem deadlock_succ {t : NB.T} (h : isDeadlock t) : isDeadlock t.succ := ⟨
  by {
    intro t' ht'
    cases ht' using NB.eval.casesOn with
    | E_Succ ht' => {
      exact h.left _ ht'
    }
  }, by {
    intro hnv
    rcases hnv with _ | _ | ⟨⟨_⟩⟩
    exact h.right (NB.isValue_of_isNat (by assumption))
  }
⟩

theorem deadlock_pred {t : NB.T} (h : isDeadlock t) : isDeadlock t.pred := ⟨
  by {
    intro t' ht'
    cases ht' using NB.eval.casesOn with
    | E_PredZero => exact h.right (.nat .zero)
    | E_PredSucc ht' => exact h.right (NB.isValue_of_isNat ht'.succ)
    | E_Pred ht' => exact h.left _ ht'
  }, by {
    intro hnv
    rcases hnv with _ | _ | ⟨⟨_⟩⟩
  }
⟩

theorem deadlock_If {c : NB.T} (t e) (h : isDeadlock c) : isDeadlock (NB.T.If c t e) := ⟨
  by {
    intro t' ht'
    cases ht' using NB.eval.casesOn with
    | E_IfTrue => exact h.right .true
    | E_IfFalse => exact h.right .false
    | E_If ht' => exact h.left _ ht'
  }, by {
    intro hnv
    rcases hnv with _ | _ | ⟨⟨_⟩⟩
  }
⟩

theorem deadlock_iszero {t : NB.T} (h : isDeadlock t) : isDeadlock t.iszero := ⟨
  by {
    intro t' ht'
    cases ht' using NB.eval.casesOn with
    | E_IszeroZero => exact h.right (.nat .zero)
    | E_IszeroSucc ht' => exact h.right (NB.isValue_of_isNat ht'.succ)
    | E_Iszero ht' => exact h.left _ ht'
  }, by {
    intro hnv
    rcases hnv with _ | _ | ⟨⟨_⟩⟩
  }
⟩

theorem deadlock_If_nat {bb : NB.T} (t₂ t₃) (h : NB.isNat bb) : isDeadlock (NB.T.If bb t₂ t₃) := ⟨
  by intro _ ht'; exact lift_is_not_wrong (NBw.determination (eval_lift ht') (.E_If_Wrong <| .nat (isNat_lift h)))
, by intro hnv; exact NB.isValue_not_If hnv
⟩

theorem deadlock_succ_true : isDeadlock (NB.T.succ .true) := ⟨
  by intro _ ht'; exact lift_is_not_wrong (NBw.determination (eval_lift ht') (.E_Succ_Wrong .true))
, by intro hnv; rcases hnv with _ | _ | ⟨_ | ⟨_, ⟨⟩⟩⟩
⟩

theorem deadlock_succ_false : isDeadlock (NB.T.succ .false) := ⟨
  by intro _ ht'; exact lift_is_not_wrong (NBw.determination (eval_lift ht') (.E_Succ_Wrong .false))
, by intro hnv; rcases hnv with _ | _ | ⟨_ | ⟨_, ⟨⟩⟩⟩
⟩

theorem deadlock_pred_true : isDeadlock (NB.T.pred .true) := ⟨
  by intro _ ht'; exact lift_is_not_wrong (NBw.determination (eval_lift ht') (.E_Pred_Wrong .true))
, by intro hnv; rcases hnv with _ | _ | ⟨_ | ⟨_, ⟨⟩⟩⟩
⟩

theorem deadlock_pred_false : isDeadlock (NB.T.pred .false) := ⟨
  by intro _ ht'; exact lift_is_not_wrong (NBw.determination (eval_lift ht') (.E_Pred_Wrong .false))
, by intro hnv; rcases hnv with _ | _ | ⟨_ | ⟨_, ⟨⟩⟩⟩
⟩

theorem deadlock_iszero_true : isDeadlock (NB.T.iszero .true) := ⟨
  by intro _ ht'; exact lift_is_not_wrong (NBw.determination (eval_lift ht') (.E_Iszero_Wrong .true))
, by intro hnv; rcases hnv with _ | _ | ⟨_ | ⟨_, ⟨⟩⟩⟩
⟩

theorem deadlock_iszero_false : isDeadlock (NB.T.iszero .false) := ⟨
  by intro _ ht'; exact lift_is_not_wrong (NBw.determination (eval_lift ht') (.E_Iszero_Wrong .false))
, by intro hnv; rcases hnv with _ | _ | ⟨_ | ⟨_, ⟨⟩⟩⟩
⟩

theorem subterm_lift_nin_wrong {t : NB.T} : NBw.T.wrong ∉ NBw.subterm (lift t) := by {
  induction t with
  | true | false | zero => simp [lift, NBw.subterm]
  | succ _ ih | pred _ ih | iszero _ ih => {
    rw [lift, NBw.subterm]
    exact ih
  }
  | If _ _ _ ihc iht ihe => {
    rw [lift, NBw.subterm]
    simp only [List.mem_append, not_or, and_assoc]
    exact ⟨ihc, iht, ihe⟩
  }
}

theorem deadlock_is_wrong (g : NB.T) : (∃ g', g ⟶* g' ∧ isDeadlock g') -> (g ⟶* NBw.T.wrong) := by {
  intro ⟨g', h, hg'⟩
  induction h with
  | refl => {
    exact deadlock_to_wrong g' hg'
  }
  | step h _ ih => {
    exact (MultiStepDeriv.lift (eval_lift h)).append ih
  }
}

/-- 補題 A.5 -/
theorem subterm_wrong_deadlock {g t} (h : lift g ⟶ t) (ht : NBw.T.wrong ∈ NBw.subterm t) : isDeadlock g := by {
  cases h using casesOn_lift_eval with
  | E_IfTrue => exact absurd ht subterm_lift_nin_wrong
  | E_IfFalse => exact absurd ht subterm_lift_nin_wrong
  | E_If h => {
    simp only [NBw.subterm, List.mem_append, subterm_lift_nin_wrong, or_false] at ht
    exact deadlock_If _ _ <| subterm_wrong_deadlock h ht
  }
  | E_If_Wrong h => exact deadlock_If_nat _ _ h
  | E_Succ h => {
    rw [NBw.subterm] at ht
    exact deadlock_succ <| subterm_wrong_deadlock h ht
  }
  | E_Succ_Wrong_True => exact deadlock_succ_true
  | E_Succ_Wrong_False => exact deadlock_succ_false
  | E_PredZero => cases ht
  | E_PredSucc h => exact absurd ht subterm_lift_nin_wrong
  | E_Pred h => {
    rw [NBw.subterm] at ht
    exact deadlock_pred <| subterm_wrong_deadlock h ht
  }
  | E_Pred_Wrong_True => exact deadlock_pred_true
  | E_Pred_Wrong_False => exact deadlock_pred_false
  | E_IszeroZero => cases ht
  | E_IszeroSucc => cases ht
  | E_Iszero h => {
    rw [NBw.subterm] at ht
    exact deadlock_iszero <| subterm_wrong_deadlock h ht
  }
  | E_Iszero_Wrong_True => exact deadlock_iszero_true
  | E_Iszero_Wrong_False => exact deadlock_iszero_false
}

theorem descend_of_nin_wrong {t : NBw.T} (h : NBw.T.wrong ∉ NBw.subterm t) : ∃ g, t = lift g := by {
  induction t with
  | true => exact ⟨.true, rfl⟩
  | false => exact ⟨.false, rfl⟩
  | zero => exact ⟨.zero, rfl⟩
  | succ t ih => {
    have ⟨g, hg⟩ := ih h
    exact ⟨.succ g, by rw [lift, hg]⟩
  }
  | pred t ih => {
    have ⟨g, hg⟩ := ih h
    exact ⟨.pred g, by rw [lift, hg]⟩
  }
  | iszero t ih => {
    have ⟨g, hg⟩ := ih h
    exact ⟨.iszero g, by rw [lift, hg]⟩
  }
  | If c t₁ t₂ ihc iht ihe => {
    simp [NBw.subterm, List.mem_append] at h
    have ⟨hc, ht₁, ht₂⟩ := h
    have ⟨g₁, hg₁⟩ := ihc hc
    have ⟨g₂, hg₂⟩ := iht ht₁
    have ⟨g₃, hg₃⟩ := ihe ht₂
    exact ⟨.If g₁ g₂ g₃, by rw [lift, hg₁, hg₂, hg₃]⟩
  }
  | wrong => rw [NBw.subterm] at h; exact absurd (List.mem_singleton_self _) h
}

theorem descend_of_subterm_lift (t g) (h : NBw.subterm t ⊆ NBw.subterm (lift g)) : ∃ g', t = lift g' := by {
  apply descend_of_nin_wrong
  intro h'
  exact absurd (h h') subterm_lift_nin_wrong
}

theorem evals_wrong_is_step {g : NB.T} (h : lift g ⟶* NBw.T.wrong) : ∃ v', lift g ⟶ v' ∧ v' ⟶* NBw.T.wrong := by {
  exact MultiStepDeriv.ne_refl h lift_is_not_wrong
}

theorem eval_descend {g g'} : lift g ⟶ lift g' → g ⟶ g' := by {
  generalize hv : lift g = v
  generalize hv' : lift g' = v'
  intro h
  induction h generalizing g g' with
  | E_IfTrue => {
    rename_i t₂ t₃
    have ⟨g, hg⟩ := descend_of_subterm_lift t₃ g (by simp [hv, NBw.subterm])
    rw [← lift, ← hv', hg, ← lift] at hv
    rw [lift_injective hv]
    exact .E_IfTrue
  }
  | E_IfFalse => {
    rename_i t₂ t₃
    have ⟨g, hg⟩ := descend_of_subterm_lift t₂ g (by simp [hv, NBw.subterm])
    rw [← lift, ← hv', hg, ← lift] at hv
    rw [lift_injective hv]
    exact .E_IfFalse
  }
  | E_If h ih => {
    rename_i c c' t e
    rcases descend_of_subterm_lift c g (by simp [hv, NBw.subterm]) with ⟨c₁, rfl⟩
    rcases descend_of_subterm_lift c' g' (by simp [hv', NBw.subterm]) with ⟨c'₁, rfl⟩
    rcases descend_of_subterm_lift t g (by simp [hv, NBw.subterm]) with ⟨t₁, rfl⟩
    rcases descend_of_subterm_lift e g (by simp [hv, NBw.subterm]) with ⟨e₁, rfl⟩
    rw [← lift] at hv hv'
    rw [lift_injective hv, lift_injective hv']
    exact .E_If (ih rfl rfl)
  }
  | E_If_Wrong h => exact absurd hv' lift_is_not_wrong
  | E_Succ h ih => {
    rename_i n n'
    have ⟨g, hg⟩ := descend_of_subterm_lift n g (by simp [hv, NBw.subterm])
    have ⟨g', hg'⟩ := descend_of_subterm_lift n' g' (by simp [hv', NBw.subterm])
    rw [hg, ← lift] at hv; rw [lift_injective hv]
    rw [hg', ← lift] at hv'; rw [lift_injective hv']
    exact .E_Succ (ih hg.symm hg'.symm)
  }
  | E_Succ_Wrong => exact absurd hv' lift_is_not_wrong
  | E_PredZero => {
    rw [← lift, ← lift] at hv; rw [← lift] at hv'
    rw [lift_injective hv, lift_injective hv']
    exact .E_PredZero
  }
  | E_PredSucc h => {
    rename_i n
    have ⟨g, hg⟩ := descend_of_subterm_lift n g (by simp [hv, NBw.subterm])
    rw [hg, ← lift, ← lift] at hv;
    rw [hg] at hv' h
    rw [lift_injective hv, lift_injective hv']
    exact .E_PredSucc (isNat_descend h)
  }
  | E_Pred h ih => {
    rename_i n n'
    have ⟨g, hg⟩ := descend_of_subterm_lift n g (by simp [hv, NBw.subterm])
    have ⟨g', hg'⟩ := descend_of_subterm_lift n' g' (by simp [hv', NBw.subterm])
    rw [hg, ← lift] at hv; rw [lift_injective hv]
    rw [hg', ← lift] at hv'; rw [lift_injective hv']
    exact .E_Pred (ih hg.symm hg'.symm)
  }
  | E_Pred_Wrong => exact absurd hv' lift_is_not_wrong
  | E_IszeroZero => {
    rw [← lift, ← lift] at hv; rw [← lift] at hv'
    rw [lift_injective hv, lift_injective hv']
    exact .E_IszeroZero
  }
  | E_IszeroSucc h => {
    rename_i n
    have ⟨g, hg⟩ := descend_of_subterm_lift n g (by simp [hv, NBw.subterm])
    rw [hg, ← lift, ← lift] at hv
    rw [hg] at h
    rw [← lift] at hv'
    rw [lift_injective hv, lift_injective hv']
    exact .E_IszeroSucc (isNat_descend h)
  }
  | E_Iszero h ih => {
    rename_i n n'
    have ⟨g, hg⟩ := descend_of_subterm_lift n g (by simp [hv, NBw.subterm])
    have ⟨g', hg'⟩ := descend_of_subterm_lift n' g' (by simp [hv', NBw.subterm])
    rw [hg, ← lift] at hv; rw [lift_injective hv]
    rw [hg', ← lift] at hv'; rw [lift_injective hv']
    exact .E_Iszero (ih hg.symm hg'.symm)
  }
  | E_Iszero_Wrong => exact absurd hv' lift_is_not_wrong
}

theorem wrong_is_deadlock {g : NB.T} (h : lift g ⟶* NBw.T.wrong) : ∃ g', g ⟶* g' ∧ isDeadlock g' := by {
  generalize hv : lift g = v
  rw [hv] at h
  induction h generalizing g with
  | refl => exact absurd hv lift_is_not_wrong
  | step h hs ih => {
    rename_i v' v
    rw [← hv] at h
    cases h with
    | E_IfTrue => {
      have ⟨t', ht', hdl⟩ := ih rfl
      exact ⟨t', .step E_IfTrue ht', hdl⟩
    }
    | E_IfFalse => {
      have ⟨t', ht', hdl⟩ := ih rfl
      exact ⟨t', .step E_IfFalse ht', hdl⟩
    }
    | E_If h => {
      rename_i c _ _
      rcases Classical.em (.wrong ∈ NBw.subterm c) with hc | hc
      {
        have := subterm_wrong_deadlock h hc
        exact ⟨_, .refl, deadlock_If _ _ this⟩
      }
      {
        have ⟨g, hg⟩ := descend_of_nin_wrong hc
        rw [hg, ← lift] at ih
        rw [hg] at h
        have ⟨g', hg', hdl⟩ := ih rfl
        exact ⟨g', .step (.E_If <| eval_descend h) hg', hdl⟩
      }
    }
    | E_If_Wrong h => {
      exact ⟨_, .refl, deadlock_If_nat _ _ h⟩
    }
    | E_Succ h => {
      rename_i n
      rcases Classical.em (.wrong ∈ NBw.subterm n) with hn | hn
      {
        have := subterm_wrong_deadlock h hn
        exact ⟨_, .refl, deadlock_succ this⟩
      }
      {
        have ⟨g, hg⟩ := descend_of_nin_wrong hn
        rw [hg, ← lift] at ih
        rw [hg] at h
        have ⟨g', hg', hdl⟩ := ih rfl
        exact ⟨g', .step (.E_Succ <| eval_descend h) hg', hdl⟩
      }
    }
    | E_Succ_Wrong_True => {
      exact ⟨_, .refl, deadlock_succ_true⟩
    }
    | E_Succ_Wrong_False => {
      exact ⟨_, .refl, deadlock_succ_false⟩
    }
    | E_PredZero => {
      cases hs with | step h => cases h using NBw.eval.casesOn
    }
    | E_PredSucc h => {
      have ⟨t', ht', hdl⟩ := ih rfl
      exact ⟨t', .step (.E_PredSucc h) ht', hdl⟩
    }
    | E_Pred h => {
      rename_i n
      rcases Classical.em (.wrong ∈ NBw.subterm n) with hn | hn
      {
        have := subterm_wrong_deadlock h hn
        exact ⟨_, .refl, deadlock_pred this⟩
      }
      {
        have ⟨g, hg⟩ := descend_of_nin_wrong hn
        rw [hg, ← lift] at ih
        rw [hg] at h
        have ⟨g', hg', hdl⟩ := ih rfl
        exact ⟨g', .step (.E_Pred <| eval_descend h) hg', hdl⟩
      }
    }
    | E_Pred_Wrong_True => {
      exact ⟨_, .refl, deadlock_pred_true⟩
    }
    | E_Pred_Wrong_False => {
      exact ⟨_, .refl, deadlock_pred_false⟩
    }
    | E_IszeroZero => {
      cases hs with | step h => cases h using NBw.eval.casesOn
    }
    | E_IszeroSucc h => {
      cases hs with | step h => cases h using NBw.eval.casesOn
    }
    | E_Iszero h => {
      rename_i n
      rcases Classical.em (.wrong ∈ NBw.subterm n) with hn | hn
      {
        have := subterm_wrong_deadlock h hn
        exact ⟨_, .refl, deadlock_iszero this⟩
      }
      {
        have ⟨g, hg⟩ := descend_of_nin_wrong hn
        rw [hg, ← lift] at ih
        rw [hg] at h
        have ⟨g', hg', hdl⟩ := ih rfl
        exact ⟨g', .step (.E_Iszero <| eval_descend h) hg', hdl⟩
      }
    }
    | E_Iszero_Wrong_True => {
      exact ⟨_, .refl, deadlock_iszero_true⟩
    }
    | E_Iszero_Wrong_False => {
      exact ⟨_, .refl, deadlock_iszero_false⟩
    }
  }
}

end NBw

namespace NBbig -- 演習 3.5.17

abbrev T := NB.T
abbrev isValue := NB.isValue
abbrev isNat := NB.isNat
open NB.T NB.eval MultiStepDeriv

inductive eval : T -> T -> Prop where
  | B_Value {v} : isValue v -> eval v v
  | B_IfTrue {t₁ t₂ v₂ t₃} : isValue v₂ -> eval t₁ true -> eval t₂ v₂ -> eval (If t₁ t₂ t₃) v₂
  | B_IfFalse {t₁ t₂ v₃ t₃} : isValue v₃ -> eval t₁ false -> eval t₃ v₃ -> eval (If t₁ t₂ t₃) v₃
  | B_Succ {t₁ nv₁} : isNat nv₁ -> eval t₁ nv₁ -> eval (succ t₁) (succ nv₁)
  | B_PredZero {t₁} : eval t₁ zero -> eval (pred t₁) zero
  | B_PredSucc {t₁ nv₁} : isNat nv₁ -> eval t₁ (succ nv₁) -> eval (pred t₁) nv₁
  | B_IszeroZero {t₁} : eval t₁ zero -> eval (iszero t₁) true
  | B_IszeroSucc {t₁ nv₁} : isNat nv₁ -> eval t₁ (succ nv₁) -> eval (iszero t₁) false
infix:100 " ⇓ " => eval

/-- 補題 A.6 -/
theorem Es_If {t₁ t₁' t₂ t₃} : t₁ ⟶* t₁' -> If t₁ t₂ t₃ ⟶* If t₁' t₂ t₃ := @inherit NB.T inferInstance (fun t₁ => .If t₁ t₂ t₃) .E_If t₁ t₁'
/-- 補題 A.6 -/
theorem Es_Succ {t₁ t₁'} : t₁ ⟶* t₁' -> succ t₁ ⟶* succ t₁' := @inherit NB.T inferInstance .succ .E_Succ t₁ t₁'
/-- 補題 A.6 -/
theorem Es_Pred {t₁ t₁'} : t₁ ⟶* t₁' -> pred t₁ ⟶* pred t₁' := @inherit NB.T inferInstance .pred .E_Pred t₁ t₁'
/-- 補題 A.6 -/
theorem Es_Iszero {t₁ t₁'} : t₁ ⟶* t₁' -> iszero t₁ ⟶* iszero t₁' := @inherit NB.T inferInstance .iszero .E_Iszero t₁ t₁'

theorem isNat_of_evals_nat {t t' : T} (ht : isNat t) (h : t ⟶* t') : isNat t' := by {
  cases h using MultiStepDeriv.casesOn with
  | refl => exact ht
  | step h _ => exact absurd h (NB.isNormalForm_of_isNat ht _)
}

/-- 命題 A.7 -/
theorem evals_from_big {t v : T} (h : t ⇓ v) : t ⟶* v := by {
  induction h with
  | B_Value hv => exact .refl
  | B_IfTrue hv _ _ ih₁ ih₂ =>
    exact (Es_If ih₁).append <| (MultiStepDeriv.lift NB.eval.E_IfTrue).append ih₂
  | B_IfFalse hv _ _ ih₁ ih₂ =>
    exact (Es_If ih₁).append <| (MultiStepDeriv.lift NB.eval.E_IfFalse).append ih₂
  | B_Succ hvp _ ih => exact Es_Succ ih
  | B_PredZero _ ih => exact (Es_Pred ih).append <| (MultiStepDeriv.lift .E_PredZero)
  | B_PredSucc hvn _ ih =>
    exact (Es_Pred ih).append <| (MultiStepDeriv.lift <| NB.eval.E_PredSucc hvn)
  | B_IszeroZero _ ih =>
    exact (Es_Iszero ih).append <| (MultiStepDeriv.lift NB.eval.E_IszeroZero)
  | B_IszeroSucc hvn _ ih =>
    exact (Es_Iszero ih).append <| (MultiStepDeriv.lift <| .E_IszeroSucc hvn)
}

/-- 命題 A.9 -/
theorem big_from_evals {t v : T} (hv : isValue v) (h : t ⟶* v) : t ⇓ v := by {
  induction h with
  | refl => exact .B_Value hv
  | step h hs ih => {
    induction h generalizing v with
    | E_IfTrue => exact .B_IfTrue hv (.B_Value .true) ih
    | E_IfFalse => exact .B_IfFalse hv (.B_Value .false) ih
    | E_If h ih' => {
      cases ih with
      | B_Value _ => exact absurd hv NB.isValue_not_If
      | B_IfTrue hv' ih₁ ih₂ => {
        have := ih' .true (evals_from_big ih₁) ih₁
        exact .B_IfTrue hv' this ih₂
      }
      | B_IfFalse hv' ih₁ ih₂ => {
        have := ih' .false (evals_from_big ih₁) ih₁
        exact .B_IfFalse hv' this ih₂
      }
    }
    | E_Succ h ih' => {
      cases ih with
      | B_Value _ => {
        rcases hv with _ | _ | ⟨⟨_⟩⟩
        rename_i hv
        have := ih' (NB.isValue_of_isNat hv) .refl (.B_Value (NB.isValue_of_isNat hv))
        exact .B_Succ hv this
      }
      | B_Succ hv' ih => {
        have := ih' (NB.isValue_of_isNat hv') (evals_from_big ih) ih
        exact .B_Succ hv' this
      }
    }
    | E_PredZero => cases ih; exact eval.B_PredZero (.B_Value (.nat .zero))
    | E_PredSucc h => {
      have hv := isNat_of_evals_nat h hs
      exact eval.B_PredSucc hv (.B_Succ hv ih)
    }
    | E_Pred h ih' => {
      cases ih with
      | B_Value _ => exact absurd hv NB.isValue_not_pred
      | B_PredZero => {
        have := ih' (.nat .zero) (evals_from_big (by assumption)) (by assumption)
        exact .B_PredZero this
      }
      | B_PredSucc hv' ih => {
        have := ih' (NB.isValue_of_isNat hv'.succ) (evals_from_big ih) ih
        exact .B_PredSucc hv' this
      }
    }
    | E_IszeroZero => {
      cases hs with
      | refl => exact .B_IszeroZero (.B_Value (.nat .zero))
      | step h => exact absurd h (NB.isNormalForm_of_isValue _ .true _)
    }
    | E_IszeroSucc h => {
      cases hs with
      | refl => exact eval.B_IszeroSucc h (.B_Value (.nat h.succ))
      | step h => exact absurd h (NB.isNormalForm_of_isValue _ .false _)
    }
    | E_Iszero h ih' => {
      cases ih with
      | B_Value _ => exact absurd hv NB.isValue_not_iszero
      | B_IszeroZero => {
        have := ih' (.nat .zero) (evals_from_big (by assumption)) (by assumption)
        exact .B_IszeroZero this
      }
      | B_IszeroSucc hv' ih => {
        have := ih' (NB.isValue_of_isNat hv'.succ) (evals_from_big ih) ih
        exact .B_IszeroSucc hv' this
      }
    }
  }
}

section -- 演習 3.5.18

inductive eval' : T -> T -> Prop
  | B_Value {v} : isValue v -> eval' v v
  | B_IfThen {t₁ t₂ v₂ t₃} : eval' t₂ v₂ -> eval' (If t₁ t₂ t₃) (If t₁ v₂ t₃)
  | B_IfElse {t₁ t₂ v₃ t₃} : eval' t₃ v₃ -> eval' (If t₁ t₂ t₃) (If t₁ t₂ v₃)
  | B_IfTrue {t₁ v₂ v₃} : isValue v₂ -> isValue v₃ -> eval' t₁ .true -> eval' (If t₁ v₂ v₃) v₂
  | B_IfFalse {t₁ v₂ v₃} : isValue v₂ -> isValue v₃ -> eval' t₁ .false -> eval' (If t₁ v₂ v₃) v₃
  | B_Succ {t₁ nv₁} : isNat nv₁ -> eval' t₁ nv₁ -> eval' (succ t₁) (succ nv₁)
  | B_PredZero {t₁} : eval' t₁ zero -> eval' (pred t₁) zero
  | B_PredSucc {t₁ nv₁} : isNat nv₁ -> eval' t₁ (succ nv₁) -> eval' (pred t₁) nv₁
  | B_IszeroZero {t₁} : eval' t₁ zero -> eval' (iszero t₁) true
  | B_IszeroSucc {t₁ nv₁} : isNat nv₁ -> eval' t₁ (succ nv₁) -> eval' (iszero t₁) false

end

end NBbig
