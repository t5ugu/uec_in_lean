namespace FPoLC

-- https://isabelle.in.tum.de/library/HOL/HOL-Proofs-Lambda/document.pdf

inductive dB
  | var : Nat -> dB
  | app : dB -> dB -> dB
  | abs : dB -> dB
infixl:200 " ∘ " => dB.app

/--
  `k` 未満は束縛変数。自由変数は `1` だけ持ち上げる
-/
def lift : dB -> Nat -> dB
  | .var i,   k => if i < k then .var i else .var (i + 1)
  | .app s t, k => lift s k ∘ lift t k
  | .abs s,   k => .abs (lift s (k + 1))

theorem lift_var {i k} : lift (.var i) k = .var (if i < k then i else i + 1) := by {
  unfold lift
  split <;> rfl
}
theorem lift_var_lt {i k} (h : i < k) : lift (.var i) k = .var i := by {
  unfold lift
  rw [if_pos h]
}
theorem lift_var_ge {i k} (h : k ≤ i) : lift (.var i) k = .var (i + 1) := by {
  unfold lift
  rw [if_neg (Nat.not_lt.mpr h)]
}
theorem lift_app (s t : dB) (k : Nat) : lift (s ∘ t) k = lift s k ∘ lift t k := rfl
theorem lift_abs (s : dB) (k : Nat) : lift (.abs s) k = .abs (lift s (k + 1)) := rfl

theorem lift_var_succ {k i} (h : k ≠ i) : lift (.var i) (k + 1) = lift (.var i) k := by {
  rw [lift_var, lift_var]
  rcases Nat.lt_trichotomy k i with l | e | g
  · rw [if_neg (Nat.not_lt.mpr l), if_neg (Nat.not_lt_of_gt l)]
  · contradiction
  · rw [if_pos (Nat.lt_add_right 1 g), if_pos g]
}

/--
  `k` 未満は束縛変数。自由変数は `n` だけ持ち上げる
-/
def liftn : Nat -> dB -> Nat -> dB
  | n, .var i,   k => if i < k then .var i else .var (i + n)
  | n, .app s t, k => liftn n s k ∘ liftn n t k
  | n, .abs s,   k => .abs (liftn n s (k + 1))

theorem liftn_zero (k : Nat) (t : dB) : liftn 0 t k = t := by {
  unfold liftn
  cases t
  case var i => simp
  case app s t => simp [liftn_zero k s, liftn_zero k t]
  case abs s => simp [liftn_zero (k + 1) s]
}

/-- `k` 番目のラムダ抽象をほどいて `s` にする -/
def subst : dB -> dB -> Nat -> dB
  | .var i,   s, k => if k < i then .var (i - 1)
    else if i = k then s
    else .var i
  | .app t u, s, k => subst t s k ∘ subst u s k
  | .abs t,   s, k => .abs (subst t (lift s 0) (k + 1))
notation:300 t:300 " [" s:0 " ⧸ " k:0 "]" => subst t s k

theorem subst_var {i k} (s : dB) : (.var i) [s ⧸ k] = if k < i then .var (i - 1) else if i = k then s else .var i := rfl
theorem subst_app (s t : dB) (k : Nat) (u : dB) : (s ∘ t) [u ⧸ k] = (s [u ⧸ k]) ∘ (t [u ⧸ k]) := rfl
theorem subst_abs (s : dB) (k : Nat) (u : dB) : (.abs s) [u ⧸ k] = .abs (s [(lift u 0) ⧸ (k + 1)]) := rfl

theorem subst_congr_before {s t u : dB} (h : s = t) (k : Nat) : s [u ⧸ k] = t [u ⧸ k] := by rw [h]
theorem subst_congr_after {s t u : dB} (h : s = t) (k : Nat) : u [s ⧸ k] = u [t ⧸ k] := by rw [h]


def substn : dB -> dB -> Nat -> dB
  | .var i,   s, k => if k < i then .var (i - 1)
    else if i = k then liftn k s 0
    else .var i
  | .app t u, s, k => substn t s k ∘ substn u s k
  | .abs t,   s, k => .abs (substn t s (k + 1))

inductive beta : dB -> dB -> Prop
  | mk (s t : dB) : beta (.abs (s ∘ t)) (s [t ⧸ 0])
  | appL {s t : dB} (u : dB) (sβt : beta s t) : beta (s ∘ u) (t ∘ u)
  | appR {s t : dB} (u : dB) (sβt : beta s t) : beta (u ∘ s) (u ∘ t)
  | abs {s t : dB} (sβt : beta s t) : beta (.abs s) (.abs t)
infixl:50 " →β " => beta

inductive beta_reds (s : dB) : dB -> Prop
  | refl : beta_reds s s
  | step {t u : dB} (sβt : beta_reds s t) (tβu : beta t u) : beta_reds s u
infixl:50 " →β* " => beta_reds

def id : dB := .abs (.var 0)

theorem beta_abs {s s' : dB} (h : s →β* s') : .abs s →β* .abs s' := by {
  induction h with
  | refl        => exact .refl
  | step _ h ih => exact .step ih (.abs h)
}

theorem beta_appL {s s' : dB} (t : dB) (h : s →β* s') : s ∘ t →β* s' ∘ t := by {
  induction h with
  | refl        => exact .refl
  | step _ h ih => exact .step ih (.appL t h)
}

theorem beta_appR (s : dB) {t t' : dB} (h : t →β* t') : s ∘ t →β* s ∘ t' := by {
  induction h with
  | refl        => exact .refl
  | step _ h ih => exact .step ih (.appR s h)
}

theorem beta_app {s s' t t' : dB} (hs : s →β* s') (ht : t →β* t') : s ∘ t →β* s' ∘ t' := by {
  induction hs with
  | refl        => exact beta_appR s ht
  | step _ h ih => exact .step ih (.appL t' h)
}

theorem subst_eq {k u} : (.var k) [u ⧸ k] = u := by {
  unfold subst
  simp
}

theorem subst_gt {i j u} (h : i < j) : (.var j) [u ⧸ i] = .var (j - 1) := by {
  unfold subst
  rw [if_pos h]
}

theorem subst_lt {i j u} (h : j < i) : (.var j) [u ⧸ i] = .var j := by {
  unfold subst
  rw [if_neg (Nat.not_lt_of_gt h), if_neg (Nat.ne_of_lt h)]
}

theorem lift_lift {i k} (t) (h : i < k + 1) : lift (lift t i) (k + 1) = lift (lift t k) i := by {
  cases t
  case var j =>
    unfold lift
    rw [lift_var, lift_var]
    simp
    split
    · rw [if_pos (Nat.lt_trans (by assumption) h)]
      split
      · rfl
      · have : j < k := Nat.lt_of_lt_of_le (by assumption) (Nat.lt_add_one_iff.mp h)
        contradiction
    · split
      · split
        · rfl
        · split
          · rfl
          · simp_all
      · split
        · have : ¬(j < k) := by simp_all
          contradiction
        · split
          · have : j + 1 < k + 1 := Nat.lt_trans (by assumption) h
            contradiction
          · rfl
  case app s t =>
    unfold lift
    rw [lift_app, lift_app]
    simp only
    rw [lift_lift s h, lift_lift t h]
  case abs s =>
    unfold lift
    rw [lift_abs, lift_abs]
    simp only
    rw [lift_lift s (Nat.add_lt_add_right h 1)]
}

theorem lift_subst {i j s t} (h : j < i + 1) : lift (t [s ⧸ j]) i = (lift t (i + 1)) [lift s i ⧸ j] := by {
  cases t
  case var k =>
    rcases Nat.lt_trichotomy j k with ⟨hjk⟩ | ⟨hjk⟩ | ⟨hjk⟩
    · rw [subst_gt hjk]
      rcases Nat.lt_trichotomy (k - 1) i with ⟨hki⟩ | ⟨hki⟩ | ⟨hki⟩
      · rw [lift_var_lt hki]
        have : k < i + 1 := by {
          rw [← @Nat.sub_add_cancel k 1 (Nat.one_le_of_lt hjk)]
          exact Nat.add_le_add_right hki 1
        }
        rw [lift_var_lt this, subst_gt hjk]
      · subst hki
        rw [lift_var_ge (Nat.le_refl _), Nat.sub_add_cancel (Nat.one_le_of_lt hjk), lift_var_ge (Nat.le_refl _), subst_gt (Nat.lt_add_right 1 hjk), Nat.add_sub_cancel]
      · rw [lift_var_ge (Nat.le_of_succ_le hki)]
        have : k ≥ i + 1 := by {
          rw [← @Nat.sub_add_cancel k 1 (Nat.one_le_of_lt hjk)]
          exact Nat.le_add_right_of_le hki
        }
        rw [lift_var_ge this, subst_gt (Nat.lt_add_right 1 hjk), Nat.sub_add_cancel (Nat.one_le_of_lt hjk), Nat.add_sub_cancel]
    · subst hjk
      rw [subst_eq, lift_var_lt h, subst_eq]
    · rw [subst_lt hjk, lift_var_lt (Nat.le_trans hjk (Nat.le_of_lt_succ h)), lift_var_lt (Nat.lt_trans hjk h), subst_lt hjk]
  case app => simp only [subst_app, lift_app, lift_subst h]
  case abs =>
    rw [subst_abs, lift_abs, lift_abs, subst_abs, lift_subst (Nat.add_lt_add_right h 1), dB.abs.injEq]
    exact subst_congr_after (lift_lift _ (Nat.zero_lt_succ i)) (j + 1)
}

