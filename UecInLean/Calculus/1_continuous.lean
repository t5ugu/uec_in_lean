import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import UecInLean.Calculus.List_max

open Set
namespace UEC.Calculus

-- 開区間 (a, b) は `Ioo a b`
-- 閉区間 [a, b] は `Icc a b`
-- などと書く

def ConvergesTo (a : ℕ → ℝ) (α : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - α| < ε
notation:80 a:max " n⟶ " α:max => ConvergesTo a α

abbrev non_decreasing (u : ℕ → ℝ) := ∀ {m n}, m ≤ n → u m ≤ u n
abbrev non_increasing (u : ℕ → ℝ) := ∀ {m n}, m ≤ n → u m ≥ u n

def isUpperBound (u : ℕ → ℝ) (M : ℝ) := ∀ n, u n ≤ M
def isLowerBound (u : ℕ → ℝ) (m : ℝ) := ∀ n, m ≤ u n
def isBound (u : ℕ → ℝ) (K : ℝ) := ∀ n, |u n| ≤ K

theorem isBound_nonneg {u M} (hM : isBound u M) : 0 ≤ M := by {
  apply le_trans' (hM 0)
  exact abs_nonneg (u 0)
}

lemma isBound_zero_or_pos {u M} (hM : isBound u M) : M = 0 ∨ M > 0 := by {
  rw [Eq.comm, ← le_iff_eq_or_lt]
  exact isBound_nonneg hM
}

theorem isBound_of_Upper_Lower {u M m K} (hK : max |M| |m| ≤ K)  : isUpperBound u M → isLowerBound u m → isBound u K := by {
  intro hM hm n
  rw [abs_le]
  constructor
  {
    rw [← neg_neg (u n), neg_le_neg_iff]
    -- -u n ≤ -m ≤ |m| ≤ max |M| |m| ≤ K
    apply (neg_le_neg (hm n)).trans <| (neg_le_abs _).trans <| (le_max_right _ _).trans hK
  }
  { -- u n ≤ M ≤ |M| ≤ max |M| |m| ≤ K
    exact (hM n).trans <| (le_abs_self _).trans <| (le_max_left _ _).trans hK
  }
}

theorem isBound_zero {u : ℕ → ℝ} : isBound u 0 ↔ ∀ n, u n = 0 := by {
  constructor
  · intro h n
    unfold isBound at h
    have := h n
    rw [abs_nonpos_iff] at this
    assumption
  · intro h n
    rw [h n, abs_zero]
}

def isSup (u : ℕ → ℝ) (M : ℝ) := isUpperBound u M ∧ ∀ ε > 0, ∃ n, M - u n < ε
def isInf (u : ℕ → ℝ) (m : ℝ) := isLowerBound u m ∧ ∀ ε > 0, ∃ n, u n - m < ε
inductive bounded (u : ℕ → ℝ) : Prop where
  | mk (M₀ : ℝ) (bd : isBound u M₀) -- (sup : ∀ M, isBound u M → M₀ ≤ M)

theorem bounded_abs {u} : bounded u → bounded (fun n => |u n|) := by {
  intro ⟨M₀, bdd ,/-sup-/⟩
  use M₀
  · intro n
    rw [abs_abs]
    exact bdd n
  -- · intro M ordM
  --   simp only [isBound, abs_abs] at ordM
  --   exact sup M ordM
}

lemma abs_lt_of_nonneg_lt {a b : ℝ} (hnn : 0 ≤ a) (hlt : a < b) : |a| < b := by {
  rw [abs_of_nonneg hnn]
  exact hlt
}

/-- 単調収束定理 -/
theorem ConvergesTo_of_mono_nondecr {a α} : isSup a α → non_decreasing a → a n⟶ α := by {
  intro ⟨ord, met⟩ nd ε hε
  have ⟨N, hN⟩ := met ε hε
  use N
  intro n hn
  rw [abs_sub_comm]
  apply abs_lt_of_nonneg_lt (sub_nonneg.mpr (ord n))
  exact (sub_le_sub_left (nd (GE.ge.le hn)) α).trans_lt hN
}

theorem ConvergesTo.bounded {a α} (h : a n⟶ α) : bounded a := by {
  let ε : ℝ := 1
  rcases h ε one_pos with ⟨N, hN⟩
  use max (|α| + ε) ((List.map (fun n => |a n|) (List.range N)).max?.getD 0)
  { -- 有界性
    intro n
    rcases Nat.lt_or_ge n N with hnN | hnN
    · apply le_max_of_le_right
      induction N with
      | zero => contradiction
      | succ N ih => {
        apply List.le_max?_getD_of_mem'
        rw [List.mem_map]
        use n
        rw [List.mem_range]
        exact ⟨hnN, by rfl⟩
      }
    · apply le_max_of_le_left
      apply le_add_of_sub_left_le
      calc
        |a n| - |α| ≤ |a n - α| := abs_sub_abs_le_abs_sub _ _
        _ ≤ ε := le_of_lt <| hN n hnN
  }
  /-
  { -- 最小性
    intro M bdd
    rw [max_le_iff]
    constructor
    · sorry
    · apply List.max?_getD_le_of_each_le
      {
        intro x hx
        rw [List.mem_map] at hx
        rcases hx with ⟨n, hn, hx⟩
        rw [← hx]
        apply bdd
      }
      {
        exact isBound_nonneg bdd
      }
  }
  -/
}

theorem ConvergesTo_synonym.Pscaled_ε {a α k} (hk : k > 0) : (∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - α| < k * ε) ↔ a n⟶ α := by {
  constructor
  · intro h ε hε
    rcases h (ε / k) (div_pos hε hk) with ⟨N, hN⟩
    use N
    intro n hn
    rw [← mul_div_cancel₀ ε (ne_of_gt hk)]
    exact hN n hn
  · intro h ε hε
    rcases h (k * ε) (mul_pos hk hε) with ⟨N, hN⟩
    use N
}

theorem ConvergesTo_synonym.abs_le_ε {a α} : (∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - α| ≤ ε) ↔ a n⟶ α := by {
  constructor
  · intro h ε hε
    rcases h (ε/2) (by linarith) with ⟨N, hN⟩
    use N
    intro n hn
    exact (hN n hn).trans_lt (by linarith)
  · intro h ε hε
    rcases h ε hε with ⟨N, hN⟩
    use N
    intro n hn
    exact le_of_lt (hN n hn)
}

theorem ConvergesTo_synonym.ranged_ε {a α l} (hl : l > 0) : (∀ ε, 0 < ε → ε < l → ∃ N, ∀ n ≥ N, |a n - α| < ε) ↔ a n⟶ α := by {
  constructor
  · intro h ε hε
    rcases lt_or_ge ε l with hεl | hεl
    · exact h ε hε hεl
    · rcases h (l/2) (by linarith) (by linarith) with ⟨N, hN⟩
      use N
      intro n hn
      apply lt_trans (hN n hn)
      rcases eq_or_lt_of_le hεl with hεl | hεl
      · rw [hεl]
        exact div_two_lt_of_pos hε
      · exact (div_two_lt_of_pos hl).trans hεl
  · intro h ε hε _
    rcases h ε hε with ⟨N, hN⟩
    use N
}

theorem ConvergesTo_synonym.shifted {a α} (N : ℕ) : (fun n => a (n + N)) n⟶ α ↔ a n⟶ α := by {
  constructor
  {
    intro h ε hε
    have ⟨N₀, hN₀⟩ := h ε hε
    use N₀ + N
    intro n hn
    have := hN₀ (n - N) (Nat.le_sub_of_add_le hn)
    simp only at this
    rw [Nat.sub_add_cancel (le_of_add_le_right hn)] at this
    exact this
  }
  {
    intro h ε hε
    have ⟨N₀, hN₀⟩ := h ε hε
    use N₀
    intro n hn
    exact hN₀ (n + N) (Nat.le_add_right_of_le hn)
  }
}

theorem ConvergesTo_zero {a α} : (fun n => a n - α) n⟶ 0 ↔ a n⟶ α := by {
  constructor <;> {
    intro h ε hε
    rcases h ε hε with ⟨N, hN⟩
    use N
    intro n hn
    simp only [sub_zero] at hN ⊢
    exact hN n hn
  }
}

theorem Converges_inv : (fun n => 1 / (n : ℝ)) n⟶ 0 := by {
  intro ε hε
  use ⌈1 / ε⌉₊ + 1
  intro n hn
  have npos : 0 < (n : ℝ) := by {
    rw [Nat.cast_pos]
    apply Nat.le_trans _ hn
    exact Nat.le_add_left 1 ⌈1 / ε⌉₊
  }
  rw [sub_zero, abs_one_div, Nat.abs_cast, one_div_lt npos hε]
  exact Nat.lt_of_ceil_lt hn
}

theorem ConvergesTo_const (α : ℝ) : (fun _ => α) n⟶ α := by {
  intro _ h
  use 0
  intros
  rw [sub_self, abs_zero]
  exact h
}

theorem ConvergesTo_subst {a b α} (h : ∀ n, a n = b n) (ha : a n⟶ α) : b n⟶ α := by {
  intro ε hε
  rcases ha ε hε with ⟨N, hN⟩
  use N
  intro n hn
  rw [← h n]
  exact hN n hn
}

theorem ConvergesTo_eq {a α β} (ha : a n⟶ α) (h : α = β) : (a n⟶ β) := by {
  rw [← h]
  exact ha
}

theorem ConvergesTo_unique {a α β} (ha : a n⟶ α) (hb : a n⟶ β) : α = β := by {
  apply eq_of_abs_sub_lt_all
  intro ε hε
  have := ha ε hε
  have ⟨Na, hNa⟩ := ha (ε/2) (by linarith)
  have ⟨Nb, hNb⟩ := hb (ε/2) (by linarith)
  calc
    |α - β|
    _ = |(α - a (max Na Nb)) + (a (max Na Nb) - β)| := by ring_nf
    _ ≤ |α - a (max Na Nb)| + |a (max Na Nb) - β| := abs_add_le _ _
    _ = |a (max Na Nb) - α| + |a (max Na Nb) - β| := by rw [abs_sub_comm]
    _ < ε / 2 + ε / 2 := by linarith [hNa (max Na Nb) (le_max_left Na Nb), hNb (max Na Nb) (le_max_right Na Nb)]
    _ = ε := by ring
}

theorem ConvergesTo_neg {a α} : a n⟶ α -> (fun n => -a n) n⟶ (-α) := by {
  intro h ε hε
  rcases h ε hε with ⟨N, hN⟩
  use N
  intro n hn
  calc
    |-a n - -α|
    _ = |-(a n - α)| := by ring_nf
    _ = |a n - α| := abs_neg _
    _ < ε := hN n hn
}

lemma ConvergesTo_of_neg {a α} : (fun n => -a n) n⟶ (-α) → a n⟶ α := by {
  intro h
  rw [← neg_neg a, ← neg_neg α]
  exact ConvergesTo_neg h
}

lemma ConvergesTo_zero_neg {a} (ha : a n⟶ 0) : (fun n => -a n) n⟶ 0 := by {
  rw [← neg_zero]
  exact ConvergesTo_neg ha
}

/-- Thm. 1.1.1 (1) + -/
theorem ConvergesTo_add {a b α β} (ha : a n⟶ α) (hb : b n⟶ β) : (a + b) n⟶ (α + β) := by {
  intro ε hε
  rcases ha (ε / 2) (by linarith) with ⟨Na, hNa⟩
  rcases hb (ε / 2) (by linarith) with ⟨Nb, hNb⟩
  use max Na Nb
  intro n hn
  calc
    |a n + b n - (α + β)|
    _ = |a n - α + (b n - β)| := by ring_nf
    _ ≤ |a n - α| + |b n - β| := abs_add_le _ _
    _ < ε := by linarith [hNa n (le_of_max_le_left hn), hNb n (le_of_max_le_right hn)]
}

lemma ConvergesTo_zero_add {a b} (ha : a n⟶ 0) (hb : b n⟶ 0) : (a + b) n⟶ 0 := by {
  rw [← zero_add 0]
  apply ConvergesTo_add ha hb
}

/-- Thm. 1.1.1 (1) - -/
lemma ConvergesTo_sub {a b α β} (ha : a n⟶ α) (hb : b n⟶ β) : (a - b) n⟶ (α - β) := by {
  simp only [sub_eq_add_neg]
  exact ConvergesTo_add ha (ConvergesTo_neg hb)
}

theorem ConvergesTo_Pscalar {a α c} (h : a n⟶ α) (hc : c > 0) : (fun n => c * a n) n⟶ (c * α) := by {
  intro ε hε
  rcases h (ε/c) (by aesop) with ⟨N, hN⟩
  use N
  intro n hn
  calc
    |c * a n - c * α|
    _ = |c * (a n - α)| := by ring_nf
    _ = |c| * |a n - α| := abs_mul _ _
    _ = c * |a n - α| := by rw [abs_of_pos hc]
    _ < ε := (lt_div_iff₀' hc).mp (hN n hn)
}

/-- Thm. 1.1.1 (2) -/
lemma ConvergesTo_scaler {a α} (c) (h : a n⟶ α) : (fun n => c * a n) n⟶ (c * α) := by {
  rcases Real.nnreal_trichotomy c with ⟨hc⟩ | ⟨⟨x, ⟨hx, ⟨hcp⟩ | ⟨hcn⟩⟩⟩⟩
  · rw [hc]
    simp only [zero_mul] -- 無名関数内でもrw
    exact ConvergesTo_const 0
  · rw [hcp]
    exact ConvergesTo_Pscalar h hx
  · rw [hcn]
    simp only [neg_mul] -- 無名関数内でもrw
    exact ConvergesTo_neg (ConvergesTo_Pscalar h hx)
}

lemma ConvergesTo_zero_scaler {a c} (ha : a n⟶ 0) : (fun n => c * a n) n⟶ 0 := by {
  rw [← mul_zero c]
  apply ConvergesTo_scaler c ha
}

theorem ConvergesTo_squeeze {a b c α} (ha : a n⟶ α) (hb : b n⟶ α) (h : ∀ n, a n ≤ c n ∧ c n ≤ b n) : c n⟶ α := by {
  intro ε hε
  rcases ha ε hε with ⟨Na, hNa⟩
  rcases hb ε hε with ⟨Nb, hNb⟩
  use max Na Nb
  intro n hn
  have ⟨hac, hcb⟩ := h n
  rcases lt_or_eq_of_le hac with hac | hac
  rcases lt_or_eq_of_le hcb with hcb | hcb
  · rw [abs_lt]
    constructor -- -ε < a n - α < c n - α < b n - α < ε
    · apply lt_trans (abs_lt.mp (hNa n (le_of_max_le_left hn))).1 (sub_lt_sub_right hac α)
    · apply lt_trans (sub_lt_sub_right hcb α) (abs_lt.mp (hNb n (le_of_max_le_right hn))).2
  · rw [hcb]
    exact hNb n (le_of_max_le_right hn)
  · rw [← hac]
    exact hNa n (le_of_max_le_left hn)
}

theorem ConvergesTo_abs {a α} : a n⟶ α → (fun n => |a n|) n⟶ |α| := by {
  intro h ε hε
  rcases h ε hε with ⟨N, hN⟩
  use N
  intro n hn
  exact (abs_abs_sub_abs_le (a n) α).trans_lt (hN n hn)
}

theorem ConvergesTo_zero_abs {a} : a n⟶ 0 ↔ (fun n => |a n|) n⟶ 0 := by {
  constructor <;> {
    intro h ε hε
    rcases h ε hε with ⟨N, hN⟩
    use N
    intro n hn
    simp only [sub_zero, abs_abs] at hN ⊢
    exact hN n hn
  }
}

theorem ConvergesTo_abs_squeeze {a b : ℕ → ℝ} (h : ∀ n, |a n| ≤ b n) (hb : b n⟶ 0) : a n⟶ 0 := by {
  apply ConvergesTo_squeeze (ConvergesTo_zero_neg hb) hb
  intro n
  rw [← abs_le]
  exact h n
}

theorem ConvergesTo_zero_bounded_mul {a b} (ha : bounded a) (hb : b n⟶ 0) : (fun n => a n * b n) n⟶ 0 := by {
  have ⟨M, hMa⟩ := ha
  apply ConvergesTo_abs_squeeze
  {
    intro n
    calc
      |a n * b n|
      _ = |a n| * |b n| := abs_mul _ _
      _ ≤ M * |b n| := mul_le_mul_of_nonneg_right (hMa n) (abs_nonneg _)
  }
  apply ConvergesTo_zero_scaler
  rw [← ConvergesTo_zero_abs]
  exact hb
}

theorem ConvergesTo_mul {a b α β} (ha : a n⟶ α) (hb : b n⟶ β) : (a * b) n⟶ (α * β) := by {
  rw [← ConvergesTo_zero]
  apply ConvergesTo_abs_squeeze
  {
    intro n
    calc
      |a n * b n - (α * β)|
      _ = |a n * (b n - β) + β * (a n - α)| := by ring_nf
      _ ≤ |a n * (b n - β)| + |β * (a n - α)| := by simp only [abs_abs, abs_add_le]
      _ = |a n| * |b n - β| + |β| * |a n - α| := by simp only [abs_mul]
  }
  apply ConvergesTo_zero_add
  · apply ConvergesTo_zero_bounded_mul (bounded_abs ha.bounded)
    rw [← ConvergesTo_zero_abs, ConvergesTo_zero]
    exact hb
  · apply ConvergesTo_zero_scaler
    rw [← ConvergesTo_zero_abs, ConvergesTo_zero]
    exact ha
}

lemma bound_pos_of_ConvergesTo_nonzero {a α} (ha : a n⟶ α) (hα : α ≠ 0) : ∃ M > 0, isBound a M := by {
  rcases ha.bounded with ⟨M, hM⟩
  have hMpos : M > 0 := by {
    rcases isBound_zero_or_pos hM with hMz | hMp
    { -- M = 0
      by_contra
      rw [hMz, isBound_zero] at hM
      have ⟨N, hN⟩ := ha |α| (lt_of_le_of_ne' (abs_nonneg _) (abs_ne_zero.mpr hα))
      have := hN N (le_refl _)
      rw [hM N, abs_sub_comm, sub_zero, lt_self_iff_false] at this
      exact this
    }
    exact hMp
  }
  use M, hMpos
}

theorem pos_inf {a α} (ha : a n⟶ α) (hα : α > 0) : ∃ N, ∀ n ≥ N, a n > (α / 2) := by {
  have ⟨N, hN⟩ := ha (α / 2) (by linarith)
  use N
  intro n hn
  linarith [abs_lt.mp <| hN n hn]
}

theorem ConvergesTo_inv_pos {a α} (ha : a n⟶ α) (hα : α > 0) : (fun n => 1 / a n) n⟶ (1 / α) := by {
  have ⟨Nm, hNm⟩ := pos_inf ha hα
  intro ε hε
  have ⟨Na, hNa⟩ := ha (ε * (α^2 / 2)) (mul_pos hε (div_pos (pow_pos hα 2) two_pos))
  use max Na Nm
  intro n hn
  simp only
  have han : a n > 0 := (div_pos hα two_pos).trans (hNm n (le_of_max_le_right hn))
  rw [div_sub_div _ _ (ne_of_gt han) (ne_of_gt hα), one_mul, mul_one, abs_div, abs_sub_comm,
    div_lt_iff₀ (abs_pos_of_pos <| mul_pos han hα), abs_mul, abs_of_pos han, abs_of_pos hα]
  apply lt_trans (hNa n (le_of_max_le_left hn))
  rw [mul_lt_mul_left hε, pow_two, mul_div_right_comm, mul_lt_mul_right hα]
  exact hNm n (le_of_max_le_right hn)
}

theorem ConvergesTo_inv {a α} (ha : a n⟶ α) (hα : α ≠ 0) : (fun n => 1 / a n) n⟶ (1 / α) := by {
  rw [ne_iff_lt_or_gt] at hα
  rcases hα with hα | hα
  {
    apply ConvergesTo_of_neg
    rw [← div_neg_eq_neg_div]
    conv => arg 1; intro; rw [← div_neg_eq_neg_div]
    exact ConvergesTo_inv_pos (ConvergesTo_neg ha) (neg_pos_of_neg hα)
  }
  exact ConvergesTo_inv_pos ha hα
}

theorem ConvergesTo_div {a b α β} (ha : a n⟶ α) (hb : b n⟶ β) (hβ : β ≠ 0) : (fun n => a n / b n) n⟶ (α / β) := by {
  rw [div_eq_mul_one_div]
  conv => arg 1; intro; rw [div_eq_mul_one_div]
  exact ConvergesTo_mul ha (ConvergesTo_inv hb hβ)
}

#check (1 : ℝ)⁻¹

-- C:\Users\n2513152\uec\uec_in_lean\.lake\packages\mathlib\Mathlib\Analysis\Calculus\MeanValue.lean
#check inv_zero
