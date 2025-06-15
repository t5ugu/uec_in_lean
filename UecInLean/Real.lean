namespace UEC

-- https://wiis.info/math/real-number/definition-of-real-number/ordered-field-of-real-number/
universe u

/--
  逆元を取れるクラス
  @see Mathlib.Algebra.Notation.Defs
-/
class Inv (α : Type u) where
  /-- ある `α` の元の逆元 `a⁻¹` -/
  inv : α → α

@[inherit_doc]
postfix:max "⁻¹" => Inv.inv

class TotallyOrderedField (R : Type) extends Add R, Zero R, Neg R, Mul R, One R, Inv R, LE R where
  add_assoc (x y z : R) : x + (y + z) = x + y + z
  add_zero (x : R) : x + 0 = x
  add_neg (x : R) : x + -x = 0
  add_comm (x y : R) : x + y = y + x

  one_ne_zero : (1 : R) ≠ 0

  mul_assoc (x y z : R) : x * (y * z) = x * y * z
  mul_one (x : R) : x * 1 = x
  mul_inv_cancel {x : R} (_ : x ≠ 0) : x * x⁻¹ = 1
  mul_comm (x y : R) : x * y = y * x
  add_mul (x y z : R) : (x + y) * z = x * z + y * z

  le_refl (x : R) : x ≤ x
  le_antisymm (x y : R) : x ≤ y → y ≤ x → x = y
  le_trans (x y z : R) : x ≤ y → y ≤ z → x ≤ z
  le_total (x y : R) : x ≤ y ∨ y ≤ x

  add_le_add_right (x y z : R) : x ≤ y → x + z ≤ y + z
  mul_nonneg (x y : R) : 0 ≤ x → 0 ≤ y → 0 ≤ x * y

-- なんか `Real` というモノが存在していて、どうやら完全順序体らしい。
axiom Real : Type
axiom Real.inst : TotallyOrderedField Real

namespace Real
noncomputable instance instTotallyOrderedField : TotallyOrderedField Real := inst
notation "ℝ" => Real

theorem add_assoc (x y z : ℝ) : x + (y + z) = x + y + z := inst.add_assoc x y z
theorem add_zero (x : ℝ) : x + 0 = x := inst.add_zero x
theorem add_neg (x : ℝ) : x + -x = 0 := inst.add_neg x
theorem add_comm (x y : ℝ) : x + y = y + x := inst.add_comm x y
theorem mul_assoc (x y z : ℝ) : x * (y * z) = x * y * z := inst.mul_assoc x y z
theorem one_ne_zero : (1 : ℝ) ≠ 0 := inst.one_ne_zero
theorem mul_one (x : ℝ) : x * 1 = x := inst.mul_one x
theorem mul_inv_cancel {x : ℝ} (hx : x ≠ 0) : x * x⁻¹ = 1 := inst.mul_inv_cancel hx
theorem mul_comm (x y : ℝ) : x * y = y * x := inst.mul_comm x y
theorem add_mul (x y z : ℝ) : (x + y) * z = x * z + y * z := inst.add_mul x y z
theorem le_refl (x : ℝ) : x ≤ x := inst.le_refl x
theorem le_antisymm {x y : ℝ} : x ≤ y → y ≤ x → x = y := inst.le_antisymm x y
theorem le_trans {x y z : ℝ} : x ≤ y → y ≤ z → x ≤ z := inst.le_trans x y z
theorem le_total (x y : ℝ) : x ≤ y ∨ y ≤ x := inst.le_total x y
theorem add_le_add_right {x y} (h : x ≤ y) (z : ℝ) : x + z ≤ y + z := inst.add_le_add_right x y z h
theorem mul_nonneg {x y : ℝ} : 0 ≤ x → 0 ≤ y → 0 ≤ x * y := inst.mul_nonneg x y

theorem zero_add (x : ℝ) : 0 + x = x := by rw [add_comm, add_zero]
theorem neg_add (x : ℝ) : -x + x = 0 := by rw [add_comm, add_neg]
theorem one_mul (x : ℝ) : 1 * x = x := by rw [mul_comm, mul_one]
theorem inv_mul {x : ℝ} (hx : x ≠ 0) : x⁻¹ * x = 1 := by rw [mul_comm, mul_inv_cancel hx]
theorem mul_add (x y z : ℝ) : x * (y + z) = x * y + x * z := by rw [mul_comm, add_mul, mul_comm x y, mul_comm x z]
theorem add_le_add_left {x y : ℝ} (z) : x ≤ y → z + x ≤ z + y := by {
  intro h
  rw [add_comm z x, add_comm z y]
  exact add_le_add_right h z
}

theorem neg_eq_comm (x y : ℝ) : -x = y ↔ x = -y := by {
  constructor
  · intro h
    rw [← add_zero x, ← add_neg (-x), add_assoc, add_neg, zero_add, h]
  · intro h
    rw [← add_zero y, ← add_neg (-y), add_assoc, add_neg, zero_add, h]
}

theorem neg_neg (x : ℝ) : -(-x) = x := by rw [neg_eq_comm]

theorem add_left_cancel (x) {y z : ℝ} : x + y = x + z ↔ y = z := by {
  constructor
  · intro h
    rw [← zero_add y, ← neg_add x, ← add_assoc, h, add_assoc, neg_add, zero_add]
  · intro h
    rw [h]
}

theorem add_right_cancel {x y} (z : ℝ) : x + z = y + z ↔ x = y := by {
  constructor
  · intro h
    rw [← add_left_cancel z, add_comm, h, add_comm]
  · intro h
    rw [h]
}

theorem mul_zero (x : ℝ) : x * 0 = 0 := by {
  rw [← add_right_cancel x, zero_add]
  conv => lhs; arg 2; rw [← mul_one x]
  rw [← mul_add, zero_add, mul_one]
}

theorem zero_mul (x : ℝ) : 0 * x = 0 := by {
  rw [mul_comm, mul_zero]
}

theorem neg_mul {x y : ℝ} : -x * y = -(x * y) := by {
  rw [← add_right_cancel (x * y), neg_add, ← add_mul, neg_add, zero_mul]
}

theorem mul_neg {x y : ℝ} : x * -y = -(x * y) := by {
  rw [mul_comm, neg_mul, mul_comm]
}

theorem neg_mul_neg {x y : ℝ} : -x * -y = x * y := by {
  rw [neg_mul, mul_neg, neg_neg]
}

noncomputable def sub (x y : ℝ) := x + -y
noncomputable instance : Sub ℝ := ⟨sub⟩
theorem sub_eq_add_neg (x y : ℝ) : x - y = x + -y := rfl

theorem neg_zero : (-0 : ℝ) = 0 := by {
  rw [← add_left_cancel 0, add_neg, add_zero]
}

theorem sub_zero (x : ℝ) : x - 0 = x := by {
  rw [sub_eq_add_neg, neg_zero, add_zero]
}

theorem neg_eq_zero (x : ℝ) : -x = 0 ↔ x = 0 := by {
  constructor
  · intro h
    rw [neg_eq_comm] at h
    rw [h, neg_zero]
  · intro h
    rw [h, neg_zero]
}

theorem sub_mul {x y z : ℝ} : (x - y) * z = x * z - y * z := by {
  rw [sub_eq_add_neg, add_mul, neg_mul, sub_eq_add_neg]
}

theorem mul_sub {x y z : ℝ} : x * (y - z) = x * y - x * z := by {
  rw [mul_comm, sub_mul, mul_comm y x, mul_comm z x]
}

noncomputable def div (x y : ℝ) := x * y⁻¹
noncomputable instance : Div ℝ := ⟨div⟩
theorem div_eq_mul_inv (x y : ℝ) : x / y = x * y⁻¹ := rfl

structure lt (x y : ℝ) where
  le : x ≤ y
  ne : x ≠ y
instance : LT ℝ := ⟨lt⟩

theorem lt_self_contra {x : ℝ} : x < x → False := by {
  intro h
  exact h.ne (le_antisymm h.le h.le)
}

theorem lt_ge_contra {x y : ℝ} : x < y → x ≥ y → False := by {
  intro h₁ h₂
  exact h₁.ne (le_antisymm h₁.le h₂)
}

theorem lt_asymm {x y : ℝ} : x < y → ¬(y < x) := by {
  intro h₁ h₂
  exact h₁.ne (le_antisymm h₁.le h₂.le)
}

theorem lt_trans {x y z : ℝ} : x < y → y < z → x < z := by {
  intro h₁ ⟨h₂le, _⟩
  constructor
  · exact le_trans h₁.le h₂le
  · intro h
    rw [← h] at h₂le
    exact h₁.ne (le_antisymm h₁.le h₂le)
}

theorem lt_trans_le {x y z : ℝ} : x < y → y ≤ z → x < z := by {
  intro h₁ h₂
  constructor
  · exact le_trans h₁.le h₂
  · intro hz
    rw [← hz] at h₂
    exact lt_ge_contra h₁ h₂
}

theorem le_trans_lt {x y z : ℝ} : x ≤ y → y < z → x < z := by {
  intro h₁ h₂
  constructor
  · exact le_trans h₁ h₂.le
  · intro hz
    rw [← hz] at h₂
    exact lt_ge_contra h₂ h₁
}

theorem eq_or_ne (x y : ℝ) : x = y ∨ x ≠ y := Classical.em (x = y)

theorem lt_trichotomy (x y : ℝ) : x < y ∨ x = y ∨ y < x := by {
  rcases eq_or_ne x y with he | hn
  · right; left; exact he
  rcases le_total x y with hl | hg
  · left; exact ⟨hl, hn⟩
  · right; right; exact ⟨hg, hn.symm⟩
}

theorem add_lt_add_right {x y} : x < y → (z : ℝ) → x + z < y + z := by {
  intro h₁ z
  constructor
  · exact add_le_add_right h₁.le z
  · intro h
    rw [add_right_cancel] at h
    exact h₁.ne h
}

theorem add_lt_add_left {x y : ℝ} (z) : x < y → z + x < z + y := by {
  intro h
  rw [add_comm z x, add_comm z y]
  exact add_lt_add_right h z
}

theorem sub_self (x : ℝ) : x - x = 0 := by {
  rw [sub_eq_add_neg, add_neg]
}

theorem sub_add_cancel {x y : ℝ} : x - y + y = x := by {
  rw [sub_eq_add_neg, ← add_assoc, neg_add, add_zero]
}

theorem add_sub_cancel {x y : ℝ} : x + y - y = x := by {
  rw [← add_right_cancel y, sub_add_cancel]
}

theorem sub_eq_zero {x y : ℝ} : x - y = 0 ↔ x = y := by {
  constructor
  · intro h
    rw [← add_right_cancel y, sub_add_cancel, zero_add] at h
    exact h
  · intro h
    rw [h, sub_self]
}

theorem neg_ne_zero {x : ℝ} : -x ≠ 0 ↔ x ≠ 0 := by {
  constructor
  · intro h₁ h₂
    rw [h₂, neg_zero] at h₁
    exact h₁ rfl
  · intro h₁ h₂
    rw [← neg_neg x, h₂, neg_zero] at h₁
    exact h₁ rfl
}

theorem mul_left {x y : ℝ} (z) (h : x = y) : z * x = z * y := by {
  rw [h]
}

theorem mul_right {x y : ℝ} (h : x = y) (z) : x * z = y * z := by {
  rw [h]
}

theorem mul_eq_mul_right {x y z : ℝ} (hz : z ≠ 0) : x * z = y * z ↔ x = y := by {
  constructor
  · intro h
    have := mul_right h (z⁻¹)
    rw [← mul_assoc, mul_inv_cancel hz, mul_one, ← mul_assoc, mul_inv_cancel hz, mul_one] at this
    exact this
  · intro h
    rw [h]
}

theorem mul_eq_mul_left {x y z : ℝ} (hz : z ≠ 0) : z * x = z * y ↔ x = y := by {
  constructor
  · intro h
    rw [← mul_eq_mul_right hz, mul_comm x z, mul_comm y z]
    exact h
  · intro h
    rw [h]
}

theorem mul_ne_zero {x y : ℝ} : x * y ≠ 0 ↔ x ≠ 0 ∧ y ≠ 0 := by {
  constructor
  · intro h
    constructor
    · intro hx
      rw [hx, zero_mul] at h
      exact h rfl
    · intro hy
      rw [hy, mul_zero] at h
      exact h rfl
  · intro ⟨hx, hy⟩ h
    have := mul_right h y⁻¹
    rw [← mul_assoc, mul_inv_cancel hy, mul_one, zero_mul] at this
    contradiction
}

theorem mul_eq_zero {x y : ℝ} : x * y = 0 ↔ x = 0 ∨ y = 0 := by {
  constructor
  · intro h
    rw [@Classical.or_iff_not_imp_left]
    intro hx
    have := mul_left (x⁻¹) h
    rw [mul_assoc, inv_mul hx, one_mul, mul_zero] at this
    exact this
  · intro h
    rcases h with h | h
    · rw [h, zero_mul]
    · rw [h, mul_zero]
}

theorem mul_pos {x y : ℝ} : 0 < x → 0 < y → 0 < x * y := by {
  intro hx hy
  constructor
  · exact mul_nonneg hx.le hy.le
  · intro h
    have := Ne.symm <| mul_ne_zero.mpr ⟨hx.ne.symm, hy.ne.symm⟩
    contradiction
}

theorem inv_ne_zero {x : ℝ} (hx : x ≠ 0) : x⁻¹ ≠ 0 := by {
  intro h
  rw [← mul_eq_mul_right hx, inv_mul hx, zero_mul] at h
  exact one_ne_zero h
}

theorem inv_inv {x : ℝ} (hx : x ≠ 0) : (x⁻¹)⁻¹ = x := by {
  rw [← mul_eq_mul_right (inv_ne_zero hx), inv_mul (inv_ne_zero hx), mul_inv_cancel hx]
}

theorem inv_mul_inv {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) : x⁻¹ * y⁻¹ = (x * y)⁻¹ := by {
  rw [← mul_eq_mul_right (mul_ne_zero.mpr ⟨hx, hy⟩), inv_mul (mul_ne_zero.mpr ⟨hx, hy⟩), mul_comm x y, mul_assoc, ← mul_assoc x⁻¹ (y⁻¹), inv_mul hy, mul_one, inv_mul hx]
}

theorem inv_one : (1 : ℝ)⁻¹ = 1 := by {
  rw [← mul_eq_mul_right one_ne_zero, inv_mul one_ne_zero, one_mul]
}

theorem neg_le_neg_of_le {x y : ℝ} : x ≤ y → -y ≤ -x := by {
  intro h
  have := add_le_add_right h (-x + -y)
  rw [add_assoc, add_neg, zero_add, add_comm, ← add_assoc, neg_add, add_zero] at this
  exact this
}

theorem neg_nonpos {x : ℝ} : -x ≤ 0 ↔ x ≥ 0 := by {
  constructor
  · intro h
    rw [← neg_zero] at h
    have := neg_le_neg_of_le h
    rw [neg_neg, neg_neg] at this
    exact this
  · intro h
    rw [← neg_zero]
    exact neg_le_neg_of_le h
}

theorem neg_lt_zero {x : ℝ} : -x < 0 ↔ x > 0 := by {
  constructor
  · intro h
    constructor
    · exact neg_nonpos.mp h.le
    · intro hz
      exact h.ne ((neg_eq_zero x).mpr hz.symm)
  · intro h
    constructor
    · exact neg_nonpos.mpr h.le
    · intro hz
      rw [neg_eq_zero] at hz
      exact h.ne hz.symm
}

theorem neg_nonneg {x : ℝ} : -x ≥ 0 ↔ x ≤ 0 := by {
  constructor
  · intro h
    rw [← neg_neg x, neg_nonpos]
    exact h
  · intro h
    rw [← neg_nonpos, neg_neg]
    exact h
}

theorem neg_pos {x : ℝ} : -x > 0 ↔ x < 0 := by {
  constructor
  · intro h
    constructor
    · exact neg_nonneg.mp h.le
    · rw [← neg_ne_zero]
      exact h.ne.symm
  · intro h
    constructor
    · exact neg_nonneg.mpr h.le
    · apply Ne.symm
      rw [neg_ne_zero]
      exact h.ne
}

theorem mul_self_nonneg (x : ℝ) : 0 ≤ x * x := by {
  rcases le_total 0 x with h | h
  · exact mul_nonneg h h
  · rw [← neg_neg x, neg_mul, mul_neg, neg_neg]
    exact mul_nonneg (neg_nonneg.mpr h) (neg_nonneg.mpr h)
}

theorem mul_self_pos {x : ℝ} (h : x ≠ 0) : 0 < x * x := by {
  constructor
  · exact mul_self_nonneg x
  · exact (mul_ne_zero.mpr ⟨h, h⟩).symm
}

theorem one_pos : (1 : ℝ) > 0 := by {
  constructor
  · have := mul_self_nonneg 1
    rw [one_mul] at this
    exact this
  · exact one_ne_zero.symm
}

theorem neg_nonpos_iff_nonneg {x : ℝ} : -x ≤ 0 ↔ x ≥ 0 := by {
  constructor
  · intro h
    rw [← neg_neg x, ← neg_zero]
    exact neg_le_neg_of_le h
  · intro h
    have := add_le_add_right h (-x)
    rw [add_neg, zero_add] at this
    exact this
}

theorem neg_le_neg {x y : ℝ} : -y ≤ -x ↔ x ≤ y := by {
  constructor
  · intro h
    rw [← neg_neg x, ← neg_neg y]
    exact neg_le_neg_of_le h
  · intro h
    exact neg_le_neg_of_le h
}

theorem neg_lt_neg {x y : ℝ} : -y < -x ↔ x < y := by {
  constructor
  · intro h
    constructor
    · exact neg_le_neg.mp h.le
    · intro hz
      have := h.ne
      rw [hz] at this
      exact this rfl
  · intro h
    constructor
    · exact neg_le_neg_of_le h.le
    · intro hz
      rw [neg_eq_comm, neg_neg] at hz
      exact h.ne hz.symm
}

theorem add_nonneg {x y : ℝ} : 0 ≤ x → 0 ≤ y → 0 ≤ x + y := by {
  intro hx hy
  apply le_trans hx
  have := add_le_add_left x hy
  rw [add_zero] at this
  exact this
}

theorem add_pos_of_pos_of_nonneg {x y : ℝ} : 0 < x → 0 ≤ y → 0 < x + y := by {
  intro hx hy
  constructor
  · exact add_nonneg hx.le hy
  · intro hz
    rw [hz] at hy
    have := add_le_add_right hy (-y)
    rw [← add_assoc, add_neg, add_zero] at this
    exact lt_ge_contra hx this
}

theorem add_pos_of_nonneg_of_pos {x y : ℝ} : 0 ≤ x → 0 < y → 0 < x + y := by {
  intro hx hy
  have := add_pos_of_pos_of_nonneg hy hx
  rw [add_comm] at this
  exact this
}

theorem add_pos_of_pos_of_pos {x y : ℝ} : 0 < x → 0 < y → 0 < x + y := by {
  intro hx hy
  exact add_pos_of_pos_of_nonneg hx hy.le
}

theorem add_nonpos {x y : ℝ} : x ≤ 0 → y ≤ 0 → x + y ≤ 0 := by {
  intro hx hy
  have := add_le_add_left x hy
  rw [add_zero] at this
  exact le_trans this hx
}

theorem add_lt_zero_of_neg_of_nonpos {x y : ℝ} : x < 0 → y ≤ 0 → x + y < 0 := by {
  intro hx hy
  constructor
  · exact add_nonpos hx.le hy
  · intro hz
    have := add_le_add_left x hy
    rw [add_zero, hz] at this
    exact lt_ge_contra hx this
}

theorem sub_nonneg {x y : ℝ} : 0 ≤ y - x ↔ x ≤ y := by {
  constructor
  · intro h
    have := add_le_add_right h x
    rw [zero_add, sub_add_cancel] at this
    exact this
  · intro h
    have := add_le_add_right h (-x)
    rw [add_neg, ← sub_eq_add_neg] at this
    exact this
}

theorem sub_pos {x y : ℝ} : 0 < y - x ↔ x < y := by {
  constructor
  · intro h
    constructor
    · exact sub_nonneg.mp h.le
    · intro hz
      rw [hz, sub_self] at h
      exact lt_self_contra h
  · intro h
    constructor
    · exact sub_nonneg.mpr h.le
    · intro hz
      rw [← add_right_cancel x, zero_add, sub_add_cancel] at hz
      exact h.ne hz
}

theorem add_le_add {x y z w : ℝ} : w ≤ x → y ≤ z → w + y ≤ x + z := by {
  intro h₁ h₂
  exact le_trans (add_le_add_right h₁ y) (add_le_add_left x h₂)
}

theorem add_lt_add_of_le_of_lt {x y z w : ℝ} : w ≤ x → y < z → w + y < x + z := by {
  intro h₁ h₂
  exact le_trans_lt (add_le_add_right h₁ y) (add_lt_add_left x h₂)
}

theorem add_lt_add_of_lt_of_le {x y z w : ℝ} : x < y → z ≤ w → x + z < y + w := by {
  intro h₁ h₂
  have h := add_lt_add_of_le_of_lt h₂ h₁
  rw [add_comm z x, add_comm w y] at h
  exact h
}

theorem add_lt_add_of_lt_of_lt {x y z w : ℝ} : x < y → z < w → x + z < y + w := by {
  intro h₁ h₂
  exact add_lt_add_of_le_of_lt h₁.le h₂
}

theorem mul_le_mul_left {x y z : ℝ} (hz : z ≥ 0) : x ≤ y → z * x ≤ z * y := by {
  intro h
  rw [← sub_nonneg, ← mul_sub]
  apply mul_nonneg hz
  rw [sub_nonneg]
  exact h
}

theorem mul_le_mul_right {x y z : ℝ} (hz : z ≥ 0) : x ≤ y → x * z ≤ y * z := by {
  intro h
  rw [mul_comm x z, mul_comm y z]
  exact mul_le_mul_left hz h
}

theorem mul_lt_mul_left {x y z : ℝ} (hz : z > 0) : x < y → z * x < z * y := by {
  intro h
  constructor
  · exact mul_le_mul_left hz.le h.le
  · intro hz'
    rw [mul_eq_mul_left hz.ne.symm] at hz'
    exact h.ne hz'
}

theorem mul_lt_mul_right {x y z : ℝ} (hz : z > 0) : x < y → x * z < y * z := by {
  intro h
  rw [mul_comm x z, mul_comm y z]
  exact mul_lt_mul_left hz h
}

theorem mul_neg_of_neg_of_pos {x y : ℝ} : x < 0 → 0 < y → x * y < 0 := by {
  intro hx hy
  rw [← neg_pos] at hx
  rw [← neg_pos, ← neg_mul]
  exact mul_pos hx hy
}

theorem mul_neg_of_pos_of_neg {x y : ℝ} : 0 < x → y < 0 → x * y < 0 := by {
  intro hx hy
  rw [mul_comm]
  exact mul_neg_of_neg_of_pos hy hx
}

theorem mul_pos_of_neg_neg {x y : ℝ} : x < 0 → y < 0 → x * y > 0 := by {
  intro hx hy
  rw [← neg_pos] at hx hy
  rw [← neg_mul_neg]
  exact mul_pos hx hy
}

theorem inv_pos_of_pos {x : ℝ} (hx : x > 0) : x⁻¹ > 0 := by {
  rw [← mul_one (x⁻¹), ← inv_mul hx.ne.symm, mul_assoc]
  apply mul_pos (mul_self_pos _) hx
  exact inv_ne_zero hx.ne.symm
}

theorem inv_neg_of_neg {x : ℝ} (hx : x < 0) : x⁻¹ < 0 := by {
  rw [← mul_one (x⁻¹), ← inv_mul hx.ne, mul_assoc]
  exact mul_neg_of_pos_of_neg (mul_self_pos (inv_ne_zero hx.ne)) hx
}

theorem inv_lt_inv_of_pos_pos_lt {x y : ℝ} (hx : x > 0) (hy : y > 0) (h : x < y) : y⁻¹ < x⁻¹ := by {
  
}
