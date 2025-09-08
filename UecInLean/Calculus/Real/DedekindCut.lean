import Batteries.Data.Rat
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Batteries.Tactic.Instances

theorem half_lt {a b : ℚ} (h : a < b) : a < (a + b) / 2 ∧ (a + b) / 2 < b := by {
  constructor
  {
    have : a + a < a + b := add_lt_add_left h a
    have : (a + a) / 2 < (a + b) / 2 := div_lt_div_of_pos_right this (by decide)
    rw [← mul_two, mul_div_cancel_right₀ _ (by decide)] at this
    exact this
  }
  {
    have : a + b < b + b := add_lt_add_right h b
    have : (a + b) / 2 < (b + b) / 2 := div_lt_div_of_pos_right this (by decide)
    rw [← mul_two, mul_div_cancel_right₀ _ (by decide)] at this
    exact this
  }
}

theorem neg_gt {a b : ℚ} (h : -a > b) : a < -b := by {
  rw [← neg_lt_neg_iff, neg_neg]
  exact h
}

/-- 下界と最大値を持たない有理数の部分集合 i.e.値の「下側」 -/
structure IsCutOfRat (L : Set ℚ) : Prop where
  /-- 下側が ∅ なときは負の無限大を表すらしい -/
  not_ninfin : L.Nonempty
  /-- 上側が ∅ なときは正の無限大を表すらしい -/
  not_pinfin : Lᶜ.Nonempty
  downward_closed : ∀ x, ∀ y > x, y ∈ L → x ∈ L
  no_max : ∀ x ∈ L, ∃ y ∈ L, y > x

theorem IsCutOfRat.lt_of_notMem {L : Set ℚ} (hL : IsCutOfRat L) {x y : ℚ} (hx : x ∉ L) (hy : y ∈ L) : y < x := by {
  by_contra h
  apply hx
  rw [not_lt, le_iff_eq_or_lt] at h
  rcases h with rfl | h
  · exact hy
  · exact hL.downward_closed _ _ h hy
}

theorem IsCutOfRat.upward_closed {L : Set ℚ} (hL : IsCutOfRat L) : ∀ x, ∀ y < x, y ∈ Lᶜ → x ∈ Lᶜ := by {
  intro x y hxy hy hx
  apply hy
  exact hL.downward_closed _ _ hxy hx
}

theorem IsCutOfRat.obtain_greater {L : Set ℚ} (hL : IsCutOfRat L) {x : ℚ} (hx : x ∈ Lᶜ) : ∃ y ∈ Lᶜ, y > x
  := ⟨x + 1, hL.upward_closed _ _ (by simp) hx, by simp⟩

theorem IsCutOfRat.obtain_smaller {L : Set ℚ} (hL : IsCutOfRat L) {x : ℚ} (hx : x ∈ L) : ∃ y ∈ L, y < x
  := ⟨x - 1, hL.downward_closed _ _ (by simp) hx, by simp⟩

def Real := { B : Set ℚ // IsCutOfRat B }
notation:max "ℝ" => Real

namespace Real

@[ext]
theorem ext {a b : ℝ} : a.val = b.val → a = b := by intro; cases a; congr

noncomputable instance : LinearOrder ℝ where
  le a b := a.val ⊆ b.val
  le_refl a x h := h
  le_trans a b c hab hbc x ha := hbc <| hab ha
  le_antisymm a b hab hba := by {
    ext
    constructor
    · intro ha; exact hab ha
    · intro hb; exact hba hb
  }
  le_total α β := by {
    by_contra h
    push_neg at h
    obtain ⟨hl, hr⟩ := h
    have ⟨a, haβ, haα⟩ := Set.nonempty_of_not_subset hr
    have ⟨b, hbα, hbβ⟩ := Set.nonempty_of_not_subset hl
    have b_lt_a := α.property.lt_of_notMem haα hbα
    have a_lt_b := β.property.lt_of_notMem hbβ haβ
    exact not_lt_of_gt a_lt_b b_lt_a
  }
  toDecidableLE := Classical.decRel _

theorem le_def (a b : ℝ) : a ≤ b ↔ a.val ⊆ b.val := by rfl

def ofRat (q : ℚ) : ℝ := ⟨
  { r | r < q },
  ⟨q - 1, by simp⟩, ⟨q, by simp⟩,
  (fun x y hxy hy => hxy.trans hy),
  by {
    intro x hx
    use (x + q) / 2
    rw [Set.mem_setOf_eq] at hx ⊢
    exact And.symm <| half_lt hx
  }⟩

theorem mem_ofRat (q r : ℚ) : r ∈ (ofRat q).val ↔ r < q
  := by rw [ofRat, Set.mem_setOf_eq]

instance {n : ℕ} : OfNat ℝ n := ⟨ofRat n⟩
instance : CoeSort ℚ ℝ := ⟨ofRat⟩

theorem lt_of_mem {q : ℚ} {x : ℝ} : q ∈ x.val ↔ ofRat q < x := by {
  constructor
  {
    intro h
    rw [lt_iff_le_and_ne]
    constructor
    · intro z hz
      exact x.property.downward_closed z q hz h
    · intro heq
      cases heq
      exact lt_irrefl q (h)
  }
  {
    intro h
    rw [lt_iff_le_not_ge] at h
    by_contra hnMem
    apply h.right
    intro z hz
    exact x.property.lt_of_notMem hnMem hz
  }
}

theorem ofRat_lt_ofRat {p q : ℚ} : ofRat p < ofRat q ↔ p < q
  := by rw [← lt_of_mem, mem_ofRat]

theorem neg_ofRat (q : ℚ) : ofRat q < 0 ↔ q < 0 := by {
  rw [show ofNat(0) = ofRat 0 by rfl, ofRat_lt_ofRat]
}

theorem lt_iff_diff_Nonempty (α β : ℝ) : α < β ↔ (β.val \ α.val).Nonempty := by {
  constructor
  {
    rw [lt_iff_le_and_ne]
    intro ⟨hle, hne⟩
    apply Set.nonempty_of_not_subset
    intro h
    rw [le_def] at hle
    have := Real.ext (subset_antisymm hle h)
    contradiction
  }
  {
    intro ⟨x, hxβ, hxα⟩
    rw [lt_iff_le_and_ne]
    constructor
    {
      intro z hzα; by_contra hzβ
      have z_lt_x := α.property.lt_of_notMem hxα hzα
      have x_lt_z := β.property.lt_of_notMem hzβ hxβ
      exact not_lt_of_gt x_lt_z z_lt_x
    }
    intro heq; cases heq; exact hxα hxβ
  }
}

/-- 「上側」が最小値を持つ実数を改めて有理数と呼ぶ -/
def Rational (x : ℝ)   := ∃ q ∈ x.valᶜ, ∀ r ∈ x.valᶜ, q ≤ r
def Irrational (x : ℝ) := ∀ q ∈ x.valᶜ, ∃ r ∈ x.valᶜ, r < q

theorem Irrational_iff_not_Rational {x : ℝ} : Irrational x ↔ ¬ Rational x
  := by unfold Irrational Rational; push_neg; rfl

theorem ofRat_Rational (q : ℚ) : Rational (ofRat q) := by {
  use q
  constructor
  · rw [Set.mem_compl_iff]
    exact lt_irrefl q
  · intro r hr
    rw [Set.mem_compl_iff] at hr
    exact le_of_not_gt hr
}

noncomputable instance : DecidablePred Rational := fun x => Classical.dec (Rational x)

instance : Add ℝ where
  add S T := ⟨
    { q | ∃ s ∈ S.val, ∃ t ∈ T.val, q = s + t },
    by {
      obtain ⟨s, hs⟩ := S.property.not_ninfin
      obtain ⟨t, ht⟩ := T.property.not_ninfin
      use s + t, s, hs, t, ht
    },
    by {
      obtain ⟨s, hs⟩ := S.property.not_pinfin
      obtain ⟨t, ht⟩ := T.property.not_pinfin
      use s + t
      intro ⟨s', hs', t', ht', h⟩
      have := Ne.symm <| ne_of_lt <| add_lt_add (S.property.lt_of_notMem hs hs') (T.property.lt_of_notMem ht ht')
      contradiction
    },
    by {
      intro x y hyx ⟨yS, hyS, yT, hyT, hy⟩
      use x - y + yS, (S.property.downward_closed _ _ (by simp [hyx]) hyS), yT, hyT
      rw [hy, sub_add, add_sub_cancel_left, sub_add_cancel]
    },
    by {
      intro x ⟨xS, hxS, xT, hxT, hx⟩
      obtain ⟨yS, hyS, hyxS⟩ := S.property.no_max xS hxS
      use yS + xT
      constructor
      · use yS, hyS, xT, hxT
      · rw [hx]
        exact add_lt_add_right hyxS _
    }
  ⟩

theorem add_def (α β : ℝ) : (α + β).val = { q | ∃ s ∈ α.val, ∃ t ∈ β.val, q = s + t } := by rfl

instance : AddCommSemigroup ℝ where
  add_assoc α β γ := by {
    ext
    constructor
    · intro ⟨_, ⟨xα, hxα, xβ, hxβ, hx'⟩, xγ, hxγ, hx⟩
      rcases hx'; rcases hx
      use xα, hxα, xβ + xγ, by { use xβ, hxβ, xγ, hxγ }
      rw [add_assoc]
    · intro ⟨xα, hxα, _, ⟨xβ, hxβ, xγ, hxγ, hx'⟩, hx⟩
      rcases hx; rcases hx'
      use xα + xβ, by { use xα, hxα, xβ, hxβ }, xγ, hxγ
      rw [add_assoc]
  }
  add_comm α β := by {
    ext
    constructor
    <;> {
      intro ⟨xα, hxα, xβ, hxβ, hx⟩
      use xβ, hxβ, xα, hxα
      rw [add_comm, hx]
    }
  }

theorem zero_add (α : ℝ) : 0 + α = α := by {
  ext x
  constructor
  {
    intro ⟨x0, hx0, xα, hxα, hx⟩
    rcases hx
    rw [lt_of_mem, neg_ofRat] at hx0
    apply α.property.downward_closed _ _ _ hxα
    simp [hx0]
  }
  {
    intro hxα
    have ⟨y, hyα, hy⟩ := α.property.no_max x hxα
    use x - y, by { rw [lt_of_mem, neg_ofRat]; simp [hy] }, y, hyα
    rw [sub_add_cancel]
  }
}

instance : Neg ℝ where
  neg α := ⟨
    -- { -r | r ∈ { q ∈ α.valᶜ | ∃ s ∈ α.valᶜ, q < s } }; 上側の min を除いたもの
    { x | ∃ s ∈ α.valᶜ, s < -x},
    by {
      obtain ⟨r, hr⟩ := α.property.not_pinfin
      obtain ⟨s, hs, hrs⟩ := α.property.obtain_greater hr
      use -s, r, hr
      rw [neg_neg]
      exact hrs
    },
    by {
      obtain ⟨r, r_in_α⟩ := α.property.not_ninfin
      use -r
      intro ⟨w, w_in_αc, w_lt_r⟩
      rw [neg_neg] at w_lt_r
      have := α.property.lt_of_notMem w_in_αc r_in_α
      exact not_lt_of_gt w_lt_r this
    },
    by {
      intro x y x_lt_y ⟨ys, ys_in_αc, hy⟩
      apply neg_lt_neg at x_lt_y
      use ys, ys_in_αc, x_lt_y.trans' hy
    },
    by {
      intro x ⟨xs, xs_in_αc, hx⟩
      use -((xs + -x) / 2)
      obtain ⟨hl, hr⟩ := half_lt hx
      constructor
      · use xs, xs_in_αc
        rw [neg_neg]
        exact hl
      · exact neg_gt hr
    }
  ⟩

theorem neg_def (α : ℝ) : (-α).val = { x | ∃ s ∈ α.valᶜ, s < -x } := by rfl

end Real
