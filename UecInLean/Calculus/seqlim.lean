import Mathlib.Data.Real.Basic
import Mathlib.Data.EReal.Basic

namespace UEC.Calculus
open Set

/-- I 上で f が xがaに右から近づく時、f x が L に近づく -/
def RightLimit (I : Set ℝ) (f : ℝ → ℝ) (a : I) (L : ℝ)
  := ∀ ε > 0, ∃ δ > 0, ∀ x ∈ I, x - a ∈ Ioo 0 δ → |f x - L| < ε
notation f " ⟶ "L" (x⟶ " a "⁺)" => RightLimit _ f a L

def LeftLimit (I : Set ℝ) (f : ℝ → ℝ) (a : I) (L : ℝ)
  := ∀ ε > 0, ∃ δ > 0, ∀ x ∈ I, a - x ∈ Ioo 0 δ → |f x - L| < ε
notation f " ⟶ " L " (x⟶ " a "⁻)" => LeftLimit _ f a L

def Limit (I : Set ℝ) (f : ℝ → ℝ) (a : I) (L : ℝ)
  := ∀ ε > 0, ∃ δ > 0, ∀ x ∈ I, |x - a| ∈ Ioo 0 δ → |f x - L| < ε
notation f " ⟶ " L " (x⟶ " a ")" => Limit _ f a L

theorem Limit_of_LRLimit {I : Set ℝ} {f : ℝ → ℝ} {a : I} {L : ℝ} (right : f ⟶ L (x⟶ a⁺)) (left : f ⟶ L (x⟶ a⁻)) : f ⟶ L (x⟶ a) := by {
  intro ε hε
  rcases right ε hε with ⟨δr, hδr, hr⟩
  rcases left ε hε with ⟨δl, hδl, hl⟩
  use min δl δr, lt_min hδl hδr
  intro x hx ⟨oxa, xaδ⟩
  rcases lt_abs.mp oxa with oxa | oxa
  · apply hr x hx
    use oxa
    rw [abs_lt] at xaδ
    exact xaδ.2.trans_le (min_le_right _ _)
  · apply hl x hx
    rw [neg_sub] at oxa
    use oxa
    rw [abs_sub_comm, abs_lt] at xaδ
    exact xaδ.2.trans_le (min_le_left _ _)
}

theorem RightLimit_of_Limit {I : Set ℝ} {f : ℝ → ℝ} {a : I} {L : ℝ} (h : f ⟶ L (x⟶ a)) : f ⟶ L (x⟶ a⁺) := by {
  intro ε hε
  rcases h ε hε with ⟨δ, hδ, h⟩
  use δ, hδ
  intro x hx ⟨oxa, xaδ⟩
  apply h x hx
  rw [mem_Ioo, abs_lt]
  exact ⟨abs_pos_of_pos oxa, (neg_neg_iff_pos.mpr hδ).trans oxa, xaδ⟩
}

theorem LeftLimit_of_Limit {I : Set ℝ} {f : ℝ → ℝ} {a : I} {L : ℝ} (h : f ⟶ L (x⟶ a)) : f ⟶ L (x⟶ a⁻) := by {
  intro ε hε
  rcases h ε hε with ⟨δ, hδ, h⟩
  use δ, hδ
  intro x hx ⟨oax, axδ⟩
  apply h x hx
  rw [mem_Ioo, abs_sub_comm, abs_lt]
  exact ⟨abs_pos_of_pos oax, (neg_neg_iff_pos.mpr hδ).trans oax, axδ⟩
}

