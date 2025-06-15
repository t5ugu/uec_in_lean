import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Range
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Tactic.TypeStar

namespace List
open Option

/--
要素が既知ならば、集合の最大値よりその要素が小さいことは明らか
`List.le_max?_getD_of_mem` は `Nat` にしか使えない
-/
theorem le_max?_getD_of_mem' {R : Type*} [LinearOrder R] {l : List R} {a : R} (ha : a ∈ l) : ∀ d, a ≤ l.max?.getD d := by {
  induction l with
  | nil => contradiction -- a ∈ [] は矛盾
  | cons h t ih => {
    intro _
    rw [max?_cons', getD_some]
    rcases mem_cons.mp ha with ha | ha
    · rw [ha, foldl_max]
      exact le_max_of_le_left (by rfl)
    · rw [foldl_max]
      exact le_max_of_le_right (ih ha h)
  }
}

theorem max?_cons_cons_comm {R : Type*} [LinearOrder R] {h₁ h₂ : R} {t} : (h₁ :: h₂ :: t).max? = (h₂ :: h₁ :: t).max? := by {
  rw [max?, max?, foldl_eq_of_comm_of_assoc, foldl_cons, foldl_assoc]
}

theorem max?_cons'' {R : Type*} [LinearOrder R] {h t} {d : R} (ht : t ≠ []) : (h :: t).max?.getD d = max h (t.max?.getD d) := by {
  induction t with
  | nil => contradiction
  | cons H T ih => {
    rw [max?, getD_some, max?_cons', getD_some, foldl_cons, foldl_assoc]
  }
}

theorem max?_getD_singleton {R : Type*} [LinearOrder R] {h d : R} : [h].max?.getD d = h := by {
  rw [max?_cons', foldl_nil, getD_some]
}

theorem max?_getD_le_of_each_le {R : Type*} [LinearOrder R] {l : List R} (M : R) (h : ∀ x ∈ l, x ≤ M)
: ∀ d ≤ M, l.max?.getD d ≤ M := by {
  intro d hd
  induction l with
  | nil => {
    rw [max?_nil, getD_none]
    exact hd
  }
  | cons H T ih => {
    rcases eq_or_ne T [] with hT | hT
    · rw [hT, max?_getD_singleton]
      exact h H mem_cons_self
    · rw [max?_cons'' hT, max_le_iff]
      constructor
      · exact h H mem_cons_self
      · exact ih (fun x hx => h x (mem_cons_of_mem H hx))
  }
}
