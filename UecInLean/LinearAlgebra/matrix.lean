import Mathlib.Tactic.Use
import Mathlib.Tactic.NthRewrite

set_option autoImplicit true

universe u v w

class Fintype (α : Type u) where
  elems : List α
  pull : α → Fin (elems.length)
  elems_pull (a) : elems[pull a] = a
  elems_inj {i j} {hi : i < elems.length} {hj : j < elems.length} : elems[i] = elems[j] → i = j

instance [Fintype α] : DecidableEq α := by {
  intro a b
  if h : (Fintype.pull a).val = (Fintype.pull b).val then
    apply isTrue
    rw [← Fintype.elems_pull a, Fin.eq_of_val_eq h, Fintype.elems_pull]
  else
    exact isFalse (by intro contra; apply h; rw [contra])
}

theorem mul_if {R} [Mul R] (p : Prop) (k t e : R) [Decidable p] :
  k * (if p then t else e) = if p then k * t else k * e := by {
  by_cases h : p
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
}

theorem List.sum_map_if_zero (L : List α) (p : α → Prop) [DecidablePred p] (f : α → β) [Lean.Grind.AddCommMonoid β] : (L.map (fun x => if p x then f x else 0)).sum = ((L.filter p).map f).sum := by {
  induction L with
  | nil => rfl
  | cons hd tl ih =>
    by_cases h : p hd
    · rw [map_cons, if_pos h, sum_cons, ih, filter_cons_of_pos (by simpa), map_cons, sum_cons]
    {
      rw [map_cons, if_neg h, sum_cons, ih, filter_cons_of_neg (by simpa)]
      apply Lean.Grind.AddCommMonoid.zero_add
    }
}

theorem List.getElem_Fin_cons_drop {l : List α} (i : Fin l.length) : l[i] :: l.drop (i.val + 1) = l.drop i := by {
  obtain ⟨_, h⟩ := i
  exact getElem_cons_drop h
}

theorem Fintype.elems_filter_eq_singleton [Fintype α] (y : α) : elems.filter (fun x => x = y) = [y] := by {
  rw [List.filter_eq_cons_iff]
  use elems.take (Fintype.pull y), elems.drop (Fintype.pull y + 1)
  exact ⟨
    by {
      nth_rw 2 [← elems_pull y]
      rw [List.getElem_Fin_cons_drop, List.take_append_drop]
    },
    by {
      suffices hy : y ∉ elems.take (Fintype.pull y) by {
        intro x hx h
        rw [decide_eq_true_eq] at h
        subst h
        exact hy hx
      }
      intro hy
      rw [List.mem_take_iff_getElem] at hy
      obtain ⟨i, hi, hm⟩ := hy
      rw [Nat.lt_min] at hi
      have : i = pull y := elems_inj (hm.trans (elems_pull y).symm)
      subst this
      exact Nat.lt_irrefl (pull y) hi.left
    },
    by simp,
    by {
      rw [List.filter_eq_nil_iff]
      suffices hy : y ∉ elems.drop (Fintype.pull y + 1) by {
        intro x hx h
        rw [decide_eq_true_eq] at h
        subst h
        exact hy hx
      }
      intro hy
      rw [List.mem_drop_iff_getElem] at hy
      obtain ⟨i, hi, hm⟩ := hy
      have : (pull y) + 1 + i = (pull y) := elems_inj (hm.trans (elems_pull y).symm)
      rw [Nat.add_assoc, Nat.add_eq_left, ← Nat.succ_eq_one_add] at this
      exact Nat.succ_ne_zero i this
    }
  ⟩
}

def Matrix (n : Type u) (m : Type v) (R : Type w) := n → m → R

namespace Matrix

instance [Add R] : Add (Matrix n m R) where
  add A B i j := A i j + B i j

theorem add_def {n m R} [Add R] (A B : Matrix n m R) (i : n) (j : m) : (A + B) i j = A i j + B i j := rfl

instance [Zero R] : OfNat (Matrix n m R) 0 where
  ofNat _ _ := 0

instance [Zero R] : Zero (Matrix n m R) where
  zero := 0

theorem zero_def {n m R} [Zero R] (i : n) (j : m) : (0 : Matrix n m R) i j = 0 := rfl

instance [Zero R] [One R] [DecidableEq n] : OfNat (Matrix n n R) 1 where
  ofNat i j := if i = j then 1 else 0

instance [Zero R] [One R] [DecidableEq n] : One (Matrix n n R) where
  one := 1

theorem one_def [Zero R] [One R] [DecidableEq n] (i j : n) : (1 : Matrix n n R) i j = if i = j then 1 else 0 := rfl

instance [Neg R] : Neg (Matrix n m R) where
  neg A i j := - A i j

theorem add_assoc {n m R} [Add R] [@Std.Associative R Add.add] (A B C : Matrix n m R) : A + B + C = A + (B + C) := by {
    funext i j
    exact @Std.Associative.assoc R (· + ·) _ (A i j) (B i j) (C i j)
  }

instance [Add R] [@Std.Associative R Add.add] : @Std.Associative (Matrix n m R) Add.add where
  assoc := add_assoc

theorem add_comm {n m R} [Add R] [@Std.Commutative R Add.add] (A B : Matrix n m R) : A + B = B + A := by {
  funext i j
  exact @Std.Commutative.comm R (· + ·) _ (A i j) (B i j)
}

instance [Add R] [@Std.Commutative R Add.add] : @Std.Commutative (Matrix n m R) Add.add where
  comm := add_comm

instance {n m l R} [Add R] [Mul R] [Zero R] [Fintype m] : HMul (Matrix n m R) (Matrix m l R) (Matrix n l R) where
  hMul M N i j := Fintype.elems.map (fun k => M i k * N k j) |> List.sum

theorem mul_def {n m l R} [Add R] [Mul R] [Zero R] [Fintype m] (M : Matrix n m R) (N : Matrix m l R) (i : n) (j : l) : (M * N) i j = (Fintype.elems.map (fun k => M i k * N k j) |> List.sum) := rfl

instance {n m R} [Mul R] : SMul R (Matrix n m R) where
  smul k A i j := k * A i j

theorem smul_def {n m R} [Mul R] (k : R) (A : Matrix n m R) (i : n) (j : m) : (k • A) i j = k * A i j := rfl

def transpose {n m R} (A : Matrix n m R) : Matrix m n R :=
  fun i j => A j i
prefix:150 "ᵀ" => Matrix.transpose

theorem transpose_transpose {n m R} (A : Matrix n m R) : ᵀ(ᵀA) = A := by {
  funext i j
  rfl
}

theorem transpose_add {n m R} [Add R] (A B : Matrix n m R) : ᵀ(A + B) = ᵀA + ᵀB := by {
  funext i j
  rfl
}

theorem transpose_smul {n m R} [Mul R] (k : R) (A : Matrix n m R) : ᵀ(k • A) = k • ᵀA := by {
  funext i j
  rfl
}

theorem transpose_mul {n m l R} [Add R] [Mul R] [@Std.Commutative R Mul.mul] [Zero R] [Fintype m] (A : Matrix n m R) (B : Matrix m l R) :
  ᵀ(A * B) = ᵀB * ᵀA := by {
  funext i j
  simp [transpose, mul_def, Std.Commutative.comm]
}

theorem mul_smul {n m R} [Mul R] [@Std.Associative R Mul.mul] (k1 k2 : R) (A : Matrix n m R) : (k1 * k2) • A = k1 • (k2 • A) := by {
  funext i j
  rw [smul_def, smul_def, smul_def]
  exact Std.Associative.assoc _ _ _
}

theorem mul_one {n m R} [Lean.Grind.Semiring R] [Fintype m] (A : Matrix n m R) : A * (1 : Matrix m m R) = A := by {
  funext i j
  simp only [mul_def, one_def, mul_if, Lean.Grind.Semiring.mul_one, Lean.Grind.Semiring.mul_zero]
  rw [List.sum_map_if_zero, Fintype.elems_filter_eq_singleton, List.map_singleton, List.sum_cons, List.sum_nil, Lean.Grind.Semiring.add_zero]
}

theorem add_zero {n m R} [Lean.Grind.Semiring R] (A : Matrix n m R) : A + 0 = A := by {
  funext i j
  rw [add_def, zero_def, Lean.Grind.Semiring.add_zero]
}

theorem smul_add {n m R} [Lean.Grind.Semiring R] (k : R) (A B : Matrix n m R) : k • (A + B) = k • A + k • B := by {
  funext i j
  simp only [smul_def, add_def, Lean.Grind.Semiring.left_distrib]
}

theorem add_smul {n m R} [Lean.Grind.Semiring R] (a b : R) (A : Matrix n m R) : (a + b) • A = a • A + b • A := by {
  funext i j
  simp only [smul_def, add_def, Lean.Grind.Semiring.right_distrib]
}

theorem one_smul {n m R} [Lean.Grind.Semiring R] (A : Matrix n m R) : (1 : R) • A = A := by {
  funext i j
  rw [smul_def, Lean.Grind.Semiring.one_mul]
}

end Matrix
