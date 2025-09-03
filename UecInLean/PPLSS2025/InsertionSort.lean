
set_option autoImplicit true

abbrev ℕ := Nat
abbrev Set := Type

/-- b: 下限 -/
inductive OList : ℕ → Set where
  | nil : OList b
  | cons : (n : ℕ) → b ≤ n → OList n → OList b

abbrev z_le_n {n : ℕ} : 0 ≤ n := Nat.zero_le n
abbrev s_le_s {m n : ℕ} : m ≤ n → m.succ ≤ n.succ := Nat.succ_le_succ

def goodList : OList 0 := .cons 1 z_le_n (.cons 2 (s_le_s z_le_n) .nil)

def insert {b : ℕ} (n : ℕ) (b_le_n : b ≤ n) : OList b → OList b
  | .nil => .cons n b_le_n .nil
  | .cons m b_le_m l =>
    if h : n ≤ m
    then .cons n b_le_n (.cons m h l)
    else .cons m b_le_m (insert n (Nat.le_of_lt <| Nat.not_le.mp h) l)

def isort : List ℕ → OList 0
  | [] => .nil
  | n :: l => insert n (z_le_n) (isort l)

#eval isort [3, 1, 2, 0, 5, 0]
