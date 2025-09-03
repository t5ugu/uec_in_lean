
set_option autoImplicit true

abbrev ℕ := Nat
abbrev Set := Type

inductive Lst (A : Set) : Set where
  | nil : Lst A
  | cons : A → Lst A → Lst A

inductive Vec (A : Set) : ℕ → Set where
  | nil : Vec A .zero
  | cons : {n : ℕ} → A → Vec A n → Vec A (.succ n)

def appendL : Lst A → Lst A → Lst A
  | Lst.nil, l => l
  | Lst.cons x xs, ys => Lst.cons x (appendL xs ys)

def appendV : Vec A m → Vec A n → Vec A (m + n) := by {
  intro v l
  match v with
  | Vec.nil =>
    rw [Nat.zero_add]
    exact l
  | Vec.cons x xs =>
    rw [Nat.succ_add]
    exact Vec.cons x (appendV xs l)
}

def mapL (f : A → B) : Lst A → Lst B
  | Lst.nil => Lst.nil
  | Lst.cons x xs => Lst.cons (f x) (mapL f xs)

def mapV (f : A → B) : Vec A n → Vec B n
  | Vec.nil => Vec.nil
  | Vec.cons x xs => Vec.cons (f x) (mapV f xs)

def headL : Lst A → Option A
  | Lst.nil => none
  | Lst.cons x _ => some x

def headV : Vec A (n + 1) → A
  | Vec.cons x _ => x

def lookupL : Lst A → ℕ → Option A
  | Lst.nil, _ => none
  | Lst.cons x _, .zero => some x
  | Lst.cons _ xs, .succ n => lookupL xs n

inductive Fin' : ℕ → Type
  | zero : {n : ℕ} → Fin' (.succ n)
  | succ : {n : ℕ} → Fin' n → Fin' (.succ n)

def lookupV : Vec A n → Fin' n → A
  | Vec.cons x _, .zero => x
  | Vec.cons _ xs, .succ n => lookupV xs n

def lengthL : Lst A → ℕ
  | Lst.nil => 0
  | Lst.cons _ xs => 1 + lengthL xs

def lookupL2 : (l : Lst A) → Fin' (lengthL l) → A
  | Lst.nil, .zero => nomatch fin
  | Lst.cons x xs, .zero => x
  | Lst.cons _ xs, .succ n => lookupL2 xs n
