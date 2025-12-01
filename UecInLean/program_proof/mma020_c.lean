-- import Mathlib.Tactic.Linarith

inductive MA
  | M
  | A

instance : Repr MA where
  reprPrec
    | MA.M, _ => "M"
    | MA.A, _ => "A"

instance : Inhabited MA where
  default := MA.A

def MA.beq : MA → MA → Bool
  | MA.M, MA.M => true
  | MA.A, MA.A => true
  | _, _ => false

instance : BEq MA where
  beq := MA.beq

inductive MAString : Nat → Type
  | nil : MAString 0
  | cons {n} (hd : MA) (tl : MAString n) : MAString (n + 1)

def MAString.get {n} (s : MAString n) (i : Fin n) : MA :=
  match s, i with
  | MAString.nil, ⟨_, h⟩ => nomatch h
  | MAString.cons hd _, ⟨0, _⟩ => hd
  | MAString.cons _ tl, ⟨i + 1, h⟩ => tl.get ⟨i, Nat.lt_of_succ_lt_succ h⟩

instance {n} : GetElem (MAString n) Nat MA (fun _ i => i < n) where
  getElem s i h := s.get ⟨i, h⟩

def MAString.isMMAString {n} (s : MAString n) : Bool :=
  if n < 3 then false else loop 0
where
  loop (i : Nat) : Bool :=
    if h : i ≥ n - 2 then false else

    if s[i] == MA.M && s[i + 1] == MA.M && s[i + 2] == MA.A then
      true
    else
      loop (i + 1)

def decode {b} (num : BitVec b) : MAString b :=
  let rec loop (l) : MAString l :=
    match l with
    | 0 => MAString.nil
    | k + 1 =>
      let bit_val := if num.getLsbD k then MA.M else MA.A
      MAString.cons bit_val (loop k)
  loop b

#eval (@decode 4 12).isMMAString

def countMMA (b : Nat) : Nat :=
  List.range' (2^(b-1)) (2^b) |> List.map (MAString.isMMAString ∘ decode ∘ BitVec.ofNat b) |> List.count true

#eval countMMA 9

def fib (n : Nat) : Nat :=
  let rec loop (i j) : Nat → Nat
    | 0 => i
    | k + 1 => loop j (i + j) k
  loop 0 1 n

def fib_acc (n : Nat) : Nat :=
  List.range n |> List.map fib |> List.sum

def countAux : Nat → Nat
  | 0 => 0
  | n + 1 => 2 * countAux n + fib_acc n

-- #eval (fun n => countMMA n - countAux n) 10
