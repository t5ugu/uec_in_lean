import Mathlib.Tactic.TypeStar

def PCont (Ar Ri Ro : Type*) := (Ar → Ri) → Ro

namespace PCont

def pure {r A} (a : A) : PCont A r r :=
  fun k => k a

def bind {R₁ R₂ R₃ A B} (c : PCont A R₂ R₃) (f : A → PCont B R₁ R₂) : PCont B R₁ R₃ := fun k => c (fun a => f a k)

instance instMonadPCont {R} : Monad (PCont · R R) where
  pure := pure
  bind := bind

def run {A P} (m : PCont A A P) : P := m id

#eval run $ bind (pure 3) (fun x => pure (x + 1))

def reset {A P} (c : PCont A A P) (Q : Type* := P) : PCont P Q Q := pure (run c)
def runReset {A P} : PCont A A P → P := run

#eval run $ reset (pure "hello")

def shift {A B R Q} (f : (A → R) → PCont B B Q) : PCont A R Q := run ∘ f
def shiftP {A R Q} (f : (A → R) → Q) : PCont A R Q := shift (pure ∘ f)

#eval run $ bind (reset $ bind (shift (fun _ => pure 10)) (fun x => pure (3 + x))) (fun x => pure (x - 1))

#eval run $ reset $ bind (shift (fun _ => pure "hi")) (fun x => pure (3 + x))

def ex1 := runReset $ bind (shift (fun k => pure k)) (fun x => pure (2 + x))
#eval ex1 10

def map {A A' R₁ R₂ R₂'} (pre : A → A') (post : R₂ → R₂') : PCont A R₁ R₂ → PCont A' R₁ R₂' :=
  fun c k => post $ c (k ∘ pre)

def seq {R₁ R₂ R₃ A B} (cf : PCont (A → B) R₂ R₃) (ca : PCont A R₁ R₂) : PCont B R₁ R₃ :=
  bind cf (fun f k => ca (k ∘ f))

def seqLeft {R₁ R₂ R₃ A B} (ca : PCont A R₂ R₃) (cb : PCont B R₁ R₂) : PCont A R₁ R₃ :=
  bind ca (fun a => bind cb (fun _ => pure a))

def seqRight {R₁ R₂ R₃ A B} (ca : PCont A R₂ R₃) (cb : PCont B R₁ R₂) : PCont B R₁ R₃ :=
  bind ca (fun _ => cb)

def resetMap {A P} (f : A → P) (c : PCont A P P) (Q : Type* := P) : PCont P Q Q := reset (map f id c) Q
def runResetMap {A P Q} (f : A → P) (c : PCont A P Q) : Q := run $ map f id c

def ex3_1 := map (5 * ·) id $ resetMap (· + 3 * 4) $ shift (fun _ => pure (10))
#eval run ex3_1

def ex3_2 := map (· ++ " world") id $ resetMap (fun c : Bool => if c then "hello" else "hi") $ shift (fun _ => pure "goodbye")
#eval run ex3_2

def ex3_3 := run $ resetMap (let x : String := ·; (x, x)) $ shift (fun _ => pure ("test", "a"))
#eval ex3_3

def ex3_4 := String.length $ run $ resetMap (fun v : Nat => "x" ++ toString v) $ shift (fun _ => pure "123")
#eval ex3_4

def ex4_times : List Nat → Nat
  | [] => 1
  | 0 :: _ => 0
  | x :: xs => x * ex4_times xs

def ex5_0 {A R : Type*} := @shift A (A → R) R (A → R) (fun k => pure k)

def ex5_1 := runResetMap (fun x : Nat => 5 * (x + 3 * 4)) $ ex5_0
#eval ex5_1 0

def ex5_2 := runResetMap (fun b : Bool => (if b then "hello" else "hi") ++ " world") $ ex5_0
#eval ex5_2 false

def ex5_3 := runResetMap (fun z:Nat => Prod.fst (let x := z; (x, x))) $ ex5_0
#eval ex5_3 12

def ex5_4 := runResetMap (fun v : Nat => "x" ++ toString v) $ ex5_0
#eval ex5_4 7

def ex6_id {α : Type*} : List α → PCont (List α) (List α) (List α → List α)
  | [] => shift (fun k => pure k)
  | x :: xs => bind (ex6_id xs) (fun rec k => k (x :: rec))
#eval (runReset (ex6_id [1, 2, 3])) [4, 5, 6]

inductive tree
  | Empty
  | Node (left : tree) (value : Nat) (right : tree)

inductive result (α : Type*)
  | Done : result α
  | Next : Nat → (Unit → result α) → result α

-- def yield {α} (n : Nat) : PCont Unit (result α) (result α) :=
--   shiftP (fun k => .Next n k)

-- def walk {α} : tree → PCont Unit Unit (result α)
--   | tree.Empty => fun _ => .Done
--   | tree.Node l v r =>
--       bind (walk l) (fun _ =>
--       bind (yield v) (fun _ =>
--       walk r))

-- def start {α} (t : tree) : PCont Unit (result α) (result α) := reset (walk t)

-- def print_nodes (t : tree) : IO Unit := loop (run $ start t)
-- where
--   loop : result Unit → IO Unit
--     | .Done => return
--     | .Next n k => do {
--       IO.print n;
--       loop (k ())
--     }

-- #eval print_nodes (tree.Node (tree.Node tree.Empty 1 tree.Empty) 2 (tree.Node tree.Empty 3 tree.Empty))

end PCont
