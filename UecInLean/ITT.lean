import Mathlib.Order.Lattice
-- import Mathlib.Tactic.Choose

-- universe u v w

-- def ac (A : Sort u) (B : A → Sort v) (C : (a : A) → B a → Sort w) :
--   ((x : A) → Σ' y : B x, C x y) → Σ' f : (x : A) → B x, (x : A) → C x (f x) :=
-- by
--   intro z
--   let zx1 : (x : A) → B x := by {
--     intro x
--     exact (z x).1
--   }
--   let zx2 : (x : A) → C x (zx1 x) := by {
--     intro x
--     exact (z x).2
--   }
--   exact ⟨zx1, zx2⟩

-- #print axioms ac

-- #print axioms Classical.choose


-- theorem ac' (A : Sort u) (B : A → Sort v) (C : (a : A) → B a → Prop) :
--   (∀ (x : A), ∃ y : B x, C x y) → ∃ f : (x : A) → B x, ∀ (x : A), C x (f x) := by {
--   intro h
--   let zx1 : (x : A) → B x := by {
--     intro x
--     exact Classical.choose (h x)
--   }
--   let zx2 : (x : A) → C x (zx1 x) := by {
--     intro x
--     exact Classical.choose_spec (h x)
--   }
--   exact ⟨zx1, zx2⟩
-- }
-- #print axioms ac'



-- inductive MyExist (A : Sort u) (P : A → Sort v) : Type (max u v) where
-- | intro (w : A) (h : P w) : MyExist A P

-- def aa (A : Sort u) (B : A → Sort v) (C : (a : A) → B a → Prop)
--   (h : (x : A) → MyExist (B x) (C x)) : ∀ x : A, B x := by {
--   let f : (x : A) → B x := by {
--     intro x
--     cases (ac A B C h) with
--     | intro w hw => exact w
--   }
--   exact f
-- }
-- #print axioms aa

#print axioms Classical.decRel

structure W (A : Type) (B : A → Type) where
  sup ::
  a : A
  b : B a → W A B

#check W.rec

theorem W.ext {A B} {c d : W A B} (ha : c.a = d.a) (hb : c.b = ha ▸ d.b) : c = d := by {
  obtain ⟨a, b⟩ := c
  obtain ⟨a', b'⟩ := d
  cases ha
  cases hb
  rfl
}

def W.elim.{u} {A B} (C : W A B → Sort u) (c : W A B) (d : (x : A) → (y : B x → W A B) → (z : (v : B x) → C (y v)) → C (.sup x y)) : C c := by {
  obtain ⟨a, b⟩ := c
  exact d a b (fun v => W.elim C (b v) d)
}

section
-- Nat と MyNat が同型であることを証明

def MyNat := W (Fin 2) (fun x => match x with | 0 => Empty | 1 => Unit)

def first : MyNat → Nat
  | .sup 0 _ => 0
  | .sup 1 b => first (b ()) + 1

def first' : Nat → MyNat
  | 0 => .sup 0 (fun x => by cases x)
  | n + 1 => .sup 1 (fun _ => first' n)

theorem first_first'_id (n : Nat) : first (first' n) = n := by {
  induction n with
  | zero => rfl
  | succ _ ih => simpa [first, first'] using ih
}

theorem first'_first_id (x : MyNat) : first' (first x) = x := by {
  apply W.elim (fun x => first' (first x) = x)
  intro a _ ih
  match a with
  | 0 => exact W.ext (by rfl) (by funext v; cases v)
  | 1 => exact W.ext (by rfl) (by funext; exact ih ())
}

end section

section

-- 順序数全体

inductive MyOrdI where
  | zero : MyOrdI
  | succ : MyOrdI → MyOrdI
  | limit : (Nat → MyOrdI) → MyOrdI

def MyOrdW := W (Fin 3) (fun x => match x with | 0 => Empty | 1 => Unit | 2 => Nat)

def second : MyOrdW → MyOrdI
  | .sup 0 _ => .zero
  | .sup 1 b => .succ (second (b ()))
  | .sup 2 b => .limit (fun n => second (b n))

def second' : MyOrdI → MyOrdW
  | .zero => .sup 0 (fun x => by cases x)
  | .succ o => .sup 1 (fun _ => second' o)
  | .limit f => .sup 2 (fun n => second' (f n))

theorem second_second'_id (o : MyOrdI) : second (second' o) = o := by {
  induction o with
  | zero => rfl
  | succ _ ih => simpa [second, second'] using ih
  | limit _ ih => simpa [second, second'] using funext ih
}

theorem second'_second_id (x : MyOrdW) : second' (second x) = x := by {
  apply W.elim (fun x => second' (second x) = x)
  intro a _ ih
  match a with
  | 0 => exact W.ext (by rfl) (by funext v; cases v)
  | 1 => exact W.ext (by rfl) (by funext _; exact ih ())
  | 2 => exact W.ext (by rfl) (by funext n; exact ih n)
}

end section

