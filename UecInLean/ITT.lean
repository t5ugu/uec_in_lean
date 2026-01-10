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
