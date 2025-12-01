-- https://github.com/Arthur742Ramos/ComputationalPathsLean/blob/main/ComputationalPaths/Path/Basic/Core.lean

set_option autoImplicit true

structure Path {A : Type} (a b : A) where
  ofEq ::
  toEq : a = b

namespace Path
variable {A : Type} {a b c d : A}

def refl (a : A) : Path a a := ⟨rfl⟩

@[simp] theorem toEq_ofEq : toEq (ofEq h) = h := rfl
@[simp] theorem ofEq_toEq : ofEq (toEq p) = p := rfl

def trans (p : Path a b) (q : Path b c) : Path a c := ⟨p.toEq.trans q.toEq⟩
def symm (p : Path a b) : Path b a := ⟨p.toEq.symm⟩

@[simp] theorem symm_refl (a : A) : symm (refl a) = refl a := rfl

theorem symm_trans (p : Path a b) (q : Path b c) : symm (trans p q) = trans (symm q) (symm p) := rfl

@[simp] theorem trans_refl (p : Path a b) : trans p (refl b) = p := rfl
@[simp] theorem refl_trans (p : Path a b) : trans (refl a) p = p := rfl

@[simp]
theorem trans_assoc (p : Path a b) (q : Path b c) (r : Path c d) :  trans (trans p q) r = trans p (trans q r) := rfl

@[simp] theorem symm_symm (p : Path a b) : symm (symm p) = p := rfl

theorem toEq_trans (p : Path a b) (q : Path b c) : toEq (trans p q) = (toEq p).trans (toEq q) := rfl
