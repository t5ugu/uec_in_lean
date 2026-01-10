
abbrev I := Bool
instance : OfNat I 0 := ⟨false⟩
instance : OfNat I 1 := ⟨true⟩
def I.inv : I → I := Bool.not
prefix:70 "~" => I.inv

universe u

def FaceLattice := Bool
def FaceLattice.none : FaceLattice := false
def FaceLattice.all : FaceLattice := true
def FaceLattice.isZero (i : I) : FaceLattice := !i
def FaceLattice.isOne (i : I) : FaceLattice := i
def FaceLattice.ofI := isOne
def FaceLattice.and (φ ψ : FaceLattice) : FaceLattice := φ && ψ
def FaceLattice.or (φ ψ : FaceLattice) : FaceLattice := φ || ψ

theorem FaceLattice.nontrivial (r : I) : FaceLattice.and (.isOne r) (.isZero r) = .none := Bool.and_not_self r

inductive PathP {A : I → Type u} : A 0 → A 1 → Type u
  | mk (p : (i : I) → A i) : PathP (p 0) (p 1)

inductive Path (A : Type u) : A → A → Type u
  | refl {a : A} : Path _ a a
notation:50 a:100 " ≡ " b:100 => Path _ a b

def Path.app {A : Type u} {a b : A} (_ : a ≡ b) : I → A
  | 0 => a
  | 1 => b

def transport {A B : Type u} : A ≡ B → A → B
  | .refl => id

inductive System
