import UecInLean.Category.Basic

open UecInLean
universe u₀ v₀ u₁ v₁ u v

inductive Path (Obj : Type u) (Hom : Obj → Obj → Type v) : Obj → Obj → Type (max u v)
  | nil (A : Obj) : Path Obj Hom A A
  | cons {A B C : Obj} (f : Hom A B) (p : Path Obj Hom B C) : Path Obj Hom A C

def Path.length {Obj : Type u} {Hom : Obj → Obj → Type v}
  {A B : Obj} : Path Obj Hom A B → Nat
  | .nil _ => 0
  | .cons _ p => (Path.length p).succ

def PathLE1 (Obj Hom A B) := { p : Path Obj Hom A B // Path.length p ≤ 1 }

def Path.comp {Obj : Type u} {Hom : Obj → Obj → Type v}
  {A C} (B)
  : Path Obj Hom A B → Path Obj Hom B C → Path Obj Hom A C
  | .nil _, q => q
  | .cons f p, q => .cons f (p.comp _ q)

def Path.comps {Obj : Type u} {Hom : Obj → Obj → Type v}
  {n : Nat} {b : Fin (n + 1) → Obj} (Ψ : (i : Fin n) → Path Obj Hom (b ⟨i, by grind⟩) (b i.succ)) : Path Obj Hom (b 0) (b ⟨n, by grind⟩) := by {
  induction n with
  | zero => exact .nil _
  | succ n ih =>
    let b₀ : Fin (n + 1) → Obj := fun i => b ⟨i, by grind⟩
    have Ψ₀ : (i : Fin n) → Path Obj Hom (b₀ ⟨i, by grind⟩) (b₀ i.succ) := fun i => Ψ ⟨i, by grind⟩

    apply Path.comp (b ⟨n, by grind⟩) (ih Ψ₀) (Ψ ⟨n, by grind⟩)
}

class VirtualDoubleCategory (Obj : Type u₀) [Category.{v₀} Obj] where
  HHom : Obj → Obj → Type u₁
  Cell (a₀ aₙ b₀ b₁ : Obj) : Path Obj HHom a₀ aₙ → PathLE1 Obj HHom b₀ b₁ → (a₀ ⟶ b₀) → (aₙ ⟶ b₁) → Type v₀
  Cell_comp {n : Nat} {a : Fin (n + 1) → Obj} {b : Fin (n + 1) → Obj}
    (f : (i : Fin (n + 1)) → Hom Obj (a i) (b i))
    (Φ : (i : Fin n) → Path Obj HHom (a ⟨i, by grind⟩) (a i.succ))
    (Ψ : (i : Fin n) → PathLE1 Obj HHom (b ⟨i, by grind⟩) (b (i.succ)))
    (φ : (i : Fin n) → Cell (a ⟨i, by grind⟩) (a i.succ) (b ⟨i, by grind⟩) (b (i.succ)) (Φ i) (Ψ i) (f ⟨i, by grind⟩) (f (i.succ)))
    (c₀ c₁ : Obj) (g₀ : b ⟨0, by grind⟩ ⟶ c₀) (g₁ : b ⟨n, by grind⟩ ⟶ c₁)
    (Ξ : PathLE1 Obj HHom c₀ c₁)
    (ψ : Cell (b ⟨0, by grind⟩) (b ⟨n, by grind⟩) c₀ c₁ (Path.comps (fun i => (Ψ i).val)) Ξ g₀ g₁)
    : Cell (a ⟨0, by grind⟩) (a ⟨n, by grind⟩) c₀ c₁ (Path.comps Φ) Ξ (f ⟨0, by grind⟩ ≫ g₀) (f ⟨n, by grind⟩ ≫ g₁)
