import Mathlib.Tactic.TypeStar

set_option autoImplicit true
namespace LambdaD

universe u

mutual
  inductive TrailType
    | Halt
    | Cons (τ₁ : Type u) (μ : TrailType) (σ : MetaCont) (τ₂ : Type u)
  inductive MetaCont
    | Halt
    | Cons (τ₁ : Type u) (μ₁ : TrailType) (σ₁ : MetaCont) (τ₂ : Type u) (μ₂ : TrailType) (σ₂ : MetaCont)
end
mutual
  def TrailType.toCPS : TrailType → Type u
    | .Halt => PUnit
    | .Cons τ₁ μ σ τ₂ => τ₁ → μ.toCPS → σ.toCPS → τ₂

  def MetaCont.toCPS : MetaCont → Type u
    | .Halt => PUnit
    | .Cons τ₁ μ₁ σ₁ τ₂ μ₂ σ₂ => (τ₁ → μ₁.toCPS → σ₁.toCPS → τ₂) × μ₂.toCPS × σ₂.toCPS
end

inductive IdContType : Type u → TrailType.{u} → MetaCont.{u} → Type u → Type (u + 1)
  | refl τ : IdContType τ .Halt .Halt τ
  | mc_cons τ τ' μ σ : IdContType τ .Halt (.Cons τ μ σ τ' μ σ) τ'
  | tr_cons τ τ' σ : IdContType τ (.Cons τ .Halt σ τ') σ τ'

theorem IdContType.halt_halt_def {τ τ'}
  (h : IdContType τ .Halt .Halt τ')
  : τ = τ' := by cases h; rfl

theorem IdContType.halt_cons_def {τ τ' τ₁ τ₁' μ₁ μ₂ σ₁ σ₂}
  (h : IdContType τ .Halt (.Cons τ₁ μ₁ σ₁ τ₁' μ₂ σ₂) τ')
  : τ = τ₁ ∧ τ' = τ₁' ∧ μ₁ = μ₂ ∧ σ₁ = σ₂ := by cases h; simp

theorem IdContType.cons_def {τ τ' τ₁ τ₁' μ₁ σ₁ σ₂}
  (h : IdContType τ (.Cons τ₁ μ₁ σ₁ τ₁') σ₂ τ')
  : τ = τ₁ ∧ τ' = τ₁' ∧ μ₁ = .Halt ∧ σ₁ = σ₂ := by cases h; simp

def IdContType.idk {τ τ' μ σ}
  : IdContType τ μ σ τ' → (τ → μ.toCPS → σ.toCPS → τ')
  | .refl _ => fun v _ _ => v
  | .mc_cons _ _ _ _ => fun v _ ⟨f, μ', σ'⟩ => f v μ' σ'
  | .tr_cons _ _ _ => fun v f => f v ()

/-- fst :: snd -> thd -/
inductive Compatible : TrailType.{u} → TrailType.{u} → TrailType.{u} → Type (u + 1)
  | halt μ : Compatible .Halt μ μ
  | cons_halt_cons τ τ' μ σ : Compatible (.Cons τ μ σ τ') .Halt (.Cons τ μ σ τ')
  | cons_cons_cons τ₁ τ₁' τ₂ τ₂' μ₁ μ₂ μ₃ σ₁ σ₂ :
      Compatible (.Cons τ₂ μ₂ σ₂ τ₂') μ₃ μ₁ →
      Compatible (.Cons τ₁ μ₁ σ₁ τ₁') (.Cons τ₂ μ₂ σ₂ τ₂') (.Cons τ₁ μ₃ σ₁ τ₁')

theorem Compatible.halt_def {μ₁ μ₂}
  (h : Compatible .Halt μ₁ μ₂)
  : μ₁ = μ₂ := by cases h; rfl

theorem Compatible.cons_halt_def {τ τ' μ μ₃ σ}
  (h : Compatible (.Cons τ μ σ τ') .Halt μ₃)
  : μ₃ = .Cons τ μ σ τ' := by cases h; rfl

theorem Compatible.cons_cons_def {τ₁ τ₁' τ₂ τ₂' μ₁ μ₂ σ₁ σ₂}
  (h : Compatible (.Cons τ₁ μ₁ σ₁ τ₁') (.Cons τ₂ μ₂ σ₂ τ₂') .Halt)
  : False := by cases h

theorem Compatible.cons_cons_cons_def {τ₁ τ₁' τ₂ τ₂' τ₃ τ₃' μ₁ μ₂ μ₃ σ₁ σ₂ σ₃}
  (h : Compatible (.Cons τ₁ μ₁ σ₁ τ₁') (.Cons τ₂ μ₂ σ₂ τ₂') (.Cons τ₃ μ₃ σ₃ τ₃'))
  : τ₁ = τ₃ ∧ τ₁' = τ₃' ∧ σ₁ = σ₃ := by cases h; simp_all

def Compatible.cons_of_cons_cons_cons {τ₁ τ₁' τ₂ τ₂' τ₃ τ₃' μ₁ μ₂ μ₃ σ₁ σ₂ σ₃}
  (h : Compatible (.Cons τ₁ μ₁ σ₁ τ₁') (.Cons τ₂ μ₂ σ₂ τ₂') (.Cons τ₃ μ₃ σ₃ τ₃'))
  : Compatible (.Cons τ₂ μ₂ σ₂ τ₂') μ₃ μ₁ := by cases h; assumption

def Compatible.compose {μ₁ μ₂ μ₃}
  : Compatible μ₁ μ₂ μ₃ → (μ₁.toCPS → μ₂.toCPS → μ₃.toCPS)
  | .halt _ => fun _ m => m
  | .cons_halt_cons _ _ _ _ => fun f _ => f
  | .cons_cons_cons _ _ _ _ _ _ _ _ _ a => fun f g v m s => f v (a.compose g m) s

def TypeD
  (τ : Type u) (μα : TrailType.{u}) (σα : MetaCont.{u}) (α : Type u) (μβ : TrailType.{u}) (σβ : MetaCont.{u}) (β : Type u)
  := (τ → μα.toCPS → σα.toCPS → α) → μβ.toCPS → σβ.toCPS → β

variable {τ τ' τ₁ τ₂ : Type}

def TVar {α μ σ} (x : τ) : TypeD τ μ σ α μ σ α := fun k t m => k x t m

def TNum {α μ σ} (n : Nat) : TypeD Nat μ σ α μ σ α := fun k t m => k n t m

def TLam {α β γ μα μβ μγ σα σβ σγ}
  (f : τ₁ → TypeD τ₂ μα σα α μβ σβ β)
  : TypeD (τ₁ → TypeD τ₂ μα σα α μβ σβ β) μγ σγ γ μγ σγ γ
  := fun k t m => k (fun x g t₁ m₁ => f x g t₁ m₁) t m

def TApp {α β γ δ μα μβ μγ μδ σα σβ σγ σδ}
  (e₁ : TypeD (τ₁ → TypeD τ₂ μα σα α μβ σβ β) μγ σγ γ μδ σδ δ)
  (e₂ : TypeD τ₁ μβ σβ β μγ σγ γ)
  : TypeD τ₂ μα σα α μδ σδ δ
  := fun k t m => e₁ (fun v₁ t₁ m₁ => e₂ (fun v₂ t₂ m₂ => v₁ v₂ k t₂ m₂) t₁ m₁) t m

def TShift {γ γ' α β μ_id μ₁ μ₂ μβ σ_id σ₁ σ₂ σβ}
  (is_id : IdContType γ μ_id σ_id γ')
  (f : (τ → TypeD τ₁ μ₁ σ₁ τ₂ μ₂ σ₂ α) → TypeD γ μ_id σ_id γ' .Halt σβ β)
  : TypeD τ μβ (.Cons τ₁ μ₁ σ₁ τ₂ μ₂ σ₂) α μβ σβ β
  := fun k t m => f (fun v k' t' m' => k v t ⟨k', t', m'⟩) is_id.idk () m

def TControl {α β γ γ' μ_id μ₁ μ₂ μγ μα μβ σ_id σ₁ σα σβ}
  (is_id : IdContType γ μ_id σ_id γ')
  (c₁ : Compatible (.Cons τ₁ μ₁ σ₁ τ₂) μ₂ μγ)
  (c₂ : Compatible μβ μγ μα)
  (f : (τ → TypeD τ₁ μ₁ σ₁ τ₂ μ₂ σα α) → TypeD γ μ_id σ_id γ' .Halt σβ β)
  : TypeD τ μα σα α μβ σβ β
  := fun k t m => f (fun v k' t' m' => k v (c₂.compose t (c₁.compose k' t')) m') is_id.idk () m

def TShift0 {τ₀ τ₀' α β μ₀ μ₀' μ₁ μ₂ μβ σ₀ σ₀' σ₁ σ₂}
  (f : (τ → TypeD τ₁ μ₁ σ₁ τ₂ μ₂ σ₂ α) → TypeD τ₀ μ₀ σ₀ τ₀' μ₀' σ₀' β)
  : TypeD τ μβ (.Cons τ₁ μ₁ σ₁ τ₂ μ₂ σ₂) α μβ (.Cons τ₀ μ₀ σ₀ τ₀' μ₀' σ₀') β
  := fun k t ⟨k₀, t₀, m₀⟩ => f (fun v k' t' m' => k v t ⟨k', t', m'⟩) k₀ t₀ m₀

def TControl0 {τ₀ τ₀' α β μ₀ μ₀' μ₁ μ₂ μα μβ μγ σ₀ σ₀' σ₁ σα}
  (c₁ : Compatible (.Cons τ₁ μ₁ σ₁ τ₂) μ₂ μγ)
  (c₂ : Compatible μβ μγ μα)
  (f : (τ → TypeD τ₁ μ₁ σ₁ τ₂ μ₂ σα α) → TypeD τ₀ μ₀ σ₀ τ₀' μ₀' σ₀' β)
  : TypeD τ μα σα α μβ (.Cons τ₀ μ₀ σ₀ τ₀' μ₀' σ₀') β
  := fun k t ⟨k₀, t₀, m₀⟩ => f (fun v k' t' m' => k v (c₂.compose t (c₁.compose k' t')) m') k₀ t₀ m₀

def TPrompt0 {α β γ γ' μ_id μα μβ σ_id σα σβ}
  (is_id : IdContType γ μ_id σ_id γ')
  (e : TypeD γ μ_id σ_id γ' .Halt (.Cons τ μα σα α μβ σβ) β)
  : TypeD τ μα σα α μβ σβ β
  := fun k t m => e is_id.idk () ⟨k, t, m⟩

def go : {μ : TrailType} → IdContType τ μ .Halt τ → TypeD τ μ .Halt τ μ .Halt τ → τ
  | .Halt, .refl _ , e => e (fun z _ _ => z) () ()
  | .Cons τ₁ .Halt σ τ₂, h, e => by {
    cases h
    exact e (fun z _ _ => z) (fun t _ _ => t) ()
  }

end LambdaD

namespace DF2

abbrev DF2Type (τ σα α σβ β) := LambdaD.TypeD τ .Halt σα α .Halt σβ β

def DF2Var {τ α σα} (x : τ) : DF2Type τ σα α σα α := LambdaD.TVar x

def DF2Num {α σα} (n : Nat) : DF2Type Nat σα α σα α := LambdaD.TNum n

def DF2Lam {τ₁ : Type} {τ₂ α β γ σα σβ σγ}
  (f : τ₁ → DF2Type τ₂ σα α σβ β)
  : DF2Type (τ₁ → DF2Type τ₂ σα α σβ β) σγ γ σγ γ
  := LambdaD.TLam f

def DF2App {τ₁ τ₂ α β γ δ σα σβ σγ σδ}
  (e₁ : DF2Type (τ₁ → DF2Type τ₂ σα α σβ β) σγ γ σδ δ)
  (e₂ : DF2Type τ₁ σβ β σγ γ)
  : DF2Type τ₂ σα α σδ δ
  := LambdaD.TApp e₁ e₂

def DF2Shift {τ τ₁ τ₂ α β γ γ' σ_id σ₁ σβ}
  (id_c_t : LambdaD.IdContType γ .Halt σ_id γ')
  (e : (τ → DF2Type τ₁ σ₁ τ₂ σ₁ α) → DF2Type γ σ_id γ' σβ β)
  : DF2Type τ (.Cons τ₁ .Halt .Halt τ₂ .Halt .Halt) α σβ β
  := fun c _ m => e (fun v c' _ m' => c v () ⟨fun v' _ _ => c' v' () m', (), ()⟩) id_c_t.idk () m

def DF2Reset {γ γ' τ α β σ_id σα}
  (id_c_t : LambdaD.IdContType γ .Halt σ_id γ')
  (e : DF2Type γ σ_id γ' (.Cons τ .Halt .Halt α .Halt .Halt) β)
  : DF2Type τ σα α σα β
  := fun c _ m => e id_c_t.idk () ⟨fun v _ _ => c v () m, (), ()⟩

end DF2
