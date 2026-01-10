
set_option autoImplicit true

universe u

def AnswerTyped (α τ β : Type u) := (τ → α) → β

def FunType (τ₁ α τ₂ β : Type u) := τ₁ → AnswerTyped α τ₂ β

def app {τ₁ τ₂ α β γ δ} (M₁ : AnswerTyped γ (FunType τ₁ α τ₂ β) δ) (M₂ : AnswerTyped β τ₁ γ) : AnswerTyped α τ₂ δ :=
  fun k => M₁ (fun f => M₂ (fun v => f v k))

def exp {τ α} (M : τ) : AnswerTyped α τ α := fun k => k M

def shift {τ t α β γ} (M : FunType τ t α t → AnswerTyped γ γ β) : AnswerTyped α τ β
  := fun k => M (fun v k' => k' (k v)) id

def reset {τ γ} (M : AnswerTyped γ γ τ) : τ := M id

def bind {α A B β} (f : A → B) (M : AnswerTyped α A β) : AnswerTyped α B β :=
  fun k => M (fun v => k (f v))

#eval reset $ bind (fun b : Bool => if b then 3 else 2) (exp (2 = 3))
#eval (reset $ bind (· ++ " world") $ shift (fun k (_ : Unit → Unit) _ => k "hello" id)) ()
