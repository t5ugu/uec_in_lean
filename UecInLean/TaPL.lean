
namespace UEC.tapl

-- 型システム入門 プログラミング言語と型の理論 ISBN 978-4-274-06911-6

inductive Term
  | var (n : Nat)
  | abs (t : Term)
  | app (t₁ t₂ : Term)
infixl:200 " ∘ " => Term.app
notation:200 "L." t:100 => Term.abs t

instance (n : Nat) : OfNat Term n where
  ofNat := Term.var n

/-- Term が n項(外からn個目の`L.`に包まれている)であること -/
inductive deBruijn : Nat -> Term -> Prop
  | var {i n} : i < n -> deBruijn n (.var i)
  | abs {n t₁} : deBruijn (n + 1) t₁ -> deBruijn n (L. t₁)
  | app {n t₁ t₂} : deBruijn n t₁ -> deBruijn n t₂ -> deBruijn n (t₁ ∘ t₂)

theorem deBruijn_var_iff {i n} : deBruijn n (.var i) ↔ i < n := by {
  constructor
  · intro h
    rcases h with ⟨h⟩
    exact h
  · intro h
    exact deBruijn.var h
}

theorem deBruijn_abs_iff {n t₁} : deBruijn n (L. t₁) ↔ deBruijn (n + 1) t₁ := by {
  constructor
  · intro h
    rcases h with ⟨⟩ | ⟨h⟩
    exact h
  · intro h
    exact deBruijn.abs h
}

theorem deBurijn_app_left {n t₁ t₂} : deBruijn n (t₁ ∘ t₂) → deBruijn n t₁ := by {
  intro h
  rcases h with ⟨⟩ | ⟨⟩ | ⟨h₁, _⟩
  exact h₁
}

theorem deBurijn_app_right {n t₁ t₂} : deBruijn n (t₁ ∘ t₂) → deBruijn n t₂ := by {
  intro h
  rcases h with ⟨⟩ | ⟨⟩ | ⟨_, h₂⟩
  exact h₂
}

theorem deBruijn_cast {n d t} (h : deBruijn n t) : deBruijn (n + d) t := by {
  cases t
  · rw [deBruijn_var_iff] at h ⊢
    exact Nat.lt_add_right d h
  · rw [deBruijn_abs_iff] at h ⊢
    rw [Nat.add_right_comm]
    exact deBruijn_cast h
  · apply deBruijn.app
    · exact deBruijn_cast (deBurijn_app_left h)
    · exact deBruijn_cast (deBurijn_app_right h)
}
/--
  var: 打ち切り値 c 以上のインデックスをシフト数 d だけ持ち上げる
  abs: 抽象の中では束縛変数のインデックスが 1 つ増える
  app: それぞれシフト
-/
def shift (c d : Nat) : Term -> Term
  | .var k => if k < c then .var k else .var (k + d)
  | .abs t₁ => L. (shift (c + 1) d t₁)
  | .app t₁ t₂ => shift c d t₁ ∘ shift c d t₂

#eval shift 0 2 (L. L. 1 ∘ (0 ∘ 2))
#eval shift 0 2 (L. 0 ∘ 1 ∘ (L. 0 ∘ 1 ∘ 2))

/-- n項のを d個シフトしたら n+d項 -/
theorem deBruijn_shift {n c d t} (h : deBruijn n t) : deBruijn (n + d) (shift c d t) := by {
  cases t
  case var k =>
    unfold shift
    split
    · exact deBruijn_cast h
    · apply deBruijn.var
      rw [deBruijn_var_iff] at h
      exact Nat.add_lt_add_right h d
  case abs t =>
    unfold shift
    rw [deBruijn_abs_iff, Nat.add_right_comm]
    apply deBruijn_shift
    exact deBruijn_abs_iff.mp h
  case app t₁ t₂ =>
    unfold shift
    apply deBruijn.app
    · exact deBruijn_shift (deBurijn_app_left h)
    · exact deBruijn_shift (deBurijn_app_right h)
}

def subst (j : Nat) (s : Term) : Term -> Term
  | .var k => if k = j then s else .var k
  | .abs t₁ => L. (subst (j + 1) (shift 0 1 s) t₁)
  | .app t₁ t₂ => subst j s t₁ ∘ subst j s t₂
notation:max "[" j:0 " ↦ " s:0 "] " t:300 => subst j s t

/-- 演習6.2.6. -/
theorem subst_deBruijn {n j s t} (hs : deBruijn n s) (ht : deBruijn n t) (h : j ≤ n) : deBruijn n [j ↦ s]t := by {
  cases t
  case var k =>
    unfold subst
    split
    exact hs; exact ht
  case abs t₁ =>
    unfold subst
    rw [deBruijn_abs_iff]
    apply subst_deBruijn
    · exact deBruijn_shift hs
    · exact deBruijn_abs_iff.mp ht
    · exact Nat.add_le_add_right h 1
  case app t₁ t₂ =>
    unfold subst
    apply deBruijn.app
    · exact subst_deBruijn hs (deBurijn_app_left ht) h
    · exact subst_deBruijn hs (deBurijn_app_right ht) h
}

/-- `.var 0` が存在しない保障がないと、おかしくなるかも? -/
def downshift (c : Nat) : Term -> Term
  | .var k => if k < c then .var k else .var (k - 1)
  | .abs t₁ => L. (downshift (c + 1) t₁)
  | .app t₁ t₂ => downshift c t₁ ∘ downshift c t₂

inductive beta : Term -> Term -> Prop
  | E_APP1 {t₁ t₁' t₂} : beta t₁ t₁' -> beta (t₁ ∘ t₂) (t₁' ∘ t₂)
  | E_APP2 {t₁ t₂ t₂'} : beta t₂ t₂' -> beta (t₁ ∘ t₂) (t₁ ∘ t₂')
  | E_APPABS {t₁₂ t₂} : beta ((L. t₁₂) ∘ (L. t₂)) (downshift 0 ([0 ↦ (L. t₂)] t₁₂))
infixl:50 " →β " => beta

class inductive betas (s : Term) : Term -> Prop
  | one {t} : beta s t -> betas s t
  | succ {t t'} : betas s t -> beta t t' -> betas s t'
infixl:50 " →β* " => betas

theorem beta_betas_betas {t₁ t₂ t₃} (h₁ : t₁ →β t₂) (h₂ : t₂ →β* t₃) : t₁ →β* t₃ := by {
  induction h₂ with
  | one h => exact betas.succ (betas.one h₁) h
  | succ hs h ih => exact betas.succ ih h
}

theorem betas_betas_betas {t₁ t₂ t₃} (h₁ : t₁ →β* t₂) (h₂ : t₂ →β* t₃) : t₁ →β* t₃ := by {
  induction h₁ with
  | one h => exact beta_betas_betas h h₂
  | succ hs h ih => exact ih (beta_betas_betas h h₂)
}

instance transBB : Trans beta beta betas where
  trans h h' := betas.succ (betas.one h) h'

instance transBsB : Trans betas beta betas where
  trans := betas.succ

instance transBBs : Trans beta betas betas where
  trans := beta_betas_betas

instance transBsBs : Trans betas betas betas where
  trans := betas_betas_betas

def β (s) {t} [betas s t] : Term := t
theorem β_spec {s t} [betas s t] : @β s t _ = t := by rw [β]

def tru := L. L. 0
def fls := L. L. 1
def test := L. L. L. 0 ∘ 1 ∘ 2
def and := L. L. 0 ∘ 1 ∘ fls

def omega : Term := (L. 0 ∘ 0) ∘ (L. 0 ∘ 0)
instance betas_omega : omega →β* omega := .one .E_APPABS
