
set_option autoImplicit true

abbrev ℕ := Nat
abbrev Set := Type

inductive Exp : Set where
  | tru  : Exp
  | fls  : Exp
  | num  : ℕ → Exp
  | ifte : Exp → Exp → Exp → Exp

def exp1 : Exp := .ifte .tru (.num 1) (.num 0)

def exp2 : Exp := .ifte (.num 1) (.num 1) (.num 0)

def exp3 : Exp := .ifte .tru (.num 1) .fls

inductive Val : Set where
  | vtru : Val
  | vfls : Val
  | vnum : ℕ → Val

def interp : Exp → Val
  | .tru  => .vtru
  | .fls  => .vfls
  | .num n => .vnum n
  | .ifte c t e =>
    match interp c with
    | .vtru => interp t
    | .vfls => interp e
    | .vnum n => sorry

inductive Ty : Set where
  | boolty : Ty
  | numty  : Ty

inductive TExp : Ty → Set where
  | tru  : TExp .boolty
  | fls  : TExp .boolty
  | num  : ℕ → TExp .numty
  | ifte : TExp .boolty → TExp τ → TExp τ → TExp τ
  | is0  : TExp .numty → TExp .boolty

def texp1 : TExp .numty := .ifte .tru (.num 1) (.num 0)

-- def texp2 : TExp .numty := .ifte (.num 1) (.num 1) (.num 0)

-- def texp3 : TExp .numty := .ifte .tru (.num 1) .fls

inductive TVal : Ty → Set where
  | vtru : TVal .boolty
  | vfls : TVal .boolty
  | vnum : ℕ → TVal .numty

def interp2 : TExp τ → TVal τ
  | .tru => .vtru
  | .fls => .vfls
  | .num n => .vnum n
  | .ifte e₁ e₂ e₃ =>
    match interp2 e₁ with
    | .vtru => interp2 e₂
    | .vfls => interp2 e₃
  | .is0 e =>
    match interp2 e with
    | .vnum 0 => .vtru
    | .vnum _ => .vfls

def interpTy : Ty → Set
  | .boolty => Bool
  | .numty  => ℕ

def interp3 : TExp τ → interpTy τ
  | .tru => true
  | .fls => false
  | .num n => n
  | .ifte e₁ e₂ e₃ =>
    match interp3 e₁ with
    | true  => interp3 e₂
    | false => interp3 e₃
  | .is0 e =>
    match interp3 e with
    | .zero => true
    | _ => false
