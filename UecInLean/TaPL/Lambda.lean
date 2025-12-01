
namespace UecInLean.TaPL

-- 型システム入門 プログラミング言語と型の理論 ISBN 978-4-274-06911-6

inductive Lambda
  | var (n : Nat)
  | abs (t : Lambda)
  | app (t₁ t₂ : Lambda)
/-- いちばん左の束縛変数を `Lambda` にすれば、`Lambda.app` 連鎖が見やすい -/
prefix:max "$" => Lambda.var
notation:200 "L." t:100 => Lambda.abs t
infixl:200 " ⬝ " => Lambda.app

instance (n : Nat) : OfNat Lambda n where
  ofNat := $ n

instance : CoeFun Lambda (fun _ => Lambda → Lambda) where
  coe := Lambda.app

def toString (t : Lambda) : String := (recu t).1
where
  recu : Lambda -> String × Nat
  | .var n => (s!"{n}", 0)
  | L. t =>
    let (s, i) := recu t
    (s!"(λ{i}. {s})", i + 1)
  | .var n ⬝ t =>
    let (s, i) := recu t
    (s!"{n} {s}", i)
  | t ⬝ .var n =>
    let (s, i) := recu t
    (s!"{s} {n}", i)
  | t₁ ⬝ t₂ =>
    let (s₁, i₁) := recu t₁
    let (s₂, i₂) := recu t₂
    (s!"({s₁} {s₂})", max i₁ i₂)

instance : ToString Lambda where
  toString := toString

/-- de Bruijn インデックス。Lambda が n項(内からn個目の`L.`に包まれている)であること -/
inductive deBruijn : Nat -> Lambda -> Prop
  | var {i n} : i < n -> deBruijn n ($ i)
  | abs {n t₁} : deBruijn (n + 1) t₁ -> deBruijn n (L. t₁)
  | app {n t₁ t₂} : deBruijn n t₁ -> deBruijn n t₂ -> deBruijn n (t₁ ⬝ t₂)

theorem deBruijn_var_iff {i n} : deBruijn n ($ i) ↔ i < n := by {
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

theorem deBurijn_app_left {n t₁ t₂} : deBruijn n (t₁ ⬝ t₂) → deBruijn n t₁ := by {
  intro h
  rcases h with ⟨⟩ | ⟨⟩ | ⟨h₁, _⟩
  exact h₁
}

theorem deBurijn_app_right {n t₁ t₂} : deBruijn n (t₁ ⬝ t₂) → deBruijn n t₂ := by {
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
def shift (c d : Nat) : Lambda -> Lambda
  | $ k => if k < c then $ k else $ (k + d)
  | L. t₁ => L. (shift (c + 1) d t₁)
  | t₁ ⬝ t₂ => shift c d t₁ ⬝ shift c d t₂

#eval shift 0 2 (L. L. 1 ⬝ (0 ⬝ 2))
#eval shift 0 2 (L. 0 ⬝ 1 ⬝ (L. 0 ⬝ 1 ⬝ 2))

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

def subst (j : Nat) (s : Lambda) : Lambda -> Lambda
  | $ k => if k = j then s else $ k
  | L. t₁ => L. (subst (j + 1) (shift 0 1 s) t₁)
  | t₁ ⬝ t₂ => subst j s t₁ ⬝ subst j s t₂
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
def downshift (c : Nat) : Lambda -> Lambda
  | $ k => if k < c then $ k else $ (k - 1)
  | L. t₁ => L. (downshift (c + 1) t₁)
  | t₁ ⬝ t₂ => downshift c t₁ ⬝ downshift c t₂

abbrev substitute (c : Nat) (s t : Lambda) : Lambda := downshift c (subst c (shift c 1 s) t)

/-- TaPL, 正規順序戦略, leftmost outermost -/
def stepNormalOrder : Lambda -> Option Lambda := recu 0
where
  recu (depth : Nat) : Lambda -> Option Lambda
  | (L. t₁) ⬝ t₂ => substitute depth t₂ t₁
  | L. t => (L. ·) <$> recu (depth + 1) t
  | t₁ ⬝ t₂ => (· ⬝ t₂) <$> recu depth t₁
  | _ => none

/-- TaPL, 名前呼び戦略, leftmost outermost w/o reduce inside abs -/
def stepCallByName : Lambda -> Option Lambda
  | (L. t₁) ⬝ t₂ => substitute 0 t₂ t₁
  | t₁ ⬝ t₂ => (· ⬝ t₂) <$> stepCallByName t₁
  | _ => none

/-- TaPL, 値呼び戦略, leftmost innermost w/o reduce inside abs -/
def stepCallByValue : Lambda -> Option Lambda
  | (L. t₁) ⬝ (L. t₂) => substitute 0 (L. t₂) t₁
  | (L. t₁) ⬝ t₂ => ((L. t₁) ⬝ ·) <$> stepCallByValue t₂
  | t₁ ⬝ t₂ => (· ⬝ t₂) <$> stepCallByValue t₁
  | _ => none

/-- Pratik Thanki. https://pratikthanki.github.io/posts/lambda-calculus-beta-reduction/, leftmost innermost -/
def stepApplicative : Lambda -> Option Lambda := recu 0
where
  recu (depth : Nat) : Lambda -> Option Lambda
  | (L. m) ⬝ n =>
    (· ⬝ n) <$> (L. ·) <$> recu depth m
    <|> ((L. m) ⬝ ·) <$> recu depth n
    <|> substitute depth n m
  | m ⬝ n =>
    (· ⬝ n) <$> recu depth m
    <|> (m ⬝ ·) <$> recu depth n
  | L. m =>
    (L. ·) <$> recu (depth + 1) m
  | .var _ => none

def beta (restStep: Nat) (step : Lambda -> Option Lambda) (t : Lambda) : Lambda :=
  match restStep, step t with
  | restStep + 1, some t' => beta restStep step t'
  | _, _ => t

def exa : Lambda := (L. 0) ⬝ ((L. 0) ⬝ (L. (L. 0) ⬝ 1))
#eval exa -- "id" (id (λ1. id 1))
  >>= stepNormalOrder -- "id" (λ1. id 1)
  >>= stepNormalOrder -- λ1. "id" 1
  >>= stepNormalOrder -- λ0. 0
  >>= stepNormalOrder -- none
#eval exa -- "id" (id (λ1. id 1))
  >>= stepCallByName -- "id" (λ1. id 1)
  >>= stepCallByName -- λ1. id 1
  >>= stepCallByName -- none
#eval exa -- id ("id" (λ1. id 1))
  >>= stepCallByValue -- "id" (λ1. id 1)
  >>= stepCallByValue -- λ1. id 1
  >>= stepCallByValue -- none
#eval exa -- id (id (λ1. "id" 1))
  >>= stepApplicative -- id ("id" (λ0. 0))
  >>= stepApplicative -- "id" (λ0. 0)
  >>= stepApplicative -- λ0. 0
  >>= stepApplicative -- none

def tru := L. L. 1
def fls := L. L. 0
def test := L. L. L. 2 ⬝ 1 ⬝ 0
#eval beta 100 stepNormalOrder (test tru 100 200) -- 100

def and := L. L. $1 0 fls
#eval beta 100 stepNormalOrder (and tru tru) -- tru
#eval beta 100 stepNormalOrder (and tru fls) -- fls

/-- 演習5.2.1 -/
def or := L. L. $1 tru 0
#eval beta 100 stepNormalOrder (or tru tru) -- tru
#eval beta 100 stepNormalOrder (or tru fls) -- tru

/-- 演習5.2.1 -/
def not := L. $0 fls tru
#eval beta 100 stepNormalOrder (not tru) -- fls

def pair := L. L. L. 0 ⬝ 2 ⬝ 1
def fst := L. 0 ⬝ tru -- tru に 2つラムダ抽象があるので、0でなく2なのでは...? そうするとバグるけど。
def snd := L. 0 ⬝ fls

#eval beta 100 stepNormalOrder (fst (pair 100 200)) -- 100

def zro : Lambda := L. L. 0
def one : Lambda := L. L. 1 ⬝ 0
def two : Lambda := L. L. 1 ⬝ (1 ⬝ 0)
def thr : Lambda := L. L. 1 ⬝ (1 ⬝ (1 ⬝ 0))
def four: Lambda := L. L. 1 ⬝ (1 ⬝ (1 ⬝ (1 ⬝ 0)))
def five: Lambda := L. L. 1 ⬝ (1 ⬝ (1 ⬝ (1 ⬝ (1 ⬝ 0))))
def six : Lambda := L. L. 1 ⬝ (1 ⬝ (1 ⬝ (1 ⬝ (1 ⬝ (1 ⬝ 0)))))
#eval beta 100 stepNormalOrder ((two) fst (pair (pair 100 200) 300)) -- 100

def scc : Lambda := L. L. L. 1 ⬝ (2 ⬝ 1 ⬝ 0)
#eval beta 100 stepNormalOrder ((scc one) fst (pair (pair 100 200) 300)) -- 100

/-- 演習5.2.2 -/
def scc2 : Lambda := L. L. L. 2 ⬝ 1 ⬝ (1 ⬝ 0)
#eval beta 100 stepNormalOrder ((scc2 one) fst (pair (pair 100 200) 300)) -- 100

def plus : Lambda := L. L. L. L. 3 ⬝ 1 ⬝ (2 ⬝ 1 ⬝ 0) -- λm n s z. m s (n s z)
#eval beta 100 stepNormalOrder ((plus one two) fst (pair (pair (pair 100 200) 300) 400)) -- 100

def times : Lambda := L. L. $1 (plus 0) zro -- λm n. m (plus n) z
#eval beta 100 stepNormalOrder ((times one two) fst (pair (pair 100 200) 300)) -- 100

/-- 演習5.2.3
  λm n s. m (n s)
  (λz. (λw. s ..n.. s w) ..m.. (λw. s ..n.. s w) z)
 -/
def times3 : Lambda := L. L. L. 2 ⬝ (1 ⬝ 0)
#eval beta 100 stepNormalOrder ((times3 one two) fst (pair (pair 100 200) 300)) -- 100

/-- 演習5.2.4
  m^n = (m回やる) を n回やる
 -/
def pow : Lambda := L. L. 0 ⬝ 1

def iszro : Lambda := L. $0 (L. fls) tru
#eval beta 100 stepNormalOrder (iszro zro) -- tru
#eval beta 100 stepNormalOrder (iszro two) -- fls

def prd : Lambda := L. fst ($0 ss zz)
where
  zz := pair zro zro
  ss := L. pair (snd 0) (plus one (snd 0))
#eval beta 100 stepNormalOrder (prd zro) -- prd(zro) = zro

/-- 演習5.2.5
  λ m n.
  (n prd m)
-/
def sub : Lambda := L. L. $0 prd 1

/-- 演習5.2.7
  λ m n.
  iszro sub m n
-/
def equal : Lambda := L. L. and (iszro (sub 0 1)) (iszro (sub 1 0))
#eval beta 1000 stepNormalOrder (equal thr thr) -- tru
#eval beta 1000 stepNormalOrder (equal thr two) -- fls

/-- 演習5.2.8
  nil: λc n. n
-/
def nil : Lambda := L. L. 0
/-- 演習5.2.8
  cons: λh t. (λc n. c h (t c n))
-/
def cons : Lambda := L. L. L. L. $1 3 ($2 1 0)
/-- 演習5.2.8
  isnil: λl. l (λc n. fls) tru
  l = nil → n そのまま
  l ≠ nil → c a₀ (c a₁ ...(c aₙ n))
-/
def isnil : Lambda := L. $0 (L. L. fls) tru
/-- 演習5.2.8
  head: λl. l (λh a. h) nil
  なんもわからんので head nil = zro とした。
-/
def head : Lambda := L. $0 (L. L. 1) zro
/-- 演習5.2.8
  tail: λl. fst (l (λe p, pair (snd p) (cons e (snd p))) (pair nil nil))
                       ↑ この p は ⟨tail, all⟩
-/
def tail : Lambda := L. fst ($0 (L. L. pair (snd 0) (cons 1 (snd 0))) (pair nil nil))

#eval beta 1000 stepNormalOrder (equal four (times two two))

def omega : Lambda := (L. $0 0) (L. $0 0)

def fixY := L. (L. $1 ($0 0)) (L. $1 ($0 0))
def fixZ := L. (L. $1 (L. $1 1 0)) (L. $1 (L. $1 1 0))


def factorial := fixZ g
where
  /--
    g = λ fct. λ n. test (equal n zro) one (times n (fct (prd n)))
  -/
  g := L. L. test (iszro 0) one (times 0 ($1 (prd 0)))

-- #eval beta 100000 stepNormalOrder (equal (factorial thr) six) -- true
