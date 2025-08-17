namespace UecInLean.TaPL

namespace ArithML

structure info where
  src : String
  idxAt : Nat
deriving Inhabited

def dummyinfo : info := default

inductive term
  | TmTrue : info -> term
  | TmFalse : info -> term
  | TmIf : info -> term -> term -> term -> term
  | TmZero : info -> term
  | TmSucc : info -> term -> term
  | TmPred : info -> term -> term
  | TmIsZero : info -> term -> term

def isnumericval : term -> Bool
  | .TmZero _ => true
  | .TmSucc _ t => isnumericval t
  | _ => false

def isval : term -> Bool
  | .TmTrue _ => true
  | .TmFalse _ => true
  | t => isnumericval t

/-- 例外処理での実装は TaPL を参照のこと -/
def eval1 : term -> Option term
  | .TmIf _ (.TmTrue _) t2 _ => some t2
  | .TmIf _ (.TmFalse _) _ t3 => some t3
  | .TmIf fi t1 t2 t3 => do
      let t1' <- eval1 t1
      some (.TmIf fi t1' t2 t3)
  | .TmSucc fi t1 => do
      let t1' <- eval1 t1
      some (.TmSucc fi t1')
  | .TmPred _ (.TmZero _) => some (.TmZero dummyinfo)
  | .TmPred _ (.TmSucc _ nvl) =>
      if isnumericval nvl
      then some nvl
      else none
  | .TmPred fi t1 => do
      let t1' <- eval1 t1
      some (.TmPred fi t1')
  | .TmIsZero _ (.TmZero _) => some (.TmTrue dummyinfo)
  | .TmIsZero _ (.TmSucc _ nvl) =>
      if isnumericval nvl
      then some (.TmFalse dummyinfo)
      else none
  | .TmIsZero fi t1 => do
      let t1' <- eval1 t1
      some (.TmIsZero fi t1')
  | _ => none

partial def eval (t : term) : term :=
  match eval1 t with
  | some t' => eval t'
  | none => t

/-- 演習 4.2.2 -/
def bigeval : term -> term
  | t@(.TmIf _ t1 t2 t3) =>
      let t1' := bigeval t1
      match t1' with
      | .TmTrue _ => bigeval t2
      | .TmFalse _ => bigeval t3
      | _ => t
  | t@(.TmSucc _ t1) =>
      let t1' := bigeval t1
      if isnumericval t1'
      then (.TmSucc dummyinfo t1')
      else t
  | t@(.TmPred _ t1) =>
      let t1' := bigeval t1
      match t1' with
      | .TmZero _ => (.TmZero dummyinfo)
      | .TmSucc _ nv1 => if isnumericval nv1 then nv1 else t
      | _ => t
  | t@(.TmIsZero _ t1) =>
      let t1' := bigeval t1
      match t1' with
      | .TmZero _ => (.TmTrue dummyinfo)
      | .TmSucc _ nv1 => if isnumericval nv1 then (.TmFalse dummyinfo) else t
      | _ => t
  | v => v

def toString : term -> String
  | .TmTrue _ => "true"
  | .TmFalse _ => "false"
  | .TmIf _ t1 t2 t3 => s!"(if {toString t1} then {toString t2} else {toString t3})"
  | .TmZero _ => "0"
  | .TmSucc _ t1 => s!"(succ {toString t1})"
  | .TmPred _ t1 => s!"(pred {toString t1})"
  | .TmIsZero _ t1 => s!"(iszero {toString t1})"

instance : ToString term := ⟨toString⟩

#eval eval (.TmIsZero dummyinfo (.TmPred dummyinfo (.TmIsZero dummyinfo (.TmZero dummyinfo)))) -- iszero (pred true)
#eval bigeval (.TmIsZero dummyinfo (.TmPred dummyinfo (.TmIsZero dummyinfo (.TmZero dummyinfo)))) -- iszero (pred (iszero 0))
