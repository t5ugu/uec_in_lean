namespace UecInLean.TaPL

inductive UntypedLambda
  | var : String -> UntypedLambda
  | abs : String -> UntypedLambda -> UntypedLambda
  | app : UntypedLambda -> UntypedLambda -> UntypedLambda

namespace UntypedLambda

instance : Coe String UntypedLambda := ⟨.var⟩

notation:100 "λ " x:100 ":. " b:100 => UntypedLambda.abs x b

-- `L x. x` のようにピリオドを打つのは技術的制約がある。理由は調べてない
macro "λ " xs:term,* ":. " b:term : term => do
  xs.getElems.foldrM (fun x acc => `(UntypedLambda.abs $x $acc)) b

#check λ "x", "y" :. "x"
