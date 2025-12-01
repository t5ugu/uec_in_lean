universe u v
structure Equiv (A B : Type u) where
  toFun    : A → B
  invFun   : B → A
  leftInv  : ∀ x : A, invFun (toFun x) = x
  rightInv : ∀ y : B, toFun (invFun y) = y

def Equiv.symm {A B : Type u} (e : Equiv A B) : Equiv B A :=
  ⟨e.invFun, e.toFun, e.rightInv, e.leftInv⟩

class Magma (A : Type u) where
  op : A → A → A

variable {A B : Type u} [mA : Magma A]

class Transport (P : Type u → Type v) where
  map : ∀ {X Y : Type u}, Equiv X Y → P X → P Y

def transport (e : Equiv A B) (P : Type u → Type v) [T : Transport P] : P A → P B := T.map e

instance : Transport (fun X => X) where
  map e x := e.toFun x

instance {α : Type v} : Transport (fun X => X → α) where
  map e f := fun b => f (e.invFun b)

instance : Transport (fun X => X → X → X) where
  map e f := fun b1 b2 => transport e (fun X => X) (f (e.invFun b1) (e.invFun b2))

instance : Transport (fun X => Magma X) where
  map e m := { op := transport e (fun X => X → X → X) m.op }

#check Exists.choose
example (e : Equiv A B) : Magma B := {
  op x y := transport e (fun X => X) (mA.op (transport e.symm (fun X => X) x) (transport e.symm (fun X => X) y))
}

example (e : Equiv A B) : Magma B := {
  op x y := e.toFun (mA.op (e.invFun x) (e.invFun y))
}

example (e : Equiv A B) : Magma B := {
  op := transport e (λ X => X → X → X) mA.op
}

example (e : Equiv A B) : Magma B := transport e (λ X => Magma X) mA
