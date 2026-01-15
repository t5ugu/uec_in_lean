import UecInLean.Category.Basic
import UecInLean.Category.Prod
import Mathlib.Tactic.TypeStar

namespace UecInLean

open prod.Functor prod.Functor

universe v u

class StrictMonoidal (V : Type u) [Category.{v} V] where
  tensor : (V × V) ⥤ V
  I : V
  α : NatTrans
    (prod.associator_inv ⋙ prod tensor (Functor.id V) ⋙ tensor)
    (prod (Functor.id V) tensor ⋙ tensor)

end UecInLean
