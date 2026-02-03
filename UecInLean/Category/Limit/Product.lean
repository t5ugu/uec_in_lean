import UecInLean.Category.Basic
import UecInLean.Category.Iso

open UecInLean

universe v u
variable {C : Type u} [Category.{v} C]

class IsProduct (a b x : C)

example (a b x y : C) [IsProduct a b x] [IsProduct a b y] : x ≅ y := by sorry
