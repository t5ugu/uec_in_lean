import UecInLean.CategoryTheory.Category.Set
import UecInLean.CategoryTheory.Category.Opposite
import UecInLean.CategoryTheory.Iso.Def

namespace UecInLean.CategoryTheory
universe u v u' v'
variable {C : Type u} [Category.{v} C]

class Functor.Represent (F : Cᵒᵖ ⥤ Type v) where
  obj : C
  repr (d : C) : (d ⟶ obj) ≅ (F.obj ⟨d⟩)
