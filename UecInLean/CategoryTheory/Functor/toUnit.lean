import UecInLean.CategoryTheory.Functor.Representable
import UecInLean.CategoryTheory.Category.Discrete

namespace UecInLean.CategoryTheory
namespace Functor

universe w v u

def toUnit (C : Type u) [Category.{v} C] : C ⥤ Category.Discrete.{w} PUnit.{w+2} where
  obj _ := ⟨PUnit.unit⟩
  map _ := 𝟙 _
  map_id _ := rfl
  map_comp _ _ := rfl

instance {C : Type u} [Category.{v} C] : Representable.{v, u} (toUnit.{v} C) where
