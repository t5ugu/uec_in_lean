import UecInLean.CategoryTheory.Iso.NaturalIso
import UecInLean.CategoryTheory.Iso.Hom

namespace UecInLean.CategoryTheory
universe v u
variable {C : Type u} [Category.{v} C]

namespace Functor

def IsRepresentedBy (F : C ⥤ Type v) (a : C) := F ≅ Hom a

class Representable (F : C ⥤ Type v) where
  repr : C
  is_repr : F.IsRepresentedBy repr

end Functor

def Iso.of_IsRepresentedBy {F : C ⥤ Type v} {a b : C} (ha : F.IsRepresentedBy a) (hb : F.IsRepresentedBy b) : a ≅ b := Iso.Hom_inj (ha.symm.trans hb)

end UecInLean.CategoryTheory
