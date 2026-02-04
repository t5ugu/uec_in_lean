import UecInLean.Category.Basic

namespace UecInLean

universe w v u
structure Enriched (V : Type v) [Category.{w} V] (C : Type u) where
  hom : C → C → V
  id {x : C} : hom x x
  comp {x y z : C} : hom x y ⟶ hom y z ⟶ hom x z
  id_comp {x y : C} (f : hom x y) :
    Category.comp (Category.id (hom x x)) f = f
  comp_id {x y : C} (f : hom x y) :
    Category.comp f (Category.id (hom y y)) = f
  comp_assoc {w x y z : C} (f : hom x y) (g : hom y z) (h : hom z w) :
    Category.comp (Category.comp f g) h = Category.comp f (Category.comp g h)

end UecInLean
