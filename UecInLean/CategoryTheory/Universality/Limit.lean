import UecInLean.CategoryTheory.Category.Discrete

namespace UecInLean.CategoryTheory.Limit

universe v v' u u'
variable {C : Type u} [Category.{v} C] {J : Type u'} [Category.{v'} J]

structure Cone (F : J ⥤ C) where
  pt : C
  π : ∀ j : J, pt ⟶ F.obj j
  comm : ∀ {j j' : J} (f : j ⟶ j'), π j ≫ F.map f = π j'

def IsLimit {F : J ⥤ C} (l : Cone F) := ∀ (d : Cone F), Σ' h : l.pt ⟶ d.pt, ∀ h' : l.pt ⟶ d.pt, h' = h

class HasLimit (F : J ⥤ C) where
  lim : Cone F
  isLim : IsLimit lim
