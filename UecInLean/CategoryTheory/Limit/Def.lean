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

namespace Product

inductive Span : Type u
  | l | r
inductive Span_hom : Span → Span → Type v
  | id (o : Span) : Span_hom o o
instance : Category Span where
  hom := Span_hom
  id := Span_hom.id
  comp f g := by cases f; exact g
  comp_id
    | .id _ => by rfl
  id_comp
    | .id _ => by rfl
  comp_assoc f g h := by {
    cases f <;> cases g <;> cases h <;> rfl
  }

def ProductFunctor (a b : C) : Discrete (Fin 2) ⥤ C where
  obj
    | ⟨0⟩ => a
    | ⟨1⟩ => b
  map := by intro _ _ ⟨⟨f⟩⟩; subst f; exact 𝟙 _
  map_id x := by rfl
  map_comp := by {
    intro _ _ _ ⟨⟨f⟩⟩ ⟨⟨g⟩⟩; subst f; subst g; rw [Category.comp_id]
  }

def ProductCone {a b : C} (p : C) (π1 : p ⟶ a) (π2 : p ⟶ b) : Cone (ProductFunctor a b) where
  pt := p
  π
    | ⟨0⟩ => π1
    | ⟨1⟩ => π2
  comm := by {
    intro ⟨j⟩ _ ⟨⟨f⟩⟩; subst f;
    rw [Discrete.id_def, Functor.map_id, Category.comp_id]
  }

class HasProduct (a b : C) extends HasLimit (ProductFunctor a b)

