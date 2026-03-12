import UecInLean.CategoryTheory.Category.Opposite
import UecInLean.CategoryTheory.Iso.Opposite
import UecInLean.CategoryTheory.Functor.Representable

namespace UecInLean.CategoryTheory

universe u v
variable {C : Type u} [Category.{v} C]

def Functor.Initial : C ⥤ Type v where
  obj _ := PUnit
  map _ _ := PUnit.unit
  map_id _ := rfl
  map_comp _ _ := rfl

theorem Functor.Initial.map_def (x y : C) (f : x ⟶ y) : (Functor.Initial.map f : PUnit → PUnit) = λ _ => PUnit.unit := rfl

def IsInitial (u : C) := Functor.Initial.IsRepresentedBy u

def IsInitial.default {i : C} (θ : IsInitial i) (x : C) : i ⟶ x
  := (θ.obj x).hom .unit

theorem IsInitial.allEq {i : C} (θ : IsInitial i) {x : C} (f g : i ⟶ x) : f = g := by {
  unfold IsInitial Functor.IsRepresentedBy at θ
  have hf := congrFun (θ.symm.naturality f) (𝟙 i)
  have hg := congrFun (θ.symm.naturality g) (𝟙 i)
  simp only [Category.Set.comp_app, Functor.Hom.map_def,
    Category.id_comp, Functor.Initial.map_def, Iso.symm_hom, Iso.inv_app] at hf hg
  rw [← hg] at hf
  have := congrArg (θ.obj x).hom hf
  rw [← Category.Set.comp_app (θ.obj x).inv (θ.obj x).hom, Iso.inv_hom_id, Category.Set.id_app, ← Category.Set.comp_app (θ.obj x).inv (θ.obj x).hom, Iso.inv_hom_id, Category.Set.id_app] at this
  exact this
}

def IsInitial.iso {i₁ i₂ : C} (h₁ : IsInitial i₁) (h₂ : IsInitial i₂) : i₁ ≅ i₂ := {
  hom := h₁.default i₂
  inv := h₂.default i₁
  hom_inv_id := h₁.allEq _ _
  inv_hom_id := h₂.allEq _ _
}

def IsTerminal (t : C) := IsInitial (⟨t⟩ : Cᵒᵖ)
def IsTerminal.default {t : C} (θ : IsTerminal t) (x : C) : x ⟶ t
  := IsInitial.default θ ⟨x⟩
def IsTerminal.iso {t₁ t₂ : C} (h₁ : IsTerminal t₁) (h₂ : IsTerminal t₂) : t₁ ≅ t₂ := (IsInitial.iso h₁ h₂).unop


universe u'
variable {D : Type u'} [Category.{v} D]

def Functor.UniversalArrow (G : D ⥤ C) (c : C) : D ⥤ Type v := {
  obj d := c ⟶ G.obj d
  map f h := h ≫ (G.map f)
  map_id := by simp
  map_comp := by simp
}

class HasUniversalArrow (c : C) (G : D ⥤ C) extends (Functor.UniversalArrow G c).Representable

end UecInLean.CategoryTheory
