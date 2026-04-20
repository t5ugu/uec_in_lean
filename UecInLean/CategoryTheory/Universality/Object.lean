import UecInLean.CategoryTheory.Category.Opposite
import UecInLean.CategoryTheory.Iso.Opposite
import UecInLean.CategoryTheory.Functor.Representable

namespace UecInLean.CategoryTheory

universe u v w
variable {C : Type u} [Category.{v} C]

def Functor.Initial : C ⥤ Type (max v w) where
  obj _ := PUnit
  map _ _ := PUnit.unit
  map_id _ := rfl
  map_comp _ _ := rfl

theorem Functor.Initial.map_def (x y : C) (f : x ⟶ y) : (Functor.Initial.map f : PUnit → PUnit) = λ _ => PUnit.unit := rfl

def IsInitial (u : C) := Functor.Initial.IsRepresentedBy u

def IsInitial.default {i : C} (θ : IsInitial i) (x : C) : i ⟶ x
  := (θ.obj x).hom .unit |>.down

theorem IsInitial.allEq {i : C} (θ : IsInitial i) {x : C} (f g : i ⟶ x) : f = g := by {
  unfold IsInitial Functor.IsRepresentedBy at θ
  have hf := congrFun (θ.symm.naturality f) ⟨𝟙 i⟩
  have hg := congrFun (θ.symm.naturality g) ⟨𝟙 i⟩
  simp only [Category.Set.comp_app, Functor.Hom.map_def,
    Category.id_comp, Functor.Initial.map_def, Iso.symm_hom, Iso.inv_app] at hf hg
  rw [← hg] at hf
  have := congrArg (θ.obj x).hom hf
  rw [← Category.Set.comp_app (θ.obj x).inv (θ.obj x).hom, Iso.inv_hom_id, Category.Set.id_app, ← Category.Set.comp_app (θ.obj x).inv (θ.obj x).hom, Iso.inv_hom_id, Category.Set.id_app] at this
  exact congrArg ULift.down this
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


universe u' v'
variable {D : Type u'} [Category.{v'} D]

def Functor.UniversalArrow (G : D ⥤ C) (c : C) : D ⥤ Type (max v v') := {
  obj d := ULift (c ⟶ G.obj d)
  map f h := ⟨h.down ≫ (G.map f)⟩
  map_id _ := by funext _; simp
  map_comp := by simp
}

@[simp]
theorem Functor.UniversalArrow.obj_def {G : D ⥤ C} {c : C} (d : D) : (Functor.UniversalArrow G c).obj d = ULift (c ⟶ G.obj d) := rfl

@[simp]
theorem Functor.UniversalArrow.map_def {G : D ⥤ C} {c : C} {d₁ d₂ : D} (f : d₁ ⟶ d₂) (h : ULift (c ⟶ G.obj d₁)) : (Functor.UniversalArrow G c).map f h = ⟨h.down ≫ (G.map f)⟩ := rfl

class HasUniversalArrow (G : D ⥤ C) (c : C) extends (G.UniversalArrow c).Representable

def HasUniversalArrow.limit {G : D ⥤ C} {c : C} (h : HasUniversalArrow G c) : D := h.repr

def HasUniversalArrow.arrow {G : D ⥤ C} {c : C} (h : HasUniversalArrow G c) : c ⟶ G.obj h.limit
  := (h.is_repr.obj h.repr).inv ⟨𝟙 _⟩ |>.down

def HasUniversalArrow.hom {G : D ⥤ C} {c : C} (h : HasUniversalArrow G c) (d : D) (f : c ⟶ G.obj d) : h.limit ⟶ d := (h.is_repr.obj d).hom ⟨f⟩ |>.down

theorem HasUniversalArrow.universality {G : D ⥤ C} {c : C} (h : HasUniversalArrow G c) (d : D) (f : c ⟶ G.obj d) : f = h.arrow ≫ G.map (h.hom d f) := by {
  have h₁
    : (h.is_repr.symm.obj d).hom ⟨h.hom d f⟩ = ⟨((h.is_repr.symm.obj h.limit).hom ⟨𝟙 h.limit⟩).down ≫ G.map (h.hom d f)⟩
    := by simpa using congrFun (h.is_repr.symm.naturality (h.hom d f)) ⟨𝟙 _⟩
  have hcancel := congrFun (h.is_repr.obj d).hom_inv_id ⟨f⟩
  exact congrArg ULift.down <| hcancel.symm.trans h₁
}

theorem HasUniversalArrow.unique {G : D ⥤ C} {c : C} (h : HasUniversalArrow G c) (d : D) (f : c ⟶ G.obj d) (g : h.limit ⟶ d) (w : f = h.arrow ≫ G.map g) : g = h.hom d f := by {
  apply congrArg ULift.down
  have h₁ := congrFun (h.is_repr.symm.naturality g) ⟨𝟙 _⟩
  have hfg : (h.is_repr.obj d).inv ⟨g⟩ = ⟨f⟩ := by simpa [w] using h₁
  rw [← congrArg (h.is_repr.obj d).hom hfg]
  have hcancelg := congrFun (h.is_repr.obj d).inv_hom_id ⟨g⟩
  simpa using hcancelg.symm
}

end UecInLean.CategoryTheory
