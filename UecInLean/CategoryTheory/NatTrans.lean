import UecInLean.CategoryTheory.Category.Def
import UecInLean.CategoryTheory.Functor.Def

namespace UecInLean.CategoryTheory

universe v v' v'' v₀ v₁ u u' u'' u₀ u₁

structure NatTrans {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  (F G : C ⥤ D) where
  app (x : C) : F.obj x ⟶ G.obj x
  naturality {x y : C} (f : x ⟶ y) :
    F.map f ≫ app y = app x ≫ G.map f := by grind

infixr:80 " ⟹ " => NatTrans

attribute [simp, grind =] NatTrans.naturality

namespace NatTrans

def id {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  (F : C ⥤ D) : F ⟹ F where
    app x := 𝟙 (F.obj x)
    naturality f := by rw [Category.comp_id, Category.id_comp]

@[simp, grind =]
theorem id_app {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  (F : C ⥤ D) (x : C)
: (NatTrans.id F).app x = 𝟙 (F.obj x) := rfl

def vcomp {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  {F G H : C ⥤ D} (η : F ⟹ G) (θ : G ⟹ H)
: F ⟹ H where
  app x := η.app x ≫ θ.app x
  naturality f := by rw [← Category.comp_assoc, η.naturality f, Category.comp_assoc, θ.naturality f, ← Category.comp_assoc]

@[simp, grind =]
theorem vcomp_app {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  {F G H : C ⥤ D} (η : F ⟹ G) (θ : G ⟹ H) (x : C)
: (vcomp η θ).app x = η.app x ≫ θ.app x := rfl

def whiskering {A : Type u₀} {C : Type u} {D : Type u'} {B : Type u₁} [Category.{v₀} A] [Category.{v} C] [Category.{v'} D] [Category.{v₁} B]
  (F : A ⥤ B) {G H : B ⥤ C} (η : G ⟹ H) (I : C ⥤ D) : (F ⋙ G ⋙ I) ⟹ (F ⋙ H ⋙ I) := {
    app a := I.map (η.app (F.obj a))
    naturality f := by {
      simp only [Functor.comp_map, ← I.map_comp]
      apply I.map_congrArg
      exact η.naturality (F.map f)
    }
  }

def whiskerLeft {A : Type u₀} {C : Type u} {B : Type u₁} [Category.{v₀} A] [Category.{v} C] [Category.{v₁} B]
  {F G : A ⥤ B} (η : F ⟹ G) (H : B ⥤ C) : (F ⋙ H) ⟹ (G ⋙ H) := {
    app a := H.map (η.app a)
    naturality f := by {
      simp only [Functor.comp_map, ← H.map_comp]
      apply H.map_congrArg
      exact η.naturality f
    }
  }

def whiskerRight {A : Type u₀} {C : Type u} {B : Type u₁} [Category.{v₀} A] [Category.{v} C] [Category.{v₁} B]
  (F : A ⥤ B) {G H : B ⥤ C} (η : G ⟹ H) : (F ⋙ G) ⟹ (F ⋙ H) := {
    app a := η.app (F.obj a)
    naturality f := η.naturality (F.map f)
  }

def hcomp {A : Type u} {B : Type u'} {C : Type u''}
  [Category.{v} A] [Category.{v'} B] [Category.{v''} C]
  {F₁ F₂ : A ⥤ B} (η : F₁ ⟹ F₂)
  {G₁ G₂ : B ⥤ C} (θ : G₁ ⟹ G₂)
: (F₁ ⋙ G₁) ⟹ (F₂ ⋙ G₂) := {
  app a := θ.app (F₁.obj a) ≫ G₂.map (η.app a)
  naturality f := by {
    rw [Functor.comp_map, ← θ.naturality, ← Category.comp_assoc, ← G₁.map_comp, θ.naturality]
    simp
  }
}

theorem hcomp_app {A : Type u} {B : Type u'} {C : Type u''}
  [Category.{v} A] [Category.{v'} B] [Category.{v''} C]
  {F₁ F₂ : A ⥤ B} (η : F₁ ⟹ F₂)
  {G₁ G₂ : B ⥤ C} (θ : G₁ ⟹ G₂)
  (a : A)
: (hcomp η θ).app a = θ.app (F₁.obj a) ≫ G₂.map (η.app a) := rfl

@[ext 9000, grind ext]
theorem ext {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  {F G : C ⥤ D} {η θ : F ⟹ G} (h : ∀ x : C, η.app x = θ.app x)
: η = θ := by {
  cases η; cases θ;
  congr
  exact funext h
}
