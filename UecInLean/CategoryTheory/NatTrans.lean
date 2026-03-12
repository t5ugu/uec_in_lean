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

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E] {A : Type u₀} [Category.{v₀} A] {B : Type u₁} [Category.{v₁} B]

def id (F : C ⥤ D) : F ⟹ F where
    app x := 𝟙 (F.obj x)
    naturality f := by rw [Category.comp_id, Category.id_comp]

@[simp]
theorem id_app (F : C ⥤ D) (x : C)
: (NatTrans.id F).app x = 𝟙 (F.obj x) := rfl

def vcomp {F G H : C ⥤ D} (η : F ⟹ G) (θ : G ⟹ H)
: F ⟹ H where
  app x := η.app x ≫ θ.app x
  naturality f := by rw [← Category.comp_assoc, η.naturality f, Category.comp_assoc, θ.naturality f, ← Category.comp_assoc]

@[simp]
theorem vcomp_app {F G H : C ⥤ D} (η : F ⟹ G) (θ : G ⟹ H) (x : C)
: (vcomp η θ).app x = η.app x ≫ θ.app x := rfl

def whiskering (F : A ⥤ B) {G H : B ⥤ C} (η : G ⟹ H) (I : C ⥤ D) : (F ⋙ G ⋙ I) ⟹ (F ⋙ H ⋙ I) := {
    app a := I.map (η.app (F.obj a))
    naturality f := by {
      simp only [Functor.comp_map, ← I.map_comp]
      exact I.congrArg_map <| η.naturality (F.map f)
    }
  }

@[simp]
theorem whiskering_app (F : A ⥤ B) {G H : B ⥤ C} (η : G ⟹ H) (I : C ⥤ D) (a : A) : (whiskering F η I).app a = I.map (η.app (F.obj a)) := rfl

def whiskerLeft {F G : A ⥤ B} (η : F ⟹ G) (H : B ⥤ C) : (F ⋙ H) ⟹ (G ⋙ H) := {
    app a := H.map (η.app a)
    naturality f := by {
      simp only [Functor.comp_map, ← H.map_comp]
      exact H.congrArg_map <| η.naturality f
    }
  }

@[simp]
theorem whiskerLeft_app {F G : A ⥤ B} (η : F ⟹ G) (H : B ⥤ C) (a : A)
: (whiskerLeft η H).app a = H.map (η.app a) := rfl

def whiskerRight (F : A ⥤ B) {G H : B ⥤ C} (η : G ⟹ H) : (F ⋙ G) ⟹ (F ⋙ H) := {
    app a := η.app (F.obj a)
    naturality f := η.naturality (F.map f)
  }

@[simp]
theorem whiskerRight_app (F : A ⥤ B) {G H : B ⥤ C} (η : G ⟹ H) (a : A)
: (whiskerRight F η).app a = η.app (F.obj a) := rfl

def hcomp {F₁ F₂ : A ⥤ B} (η : F₁ ⟹ F₂) {G₁ G₂ : B ⥤ C} (θ : G₁ ⟹ G₂)
: (F₁ ⋙ G₁) ⟹ (F₂ ⋙ G₂) := {
  app a := θ.app (F₁.obj a) ≫ G₂.map (η.app a)
  naturality f := by {
    rw [Functor.comp_map, ← θ.naturality, ← Category.comp_assoc, ← G₁.map_comp, θ.naturality]
    simp
  }
}

@[simp]
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

theorem whiskerLeft_eq_whiskering {F G : A ⥤ B} (η : F ⟹ G) (H : B ⥤ C) : whiskerLeft η H = whiskering (.id A) η H := by ext <;> simp

theorem whiskerRight_eq_whiskering {G H : B ⥤ C} (η : G ⟹ H) (F : A ⥤ B) : whiskerRight F η = whiskering F η (.id C) := by ext <;> simp

end NatTrans
