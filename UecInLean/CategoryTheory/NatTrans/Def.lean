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

@[simp]
theorem vcomp_id {F G : C ⥤ D} (η : F ⟹ G) : vcomp η (id G) = η := by ext; simp

@[simp]
theorem id_vcomp {F G : C ⥤ D} (η : F ⟹ G) : vcomp (id F) η = η := by ext; simp

@[simp]
theorem vcomp_assoc {F G H K : C ⥤ D} (η : F ⟹ G) (θ : G ⟹ H) (ι : H ⟹ K) : vcomp (vcomp η θ) ι = vcomp η (vcomp θ ι) := by ext; simp

end NatTrans
