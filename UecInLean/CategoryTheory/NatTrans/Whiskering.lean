import UecInLean.CategoryTheory.NatTrans.Def

namespace UecInLean.CategoryTheory.NatTrans

universe v v' v'' v₀ v₁ u u' u'' u₀ u₁
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E] {A : Type u₀} [Category.{v₀} A] {B : Type u₁} [Category.{v₁} B]

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

theorem whiskerLeft_eq_whiskering {F G : A ⥤ B} (η : F ⟹ G) (H : B ⥤ C) : whiskerLeft η H = whiskering (.id A) η H := by ext <;> simp

theorem whiskerRight_eq_whiskering {G H : B ⥤ C} (η : G ⟹ H) (F : A ⥤ B) : whiskerRight F η = whiskering F η (.id C) := by ext <;> simp
