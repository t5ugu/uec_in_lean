import UecInLean.CategoryTheory.Category.Def

namespace UecInLean.CategoryTheory

universe v v' v'' v''' u u' u'' u'''

structure Functor (C : Type u) (D : Type u') [Category.{v} C] [Category.{v'} D] where
  obj : C → D
  map {x y : C} : (x ⟶ y) → (obj x ⟶ obj y)
  map_id (x : C) : map (𝟙 x) = 𝟙 (obj x)
  map_comp {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    map (f ≫ g) = (map f) ≫ (map g)

/--
  関手圏の対象は `Type max (u u' v v')`
  関手圏の射は `Type max (u v')`
 -/
infixr:30 " ⥤ " => Functor

namespace Functor

attribute [simp, grind =] map_id map_comp

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E] {B : Type u'''} [Category.{v'''} B]

theorem congrArg_map
  (F : C ⥤ D) {x y : C} {f g : x ⟶ y} (h : f = g) :
  F.map f = F.map g := by rw [h]

def id (C : Type u) [Category.{v} C] : C ⥤ C where
  obj x := x
  map f := f
  map_id x := by rfl
  map_comp f g := by rfl

@[simp]
theorem id_obj (x : C) :
  (id C).obj x = x := rfl
@[simp]
theorem id_map {x y : C} (f : x ⟶ y) :
  (id C).map f = f := rfl

def comp (F : C ⥤ D) (G : D ⥤ E) : C ⥤ E where
    obj x := G.obj (F.obj x)
    map f := G.map (F.map f)
    map_id x := by rw [map_id F, map_id G]
    map_comp f g := by rw [map_comp F, map_comp G]
infixr:90 " ⋙ " => Functor.comp

@[simp, grind =]
theorem comp_obj (F : C ⥤ D) (G : D ⥤ E) (x : C) :
  (F ⋙ G).obj x = G.obj (F.obj x) := rfl

@[simp, grind =]
theorem comp_map {x y : C} (f : x ⟶ y)
  (F : C ⥤ D) (G : D ⥤ E) :
  (F ⋙ G).map f = G.map (F.map f) := rfl

class Full (F : C ⥤ D) where
  full {x y : C} : Function.Surjective (@F.map x y)
theorem map_surj (F : C ⥤ D) [Full F] {x y : C} (f : F.obj x ⟶ F.obj y) : ∃ g : x ⟶ y, F.map g = f := Full.full f

class Faithful (F : C ⥤ D) where
  faithful {x y : C} : Function.Injective (@F.map x y)
theorem map_inj (F : C ⥤ D) [Faithful F] {x y : C} {f g : x ⟶ y} (h : F.map f = F.map g) : f = g :=
  Faithful.faithful h

theorem map_inj_iff (F : C ⥤ D) [Faithful F] {x y : C} {f g : x ⟶ y} : F.map f = F.map g ↔ f = g := ⟨map_inj F, congrArg (F.map)⟩

class FullyFaithful (F : C ⥤ D) extends Full F, Faithful F
noncomputable def pull (F : C ⥤ D) [FullyFaithful F] {x y : C} (f : F.obj x ⟶ F.obj y) : x ⟶ y := Classical.choose (map_surj F f)
theorem map_pull (F : C ⥤ D) [FullyFaithful F] {x y : C} (f : F.obj x ⟶ F.obj y) : F.map (pull F f) = f := Classical.choose_spec (map_surj F f)

@[ext (iff:=false)]
theorem ext {F G : C ⥤ D} (h_obj : ∀ x, F.obj x = G.obj x) (h_map : ∀ {x y : C} (f : x ⟶ y), F.map f = Category.eq_to_hom (h_obj x) ≫ (G.map f) ≫ Category.eq_to_hom (h_obj y).symm) : F = G := by {
  obtain ⟨obj, map⟩ := F
  rw [← funext_iff] at h_obj
  subst h_obj
  simp only [Category.eq_to_hom_refl, Category.comp_id, Category.id_comp] at h_map
  congr
  funext x y f
  exact h_map f
}

@[simp]
theorem id_comp (F : C ⥤ D) : id C ⋙ F = F := rfl

@[simp]
theorem comp_id (F : C ⥤ D) : F ⋙ id D = F := rfl

@[simp, grind =]
theorem comp_assoc (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ B) :
  (F ⋙ G) ⋙ H = F ⋙ (G ⋙ H) := rfl

end UecInLean.CategoryTheory.Functor
