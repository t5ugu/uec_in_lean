import UecInLean.Category.Basic

namespace UecInLean.prod

universe v v' u u'

instance Category.Prod {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D] : Category (C × D) where
  hom X Y := (X.1 ⟶ Y.1) × (X.2 ⟶ Y.2)
  id X := (𝟙 X.1, 𝟙 X.2)
  comp f g := (f.1 ≫ g.1, f.2 ≫ g.2)
  id_comp f := by simp
  comp_id f := by simp
  comp_assoc f g h := by simp

@[simp, grind =]
theorem Category.Prod_hom {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  (X Y : C × D) : @Category.hom (C × D) _ X Y = ((X.1 ⟶ Y.1) × (X.2 ⟶ Y.2)) := rfl
@[simp, grind =]
theorem Category.Prod_id {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  (X : C × D) : @Category.id (C × D) _ X = (Category.id X.1, Category.id X.2) := rfl
@[simp, grind =]
theorem Category.Prod_comp {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  {X Y Z : C × D} (f : X ⟶ Y) (g : Y ⟶ Z) :
  @Category.comp (C × D) _ _ _ _ f g = (f.1 ≫ g.1, f.2 ≫ g.2) := rfl

universe u₀ u₁ u₂ u₀' u₁' v₀ v₁ v₂ v₀' v₁'

variable {C₀ : Type u₀} {C₁ : Type u₁} {D₁ : Type u₀'} {D₂ : Type u₁'}
  [Category.{v₀} C₀] [Category.{v₁} C₁] [Category.{v₀'} D₁] [Category.{v₁'} D₂]

def Functor.fst {C : Type u₀} {D : Type u₁} [Category.{v₀} C] [Category.{v₁} D] : (C × D) ⥤ C where
  obj X := X.1
  map f := f.1
  map_id X := by simp
  map_comp f g := by simp

def Functor.snd {C : Type u₀} {D : Type u₁} [Category.{v₀} C] [Category.{v₁} D] : (C × D) ⥤ D where
  obj X := X.2
  map f := f.2
  map_id X := by simp
  map_comp f g := by simp

def Functor.swap (C : Type u₀) (D : Type u₁) [Category.{v₀} C] [Category.{v₁} D] : (C × D) ⥤ (D × C) where
  obj X := (X.2, X.1)
  map f := (f.2, f.1)
  map_id X := by simp
  map_comp f g := by simp

def Functor.prod
  (F₁ : C₀ ⥤ D₁) (F₂ : C₁ ⥤ D₂) : (C₀ × C₁) ⥤ (D₁ × D₂) where
    obj X := (F₁.obj X.1, F₂.obj X.2)
    map f := (F₁.map f.1, F₂.map f.2)
    map_id X := by simp
    map_comp f g := by simp

def Functor.curry {C : Type u₀} {D : Type u₁} {E : Type u₂}
  [Category.{v₀} C] [Category.{v₁} D] [Category.{v₂} E]
  (F : (C × D) ⥤ E) : C ⥤ (D ⥤ E) where
    obj x := {
      obj y := F.obj (x, y)
      map f := F.map (Category.id x, f)
      map_id y := F.map_id (x, y)
      map_comp f g := by simp [← F.map_comp]
    }
    map f := {
      app y := F.map (f, Category.id y)
      naturality g := by simp [← F.map_comp]
    }
    map_id x := by {
      apply NatTrans.ext
      exact fun y => F.map_id (x, y)
    }
    map_comp f g := by {
      apply NatTrans.ext
      simp [← F.map_comp]
    }

def Functor.uncurry {C : Type u₀} {D : Type u₁} {E : Type u₂}
  [Category.{v₀} C] [Category.{v₁} D] [Category.{v₂} E]
  (F : C ⥤ (D ⥤ E)) : (C × D) ⥤ E where
    obj x := (F.obj x.1).obj x.2
    map {x y} f := (F.map f.1).app x.2 ≫ (F.obj y.1).map f.2
    map_id X := by simp
    map_comp := by {
      intro _ ⟨x₂, y₂⟩ _ ⟨f₁, g₁⟩ ⟨f₂, g₂⟩
      simp
      rw [← Category.comp_assoc ((F.obj x₂).map g₁), (F.map f₂).naturality g₁, Category.comp_assoc]
    }

variable {C : Type u₀} [Category.{v₀} C] {D : Type u₁} [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E]

def associator : ((C × D) × E) ⥤ (C × (D × E)) where
  obj X := (X.1.1, (X.1.2, X.2))
  map f := (f.1.1, (f.1.2, f.2))
  map_id X := by simp
  map_comp f g := by simp

def associator_inv : (C × (D × E)) ⥤ ((C × D) × E) where
  obj X := ((X.1, X.2.1), X.2.2)
  map f := ((f.1, f.2.1), f.2.2)
  map_id X := by simp
  map_comp f g := by simp

end UecInLean.prod
