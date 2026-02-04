import UecInLean.CategoryTheory.Category.Product
import UecInLean.CategoryTheory.Functor.Def

namespace UecInLean.CategoryTheory

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
