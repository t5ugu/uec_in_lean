import UecInLean.CategoryTheory.Functor.Def

namespace UecInLean.CategoryTheory.Category

universe v₀ v₁ v u₀ u₁ u
variable {C₀ : Type u₀} [Category.{v₀} C₀] {C₁ : Type u₁} [Category.{v₁} C₁] {D : Type u} [Category.{v} D]

structure Comma (F : C₀ ⥤ D) (G : C₁ ⥤ D) where
  c₀ : C₀
  c₁ : C₁
  f : F.obj c₀ ⟶ G.obj c₁

structure Comma.Hom {F : C₀ ⥤ D} {G : C₁ ⥤ D} (X Y : Comma F G) where
  g₀ : X.c₀ ⟶ Y.c₀
  g₁ : X.c₁ ⟶ Y.c₁
  comm : F.map g₀ ≫ Y.f = X.f ≫ G.map g₁

instance {F : C₀ ⥤ D} {G : C₁ ⥤ D} : Category (Comma F G) where
  hom := Comma.Hom
  id _ := ⟨𝟙 _, 𝟙 _, by simp⟩
  comp := by {
    intro _ _ _ ⟨f₀, f₁, comm⟩ ⟨g₀, g₁, comm'⟩
    exact ⟨f₀ ≫ g₀, f₁ ≫ g₁, by {
      rw [Functor.map_comp, Category.comp_assoc, comm', ← Category.comp_assoc, comm]
      simp
    }⟩
  }
  comp_id _ := by simp
  id_comp _ := by simp
  comp_assoc _ _ _ := by simp

@[simp]
theorem Comma.id_def {F : C₀ ⥤ D} {G : C₁ ⥤ D} (X : Comma F G) :
  𝟙 X = ⟨𝟙 X.c₀, 𝟙 X.c₁, by simp⟩ := by rfl

@[simp]
theorem Comma.comp_def {F : C₀ ⥤ D} {G : C₁ ⥤ D}
  {X Y Z : Comma F G} (f : X ⟶ Y) (g : Y ⟶ Z) :
  f ≫ g = ⟨f.g₀ ≫ g.g₀, f.g₁ ≫ g.g₁, by {
    rw [Functor.map_comp, Category.comp_assoc, g.comm, ← Category.comp_assoc, f.comm, Functor.map_comp]
    simp
  }⟩ := by rfl

infix:800 " ↓ " => Comma
