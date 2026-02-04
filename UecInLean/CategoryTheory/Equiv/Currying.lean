import UecInLean.CategoryTheory.Category.Product
import UecInLean.CategoryTheory.Category.Set
import UecInLean.CategoryTheory.Equiv.Def

namespace UecInLean.CategoryTheory.Equiv

universe u₀ u₁ u₂ v₀ v₁ v₂
variable {C : Type u₀} {D : Type u₁} {E : Type u₂} [Category.{v₀} C] [Category.{v₁} D] [Category.{v₂} E]

def Functor.curry (F : (C × D) ⥤ E) : C ⥤ (D ⥤ E) where
  obj x := {
    obj y := F.obj (x, y)
    map f := F.map (𝟙 x, f)
    map_id y := F.map_id (x, y)
    map_comp f g := by simp [← F.map_comp]
  }
  map f := {
    app y := F.map (f, 𝟙 y)
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

def Functor.uncurry (F : C ⥤ (D ⥤ E)) : (C × D) ⥤ E where
  obj x := (F.obj x.1).obj x.2
  map {x y} f := (F.map f.1).app x.2 ≫ (F.obj y.1).map f.2
  map_id X := by simp
  map_comp := by {
    intro _ ⟨x₂, y₂⟩ _ ⟨f₁, g₁⟩ ⟨f₂, g₂⟩
    simp
    rw [← Category.comp_assoc ((F.obj x₂).map g₁), (F.map f₂).naturality g₁, Category.comp_assoc]
  }

def Functor_currying : ((C × D) ⥤ E) ≃ (C ⥤ (D ⥤ E)) where
  fore := {
    obj F := Functor.curry F
    map θ := {
      app x := {
        app y := θ.app (x, y)
        naturality g := by simp [Functor.curry]
      }
      naturality f := by {
        apply NatTrans.ext
        intro y
        simp [Functor.curry]
      }
    }
    map_id F := by {
      apply NatTrans.ext; intro x
      apply NatTrans.ext; intro y
      rfl
    }
    map_comp θ₁ θ₂ := by {
      apply NatTrans.ext
      intro x
      apply NatTrans.ext
      intro y
      rfl
    }
  }
  back := {
    obj := Functor.uncurry,
    map θ := {
      app := fun ⟨x, y⟩ => (θ.app x).app y
      naturality := by {
        intro x y f
        simp only [Functor.uncurry, Category.comp_assoc]
        rw [NatTrans.naturality, ← Category.comp_assoc, ← Category.Functor_comp_app, θ.naturality, Category.Functor_comp_app, Category.comp_assoc]
      }
    }
    map_id F := by {
      apply NatTrans.ext
      intro ⟨x, y⟩
      rfl
    }
    map_comp θ₁ θ₂ := by {
      apply NatTrans.ext
      intro ⟨x, y⟩
      rfl
    }
  }
  fore_back_id := Iso.NaturalIso.ofComponents (fun F => Iso.NaturalIso.ofComponents (fun x => by {
    simp [Functor.curry, Functor.uncurry]; exact Iso.refl _
  }) (by {
    intro x y f
    simp [Functor.curry, Functor.uncurry]
    rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id, ← F.map_comp, Category.Product_comp]
    rw [Category.comp_id, Category.id_comp]
    rfl
  })) (by {
    intro F G θ
    apply NatTrans.ext
    intro ⟨x, y⟩
    simp [Functor.curry, Functor.uncurry, Iso.NaturalIso.ofComponents, Iso.refl_hom]
  })
  back_fore_id := Iso.NaturalIso.ofComponents (fun F => Iso.NaturalIso.ofComponents (fun x => Iso.NaturalIso.ofComponents (fun _ => Iso.refl _) (by {
    intro y y' f
    simp [Functor.curry, Functor.uncurry, Iso.refl_hom]
  })) (by {
    intro x x' f
    apply NatTrans.ext
    intro y
    simp [Functor.curry, Functor.uncurry, Iso.NaturalIso.ofComponents, Iso.refl_hom]
  })) (by {
    intro F G θ
    apply NatTrans.ext
    intro x
    apply NatTrans.ext
    intro y
    simp [Functor.curry, Functor.uncurry, Iso.NaturalIso.ofComponents, Iso.refl_hom]
  })
end UecInLean.CategoryTheory.Equiv
