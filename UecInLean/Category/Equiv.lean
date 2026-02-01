import UecInLean.Category.Basic
import UecInLean.Category.Iso
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Use

namespace UecInLean

universe u u' u'' v v' v''

structure Equiv (A : Type u) [Category.{v} A] (B : Type u') [Category.{v'} B] where
  fore : A ⥤ B
  back : B ⥤ A
  fore_back_id : fore ⋙ back ≅ Functor.id A
  back_fore_id : back ⋙ fore ≅ Functor.id B
infix:25 " ≃ " => Equiv

variable {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B] {C : Type u''} [Category.{v''} C]

class IsEquiv (F : A ⥤ B) where
  equiv : ∃ G : B ⥤ A, ∃ _ : F ⋙ G ≅ Functor.id A, ∃ _ : G ⋙ F ≅ Functor.id B, True
theorem IsEquiv.equivalence (F : A ⥤ B) [IsEquiv F] : ∃ G : B ⥤ A, ∃ _ : F ⋙ G ≅ Functor.id A, ∃ _ : G ⋙ F ≅ Functor.id B, True := IsEquiv.equiv

noncomputable def Equiv_of_IsEquiv (F : A ⥤ B) [IsEquiv F] : Equiv A B := by {
  choose G θ ε _ using IsEquiv.equivalence F
  exact ⟨F, G, θ, ε⟩
}

theorem IsEquiv_of_Equiv (e : Equiv A B) : IsEquiv e.fore := by {
  exact ⟨e.back, e.fore_back_id, e.back_fore_id, True.intro⟩
}

class IsFaithful (F : A ⥤ B) where
  faithful {x y : A} : Function.Injective (@F.map x y)
theorem IsFaithful.map_inj (F : A ⥤ B) [IsFaithful F] {x y : A} {f g : x ⟶ y} (h : F.map f = F.map g) : f = g :=
  IsFaithful.faithful h

class IsFull (F : A ⥤ B) where
  full {x y : A} : Function.Surjective (@F.map x y)
theorem IsFull.map_surj (F : A ⥤ B) [IsFull F] {x y : A} (f : F.obj x ⟶ F.obj y) : ∃ g : x ⟶ y, F.map g = f := IsFull.full f

class IsFullyFaithful (F : A ⥤ B) extends IsFull F, IsFaithful F

noncomputable def IsFullyFaithful.pull (F : A ⥤ B) [IsFullyFaithful F] {x y : A} (f : F.obj x ⟶ F.obj y) : x ⟶ y :=
  Classical.choose (IsFull.map_surj F f)
theorem IsFullyFaithful.map_pull (F : A ⥤ B) [IsFullyFaithful F] {x y : A} (f : F.obj x ⟶ F.obj y) : F.map (IsFullyFaithful.pull F f) = f :=
  Classical.choose_spec (IsFull.map_surj F f)

class IsConservative (F : A ⥤ B) where
  conservative {x y : A} (f : x ⟶ y) : IsIso (F.map f) → IsIso f

def IsConservative.iso_of_iso_map (F : A ⥤ B) [IsConservative F] {x y : A} (f : x ⟶ y) (h : IsIso (F.map f)) : IsIso f :=
  IsConservative.conservative f h

class IsEssentiallyInjective (F : A ⥤ B) where
  essInj {x y : A} : F.obj x ≅ F.obj y → Nonempty (x ≅ y)
noncomputable def IsEssentiallyInjective.pull_equiv (F : A ⥤ B) [IsEssentiallyInjective F] {x y : A} (e : F.obj x ≅ F.obj y) : x ≅ y := Classical.choice <| IsEssentiallyInjective.essInj e

class IsEssentiallySurjective (F : A ⥤ B) where
  essSurj (b : B) : ∃ a, Nonempty (F.obj a ≅ b)
def IsEssentiallySurjective.obj_equiv (F : A ⥤ B) [ℱ : IsEssentiallySurjective F] (b : B) : ∃ a, Nonempty (F.obj a ≅ b) := ℱ.essSurj b

instance {F : A ⥤ B} [IsFullyFaithful F] : IsEssentiallyInjective F where
  essInj := by {
    intro c c' ⟨f, g, hfg, hgf⟩
    have ⟨k, hk⟩ := IsFull.map_surj F f
    have ⟨h, hh⟩ := IsFull.map_surj F g
    exact ⟨k, h, by {
      apply IsFaithful.map_inj F
      rw [F.map_comp, hk, hh, hfg, F.map_id]
    }, by {
      apply IsFaithful.map_inj F
      rw [F.map_comp, hh, hk, hgf, F.map_id]
    }⟩
  }

instance {F : A ⥤ B} [IsFullyFaithful F] : IsConservative F where
  conservative := by {
    intro a b f ⟨Ffinv, hFf₁, hFf₂⟩
    have ⟨g, hg⟩ := IsFull.map_surj F Ffinv
    rw [← hg, ← F.map_comp, ← F.map_id] at hFf₁ hFf₂
    exact ⟨g, IsFaithful.map_inj F hFf₁, IsFaithful.map_inj F hFf₂⟩
  }

theorem IsEssentiallyInjective_of_IsFull_of_IsConservative {F : A ⥤ B} [IsFull F] [IsConservative F] : IsEssentiallyInjective F where
  essInj e := by {
    have ⟨g, hg⟩ := IsFull.full e.hom

    have := IsConservative.iso_of_iso_map F g
    rw [hg] at this
    obtain ⟨g_inv, hg_inv₁, hg_inv₂⟩ := this e.isIso
    exact ⟨⟨g, g_inv, hg_inv₁, hg_inv₂⟩⟩
  }

variable {F : A ⥤ B} {G : B ⥤ C}

instance [IsFaithful F] [IsFaithful G] : IsFaithful (F ⋙ G) where
  faithful := by {
    intro x y f g h
    rw [F.comp_map] at h
    exact IsFaithful.faithful <| IsFaithful.faithful h
  }

instance [IsFull F] [IsFull G] : IsFull (F ⋙ G) where
  full := by {
    intro x y f
    simp only [Functor.comp_obj] at f
    have ⟨g, hg⟩ := IsFull.full f
    have ⟨h, hh⟩ := IsFull.full g
    exact ⟨h, by rw [F.comp_map, hh, hg]⟩
  }

instance [IsEssentiallySurjective F] [IsEssentiallySurjective G] : IsEssentiallySurjective (F ⋙ G) where
  essSurj := by {
    intro c
    have ⟨b, ⟨hb⟩⟩ := IsEssentiallySurjective.obj_equiv G c
    have ⟨a, ⟨ha⟩⟩ := IsEssentiallySurjective.obj_equiv F b
    exact ⟨a, by rw [Functor.comp_obj]; exact ⟨(ha.map G).trans hb⟩⟩
  }

instance [IsEquiv F] : IsEssentiallySurjective F where
  essSurj d := by {
    obtain ⟨G, ⟨θ⟩, ⟨ε⟩⟩ := IsEquiv.equivalence F
    exact ⟨G.obj d, ⟨by {
      rw [← Functor.comp_obj]
      exact (ε.obj d).trans (.id_obj d)
    }⟩⟩
  }

instance [IsEquiv F] : IsFaithful F where
  faithful := by {
    intro c c' f f' h
    obtain ⟨G, θ, ε⟩ := IsEquiv.equivalence F
    have hf := θ.naturality f
    have hf' := θ.naturality f'
    rw [Functor.comp_map, h, ← Functor.comp_map, hf', θ.NaturalIso_hom_app_comp_inj, Functor.id_map, Functor.id_map] at hf
    exact hf.symm
  }

instance [IsEquiv F] : IsFull F where
  full := by {
    intro c c' g
    obtain ⟨G, θ, ε, _⟩ := IsEquiv.equivalence F
    exact ⟨θ.inv.app c ≫ G.map g ≫ θ.hom.app c', by {
      have : IsEquiv G := ⟨F, ε, θ, True.intro⟩
      have : IsFaithful G := inferInstance
      apply IsFaithful.map_inj G

      rw [← Functor.comp_map, θ.NaturalIso_map_left_eq_conj_right, Functor.id_map]
      rw [Category.comp_assoc, Category.comp_assoc, θ.hom_app_comp_inv_app]
      simp only [Functor.comp_obj]
      rw [Category.comp_id, ← Category.comp_assoc (θ.hom.app c), θ.hom_app_comp_inv_app, Category.id_comp]
    }⟩
  }

theorem IsEquiv_of_IsFullyFaithful_and_IsEssentiallySurjective (F : A ⥤ B) [IsFullyFaithful F] [IsEssentiallySurjective F] : IsEquiv F := by {
  let G : B ⥤ A := {
    obj := by {
      intro d
      exact Classical.choose (IsEssentiallySurjective.obj_equiv F d)
    },
    map := by {
      intro d d' g
      have εd := Classical.choice <| Classical.choose_spec (IsEssentiallySurjective.obj_equiv F d)
      have εd' := Classical.choice <| Classical.choose_spec (IsEssentiallySurjective.obj_equiv F d')
      exact IsFullyFaithful.pull F (εd.hom ≫ g ≫ εd'.inv)
    }
    map_comp := by {
      intro d₀ d₁ d₂ g h
      apply IsFaithful.map_inj F
      rw [F.map_comp, IsFullyFaithful.map_pull F, IsFullyFaithful.map_pull F, IsFullyFaithful.map_pull F]
      conv => {
        rhs
        simp only [Category.comp_assoc]
        rw [← Category.comp_assoc (Iso.inv _), Iso.inv_hom_id, Category.id_comp, ← Category.comp_assoc g]
      }
    }
    map_id := by {
      intro d
      apply IsFaithful.map_inj F
      rw [IsFullyFaithful.map_pull F, Category.id_comp, Iso.hom_inv_id, F.map_id]
    }
  }

  let ε : G ⋙ F ≅ Functor.id B := Iso.NaturalIso_mk' (fun b => Classical.choice (Classical.choose_spec (IsEssentiallySurjective.obj_equiv F b))) (by {
    intro d d' g
    unfold G
    simp only
    rw [Functor.comp_map, Functor.id_map, IsFullyFaithful.map_pull, Category.comp_assoc,Category.comp_assoc, Iso.inv_hom_id, Category.comp_id]
  })

  exact ⟨G, Iso.NaturalIso_mk {
    app := by {
      intro c
      apply IsFullyFaithful.pull F (ε.hom.app (F.obj c))
    }
    naturality := by {
      intro c c' f
      apply IsFaithful.map_inj F
      rw [F.map_comp, Functor.comp_map, ← Functor.comp_map, IsFullyFaithful.map_pull F, F.map_comp, IsFullyFaithful.map_pull F, Functor.id_map, ε.naturality (F.map f), Functor.id_map]
    }
  } (by {
    intro c
    simp only
    have : IsConservative F := inferInstance
    apply IsConservative.iso_of_iso_map F
    rw [IsFullyFaithful.map_pull F]
    exact Iso.isIso _
  }), ε, True.intro⟩
}

theorem IsEquiv_comp (F : A ⥤ B) (G : B ⥤ C) [IsEquiv F] [IsEquiv G] : IsEquiv (F ⋙ G) := by {
  have : IsEssentiallySurjective (F ⋙ G) := inferInstance
  have full : IsFull (F ⋙ G) := inferInstance
  have faithful : IsFaithful (F ⋙ G) := inferInstance
  have : IsFullyFaithful (F ⋙ G) := IsFullyFaithful.mk
  exact IsEquiv_of_IsFullyFaithful_and_IsEssentiallySurjective (F ⋙ G)
}

noncomputable def Equiv.trans {A : Type u} {B : Type u'} {C : Type u''}
  [Category.{v} A] [Category.{v'} B] [Category.{v''} C]
  (e₁ : Equiv A B) (e₂ : Equiv B C) : Equiv A C := by {
  have := IsEquiv_of_Equiv e₁
  have := IsEquiv_of_Equiv e₂
  have := IsEquiv_comp e₁.fore e₂.fore
  exact Equiv_of_IsEquiv (e₁.fore ⋙ e₂.fore)
}

end UecInLean
