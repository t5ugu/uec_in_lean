import UecInLean.CategoryTheory.Equiv.Def
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Use

namespace UecInLean.CategoryTheory
universe u u' u'' v v' v''

variable {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B] {C : Type u''} [Category.{v''} C]

class Functor.IsEquiv (F : A ⥤ B) where
  equiv : ∃ G : B ⥤ A, ∃ _ : F ⋙ G ≅ Functor.id A, ∃ _ : G ⋙ F ≅ Functor.id B, True
theorem Functor.equivalence (F : A ⥤ B) [F.IsEquiv] : ∃ G : B ⥤ A, ∃ _ : F ⋙ G ≅ Functor.id A, ∃ _ : G ⋙ F ≅ Functor.id B, True := Functor.IsEquiv.equiv

noncomputable def Equiv.of_IsEquiv (F : A ⥤ B) [F.IsEquiv] : A ≃ B := by {
  choose G θ ε _ using F.equivalence
  exact ⟨F, G, θ, ε⟩
}

theorem Functor.IsEquiv.of_Equiv (e : A ≃ B) : e.fore.IsEquiv := by {
  exact ⟨e.back, e.fore_back_id, e.back_fore_id, True.intro⟩
}

class Functor.Conservative (F : A ⥤ B) where
  conservative {x y : A} (f : x ⟶ y) : IsIso (F.map f) → IsIso f

def Functor.IsIso_of_IsIso_map (F : A ⥤ B) [Conservative F] {x y : A} (f : x ⟶ y) (h : IsIso (F.map f)) : IsIso f :=
  Functor.Conservative.conservative f h

class Functor.EssentiallyInjective (F : A ⥤ B) where
  essInj {x y : A} : F.obj x ≅ F.obj y → Nonempty (x ≅ y)
noncomputable def Functor.EssentiallyInjective.pull_equiv (F : A ⥤ B) [Functor.EssentiallyInjective F] {x y : A} (e : F.obj x ≅ F.obj y) : x ≅ y := Classical.choice <| Functor.EssentiallyInjective.essInj e

class Functor.EssentiallySurjective (F : A ⥤ B) where
  essSurj (b : B) : ∃ a, ∃ _ : F.obj a ≅ b, True
theorem Functor.obj_equiv (F : A ⥤ B) [F.EssentiallySurjective] (b : B) : ∃ a, ∃ _ : F.obj a ≅ b, True := Functor.EssentiallySurjective.essSurj b

instance {F : A ⥤ B} [F.FullyFaithful] : F.EssentiallyInjective where
  essInj := by {
    intro c c' ⟨f, g, hfg, hgf⟩
    have ⟨k, hk⟩ := F.map_surj f
    have ⟨h, hh⟩ := F.map_surj g
    exact ⟨k, h, by {
      apply F.map_inj
      rw [F.map_comp, hk, hh, hfg, F.map_id]
    }, by {
      apply F.map_inj
      rw [F.map_comp, hh, hk, hgf, F.map_id]
    }⟩
  }

instance {F : A ⥤ B} [F.FullyFaithful] : F.Conservative where
  conservative := by {
    intro a b f ⟨Ffinv, hFf₁, hFf₂⟩
    have ⟨g, hg⟩ := F.map_surj Ffinv
    rw [← hg, ← F.map_comp, ← F.map_id] at hFf₁ hFf₂
    exact ⟨g, F.map_inj hFf₁, F.map_inj hFf₂⟩
  }

theorem IsEssentiallyInjective_of_IsFull_of_IsConservative {F : A ⥤ B} [F.Full] [F.Conservative] : F.EssentiallyInjective where
  essInj e := by {
    have ⟨g, hg⟩ := F.map_surj e.hom

    have := F.IsIso_of_IsIso_map g
    rw [hg] at this
    obtain ⟨g_inv, hg_inv₁, hg_inv₂⟩ := this e.isIso
    exact ⟨⟨g, g_inv, hg_inv₁, hg_inv₂⟩⟩
  }

variable {F : A ⥤ B} {G : B ⥤ C}

instance [F.Faithful] [G.Faithful] : (F ⋙ G).Faithful where
  faithful := by {
    intro x y f g h
    exact F.map_inj <| G.map_inj h
  }

instance [F.Full] [G.Full] : (F ⋙ G).Full where
  full := by {
    intro x y f
    simp only [Functor.comp_obj] at f
    have ⟨g, hg⟩ := G.map_surj f
    have ⟨h, hh⟩ := F.map_surj g
    exact ⟨h, by rw [F.comp_map, hh, hg]⟩
  }

instance [F.EssentiallySurjective] [G.EssentiallySurjective] : (F ⋙ G).EssentiallySurjective where
  essSurj := by {
    intro c
    have ⟨b, hb, _⟩ := G.obj_equiv c
    have ⟨a, ha, _⟩ := F.obj_equiv b
    exact ⟨a, (ha.map G).trans hb, True.intro⟩
  }

instance [F.IsEquiv] : F.EssentiallySurjective where
  essSurj d := by {
    obtain ⟨G, θ, ε, _⟩ := F.equivalence
    exact ⟨G.obj d, (ε.obj d).trans (.id_obj d), True.intro⟩
  }

instance [F.IsEquiv] : F.Faithful where
  faithful := by {
    intro c c' f f' h
    obtain ⟨G, θ, ε, _⟩ := F.equivalence
    have hf := θ.naturality f
    have hf' := θ.naturality f'
    rw [Functor.comp_map, h, ← Functor.comp_map, hf', Iso.hom_app, (θ.obj c).hom_comp_inj, Functor.id_map, Functor.id_map] at hf
    exact hf.symm
  }

instance [F.IsEquiv] : F.Full where
  full := by {
    intro c c' g
    obtain ⟨G, θ, ε, _⟩ := F.equivalence
    exact ⟨θ.inv.app c ≫ G.map g ≫ θ.hom.app c', by {
      have : G.IsEquiv := ⟨F, ε, θ, True.intro⟩
      have : G.Faithful := inferInstance
      apply G.map_inj

      have : ∀ f : c ⟶ c', (F ⋙ G).map f = θ.hom.app _ ≫ (Functor.id A).map f ≫ θ.inv.app _ := by {
        intro f
        rw [← Category.comp_assoc, ← θ.naturality, Category.comp_assoc, θ.hom_app_comp_inv_app, Category.comp_id]
      }
      rw [← Functor.comp_map, this, Functor.id_map]
      rw [Category.comp_assoc, Category.comp_assoc, θ.hom_app_comp_inv_app]
      simp only [Functor.comp_obj]
      rw [Category.comp_id, ← Category.comp_assoc (θ.hom.app c), θ.hom_app_comp_inv_app, Category.id_comp]
    }⟩
  }

theorem IsEquiv_of_IsFullyFaithful_and_IsEssentiallySurjective (F : A ⥤ B) [F.FullyFaithful] [F.EssentiallySurjective] : F.IsEquiv := by {
  let G : B ⥤ A := {
    obj := by {
      intro d
      exact Classical.choose (F.obj_equiv d)
    },
    map := by {
      intro d d' g
      have εd := Classical.choose <| Classical.choose_spec (F.obj_equiv d)
      have εd' := Classical.choose <| Classical.choose_spec (F.obj_equiv d')
      exact F.pull (εd.hom ≫ g ≫ εd'.inv)
    }
    map_comp := by {
      intro d₀ d₁ d₂ g h
      apply F.map_inj
      rw [F.map_comp, F.map_pull, F.map_pull, F.map_pull]
      conv => {
        rhs
        simp only [Category.comp_assoc]
        rw [← Category.comp_assoc (Iso.inv _), Iso.inv_hom_id, Category.id_comp, ← Category.comp_assoc g]
      }
    }
    map_id := by {
      intro d
      apply F.map_inj
      rw [F.map_pull, Category.id_comp, Iso.hom_inv_id, F.map_id]
    }
  }

  let ε : G ⋙ F ≅ Functor.id B := Iso.NaturalIso.ofComponents (fun b => Classical.choose (Classical.choose_spec (F.obj_equiv b))) (by {
    intro d d' g
    unfold G
    simp only
    rw [Functor.comp_map, Functor.id_map, F.map_pull, Category.comp_assoc,Category.comp_assoc, Iso.inv_hom_id, Category.comp_id]
  })

  exact ⟨G, Iso.NaturalIso.mk {
    app := by {
      intro c
      apply F.pull (ε.hom.app (F.obj c))
    }
    naturality := by {
      intro c c' f
      apply F.map_inj
      rw [F.map_comp, Functor.comp_map, ← Functor.comp_map, F.map_pull, F.map_comp, F.map_pull, Functor.id_map, ε.naturality (F.map f), Functor.id_map]
    }
  } (by {
    intro c
    simp only
    have : F.Conservative := inferInstance
    apply F.IsIso_of_IsIso_map
    rw [F.map_pull]
    exact Iso.isIso _
  }), ε, True.intro⟩
}

theorem IsEquiv_comp (F : A ⥤ B) (G : B ⥤ C) [F.IsEquiv] [G.IsEquiv] : (F ⋙ G).IsEquiv := by {
  have : (F ⋙ G).EssentiallySurjective := inferInstance
  have toFull : (F ⋙ G).Full := inferInstance
  have toFaithful : (F ⋙ G).Faithful := inferInstance
  have : (F ⋙ G).FullyFaithful := { toFull, toFaithful }
  exact IsEquiv_of_IsFullyFaithful_and_IsEssentiallySurjective (F ⋙ G)
}

-- Equiv.trans
noncomputable example {A : Type u} {B : Type u'} {C : Type u''}
  [Category.{v} A] [Category.{v'} B] [Category.{v''} C]
  (e₁ : Equiv A B) (e₂ : Equiv B C) : Equiv A C := by {
  have := Functor.IsEquiv.of_Equiv e₁
  have := Functor.IsEquiv.of_Equiv e₂
  have := IsEquiv_comp e₁.fore e₂.fore
  exact Equiv.of_IsEquiv (e₁.fore ⋙ e₂.fore)
}
