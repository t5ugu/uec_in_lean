import UecInLean.Category.Basic
import UecInLean.Category.Iso

namespace UecInLean

universe u u' u'' v v' v''

structure Equiv (A : Type u) [Category.{v} A] (B : Type u') [Category.{v'} B] where
  fore : A ⥤ B
  back : B ⥤ A
  fore_back_id : ∀ x, (fore ⋙ back).obj x ≅ x
  back_fore_id : ∀ x, (back ⋙ fore).obj x ≅ x
infix:25 " ≃ " => Equiv

variable {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B] {C : Type u''} [Category.{v''} C]

class IsFaithful (F : A ⥤ B) where
  faithful {x y : A} : Function.Injective (@F.map x y)
theorem IsFaithful.map_inj (F : A ⥤ B) [IsFaithful F] {x y : A} {f g : x ⟶ y} (h : F.map f = F.map g) : f = g :=
  IsFaithful.faithful h

class IsFull (F : A ⥤ B) where
  full {x y : A} : Function.Surjective (@F.map x y)
theorem IsFull.map_surj (F : A ⥤ B) [IsFull F] {x y : A} (f : F.obj x ⟶ F.obj y) : ∃ g : x ⟶ y, F.map g = f := IsFull.full f

class IsFullyFaithful (F : A ⥤ B) extends IsFull F, IsFaithful F

noncomputable def IsFullyFaithful.inv (F : A ⥤ B) [IsFullyFaithful F] {x y : A} (f : F.obj x ⟶ F.obj y) : x ⟶ y :=
  Classical.choose (IsFull.map_surj F f)

class IsConservative (F : A ⥤ B) where
  conservative {x y : A} (f : x ⟶ y) : IsIso (F.map f) → IsIso f

def IsConservative.iso_of_iso_map (F : A ⥤ B) [IsConservative F] {x y : A} (f : x ⟶ y) (h : IsIso (F.map f)) : IsIso f :=
  IsConservative.conservative f h

class IsEssentiallyInjective (F : A ⥤ B) where
  essInj {x y : A} : F.obj x ≅ F.obj y → Nonempty (x ≅ y)

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

instance {F : A ⥤ B} [IsFull F] [IsConservative F] : IsEssentiallyInjective F where
  essInj e := by {
    have ⟨g, hg⟩ := IsFull.full e.hom

    have := IsConservative.iso_of_iso_map F g
    rw [hg] at this
    obtain ⟨g_inv, hg_inv₁, hg_inv₂⟩ := this e.isIso
    exact ⟨⟨g, g_inv, hg_inv₁, hg_inv₂⟩⟩
  }

section

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

end
