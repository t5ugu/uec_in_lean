import UecInLean.CategoryTheory.Category.Def
import UecInLean.CategoryTheory.Functor.Def

namespace UecInLean.CategoryTheory.Category

universe v v₀ u u₀

structure Discrete (α : Type u) : Type (max u v) where
  as : α

@[simp]
theorem Discrete.mk_as {α : Type u} (a : α) : (Discrete.mk a).as = a := rfl

instance (α : Type u) : Category.{v} (Discrete.{v} α) where
  hom x y := ULift <| PLift (x = y)
  id x := ⟨⟨rfl⟩⟩
  comp := fun ⟨⟨hf⟩⟩ ⟨⟨hg⟩⟩ => ⟨⟨by rw [hf, hg]⟩⟩
  id_comp := fun ⟨⟨_⟩⟩ => rfl
  comp_id := fun ⟨⟨_⟩⟩ => rfl
  comp_assoc := fun ⟨⟨_⟩⟩ ⟨⟨_⟩⟩ ⟨⟨_⟩⟩ => rfl

instance {α : Type u} {x y : Discrete α} : Subsingleton (x ⟶ y) where
  allEq := fun ⟨⟨_⟩⟩ ⟨⟨_⟩⟩ => rfl

@[simp]
theorem Discrete.eq_of_hom {α : Type u} {x y : Discrete α} : x ⟶ y → x = y := by
  intro ⟨⟨h⟩⟩; exact h

@[simp]
theorem Discrete.id_def {α : Type u} {x : Discrete α} : ULift.up (PLift.up (Eq.refl x)) = 𝟙 x := by rfl

@[simp]
theorem Discrete.hom_eq {α : Type u} {x y : Discrete α} (h : x = y) : (f : x ⟶ y) → ULift.up (PLift.up h) = f := fun ⟨⟨_⟩⟩ => rfl

abbrev DiscN (n : Nat) := Discrete.{0} (Fin n)
