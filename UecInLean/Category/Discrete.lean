import UecInLean.Category.Basic

namespace UecInLean

universe v v₀ u u₀

structure Discrete (α : Type u) where
  as : α

theorem Discrete.mk_as {α : Type u} (a : α) : (Discrete.mk a).as = a := rfl

instance (α : Type u) : Category.{v} (Discrete α) where
  hom x y := ULift <| PLift (x = y)
  id x := ⟨⟨rfl⟩⟩
  comp := fun ⟨⟨hf⟩⟩ ⟨⟨hg⟩⟩ => ⟨⟨by rw [hf, hg]⟩⟩
  id_comp := fun ⟨⟨_⟩⟩ => rfl
  comp_id := fun ⟨⟨_⟩⟩ => rfl
  comp_assoc := fun ⟨⟨_⟩⟩ ⟨⟨_⟩⟩ ⟨⟨_⟩⟩ => rfl

instance {α : Type u} {x y : Discrete α} : Subsingleton (x ⟶ y) where
  allEq := fun ⟨⟨_⟩⟩ ⟨⟨_⟩⟩ => rfl -- by proof irrelevance

-- 離散圏とみなしていたことを忘れる関手
def Discrete.forget {α : Type u} [Category.{v} α] : Discrete α ⥤ α where
  obj x := x.as
  map := fun ⟨⟨h⟩⟩ => by cases h; exact 𝟙 (as _)
  map_id x := rfl
  map_comp := fun ⟨⟨hf⟩⟩ ⟨⟨hg⟩⟩ => by cases hf; cases hg; rw [Category.comp_id]

def Discrete.functor {I : Type u₀} {C : Type u} [Category.{v} C] (f : I → C) : Functor.{v₀} (Discrete I) C := {
  obj := f ∘ Discrete.as
  map := fun ⟨⟨h⟩⟩ => by cases h; exact 𝟙 (f (as _))
  map_id _ := rfl
  map_comp := fun ⟨⟨hf⟩⟩ ⟨⟨hg⟩⟩ => by cases hf; cases hg; simp
}

abbrev DiscN (n : Nat) := Discrete (Fin n)

end UecInLean
