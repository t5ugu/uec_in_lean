import UecInLean.CategoryTheory.Category.Discrete
import UecInLean.CategoryTheory.Functor.Def

namespace UecInLean.CategoryTheory.Functor
open Category

universe v v₀ v₁ u u₀ u₁ u'
variable {C : Type u} [Category.{v} C] {D : Type u'}

-- 離散圏とみなしていたことを忘れる関手
def Discrete.forget : Discrete C ⥤ C where
  obj x := x.as
  map := fun ⟨⟨h⟩⟩ => by cases h; exact 𝟙 (Discrete.as _)
  map_id x := rfl
  map_comp := fun ⟨⟨hf⟩⟩ ⟨⟨hg⟩⟩ => by cases hf; cases hg; rw [Category.comp_id]

def Discrete.func {I : Type u₀} (f : I → C) : (Discrete.{v₀} I) ⥤ C := {
  obj := f ∘ Discrete.as
  map := fun ⟨⟨h⟩⟩ => by cases h; exact 𝟙 (f (Discrete.as _))
  map_id _ := rfl
  map_comp := fun ⟨⟨hf⟩⟩ ⟨⟨hg⟩⟩ => by cases hf; cases hg; simp
}

@[simp]
theorem to_Disc1_obj (F : C ⥤ DiscN 1) (c : C) : F.obj c = ⟨0⟩ := by {
  obtain ⟨n, hlt⟩ := F.obj c
  rw [Nat.lt_one_iff] at hlt
  cases hlt
  rfl
}

@[simp]
theorem to_Discrete_map_eq_id (F : C ⥤ Discrete D) {c₁ : C} (f : c₁ ⟶ c₁)
: F.map f = 𝟙 (F.obj c₁)
:= by {
  obtain ⟨⟨h⟩⟩ := F.map f
  cases h
  rfl
}

@[simp]
theorem to_Disc1_map_eq (F : C ⥤ DiscN 1) {c₁ c₂ : C} (f : c₁ ⟶ c₂) : F.map f = (by { simp; exact 𝟙 (⟨0⟩ : DiscN 1)}) := by {
  obtain ⟨⟨h⟩⟩ := F.map f
  rfl
}

end UecInLean.CategoryTheory.Functor
