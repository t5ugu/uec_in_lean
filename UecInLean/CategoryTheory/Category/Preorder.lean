import UecInLean.CategoryTheory.Category.Def

namespace UecInLean.CategoryTheory
universe v u

instance instPreorder (P : Type u) [LE P] [Std.IsPreorder P] : Category.{v} P where
  hom x y := ULift <| PLift (x ≤ y)
  id x := ⟨⟨Std.le_refl x⟩⟩
  comp := fun ⟨⟨hxy⟩⟩ ⟨⟨hyz⟩⟩ => ⟨⟨Std.le_trans hxy hyz⟩⟩
  id_comp := fun ⟨⟨_⟩⟩ => rfl
  comp_id := fun ⟨⟨_⟩⟩ => rfl
  comp_assoc := fun ⟨⟨_⟩⟩ ⟨⟨_⟩⟩ ⟨⟨_⟩⟩ => rfl

instance instSubsingletonPreorderHom {P : Type u} [LE P] [Std.IsPreorder P]
  {x y : P} : Subsingleton (x ⟶ y) where
  allEq := fun ⟨⟨_⟩⟩ ⟨⟨_⟩⟩ => rfl
