import UecInLean.Category.Basic

namespace UecInLean

universe v u

structure Opposite (α : Type u) where
  op ::
  unop : α
postfix:max "ᵒᵖ" => Opposite

namespace Opposite

variable {α}

theorem op_unop (x : αᵒᵖ) : op (unop x) = x := rfl
theorem unop_op (x : α) : unop (op x) = x := rfl

end Opposite

instance Category.Opposite {C : Type u} [Category C] : Category Cᵒᵖ where
  hom X Y := Y.unop ⟶ X.unop
  id X := Category.id X.unop
  comp f g := g ≫ f
  id_comp := Category.comp_id
  comp_id := Category.id_comp
  comp_assoc f g h := by rw [Category.comp_assoc h g f]

@[simp, grind =]
theorem Category.Opposite_hom {C : Type u} [Category C] {X Y : C} : (⟨X⟩ : Cᵒᵖ) ⟶ ⟨Y⟩ = Y ⟶ X := rfl
@[simp, grind =]
theorem Category.Opposite_id {C : Type u} [Category C] (X : C) : @Category.id Cᵒᵖ _ ⟨X⟩ = Category.id X := rfl
@[simp, grind =]
theorem Category.Opposite_comp {C : Type u} [Category C]
  {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) : Category.comp f g = @Category.comp C _ _ _ _ g f := rfl
