import UecInLean.Category.Basic
import UecInLean.Category.Iso

namespace UecInLean

universe v v' u u'

structure Opposite (α : Type u) where
  op ::
  unop : α
postfix:max "ᵒᵖ" => Opposite

namespace Opposite

variable {α}

theorem op_unop (x : αᵒᵖ) : op (unop x) = x := rfl
theorem unop_op (x : α) : unop (op x) = x := rfl

end Opposite

instance {C : Type u} [Category C] : Category Cᵒᵖ where
  hom X Y := Y.unop ⟶ X.unop
  id X := 𝟙 X.unop
  comp f g := g ≫ f
  id_comp := Category.comp_id
  comp_id := Category.id_comp
  comp_assoc f g h := by rw [Category.comp_assoc h g f]

@[simp, grind =]
theorem Category.Opposite_hom {C : Type u} [Category C] {X Y : Cᵒᵖ} : X ⟶ Y = Y.unop ⟶ X.unop := rfl
@[simp, grind =]
theorem Category.Opposite_id {C : Type u} [Category C] (X : C) : @CategoryStruct.id Cᵒᵖ _ ⟨X⟩ = 𝟙 X := rfl
@[simp, grind =]
theorem Category.Opposite_comp {C : Type u} [Category C]
  {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) : f ≫ g = @CategoryStruct.comp C _ _ _ _ g f := rfl

def Functor.Opposite {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  (F : C ⥤ D) : Cᵒᵖ ⥤ Dᵒᵖ where
  obj := fun ⟨x⟩ => ⟨F.obj x⟩
  map f := F.map f
  map_id x := F.map_id x.unop
  map_comp f g := F.map_comp g f

def Functor.unOpposite {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  (F : Cᵒᵖ ⥤ Dᵒᵖ) : C ⥤ D where
  obj x := (F.obj ⟨x⟩).unop
  map f := F.map f
  map_id x := F.map_id ⟨x⟩
  map_comp f g := F.map_comp g f
