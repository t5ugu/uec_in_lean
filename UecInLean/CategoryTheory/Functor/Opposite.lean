import UecInLean.CategoryTheory.Category.Opposite
import UecInLean.CategoryTheory.Functor.Def

namespace UecInLean.CategoryTheory.Functor

universe v v' v'' u u' u''
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E]

def op (F : C ⥤ D) : Cᵒᵖ ⥤ Dᵒᵖ where
  obj := fun ⟨x⟩ => ⟨F.obj x⟩
  map := fun f => F.map f
  map_id := fun x => F.map_id x.unop
  map_comp := fun f g => F.map_comp g f

def unop (F : Cᵒᵖ ⥤ Dᵒᵖ) : C ⥤ D where
  obj x := (F.obj ⟨x⟩).unop
  map f := F.map f
  map_id x := F.map_id ⟨x⟩
  map_comp f g := F.map_comp g f

theorem op_unop (F : C ⥤ D) : F.op.unop = F := by simp [op, unop]
theorem unop_op (F : Cᵒᵖ ⥤ Dᵒᵖ) : F.unop.op = F := by ext <;> simp [op, unop]

theorem op_comp (F : C ⥤ D) (G : D ⥤ E) : (F ⋙ G).op = F.op ⋙ G.op := by ext <;> simp [op, comp]
theorem unop_comp (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : Dᵒᵖ ⥤ Eᵒᵖ) : (F ⋙ G).unop = F.unop ⋙ G.unop := by ext <;> simp [unop, comp]

theorem op_obj (F : C ⥤ D) (x : C) : F.op.obj ⟨x⟩ = ⟨F.obj x⟩ := rfl
theorem op_map (F : C ⥤ D) {x y : C} (f : x ⟶ y) : F.op.map f = F.map f := rfl
theorem unop_obj (F : Cᵒᵖ ⥤ Dᵒᵖ) (x : C) : F.unop.obj x = (F.obj ⟨x⟩).unop := rfl
theorem unop_map (F : Cᵒᵖ ⥤ Dᵒᵖ) {x y : C} (f : x ⟶ y) : F.unop.map f = F.map f := rfl

end UecInLean.CategoryTheory.Functor
