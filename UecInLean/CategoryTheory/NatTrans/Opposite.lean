import UecInLean.CategoryTheory.NatTrans.Def
import UecInLean.CategoryTheory.Functor.Opposite

namespace UecInLean.CategoryTheory.NatTrans

universe v v' v'' u u' u''

def op {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {F G : C ⥤ D} (α : F ⟹ G) : G.op ⟹ F.op where
  app x := α.app x.unop
  naturality _ := by simp [Functor.op_map, Category.Opposite.comp_def, α.naturality]

def unop {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ⟹ G) : G.unop ⟹ F.unop where
  app x := α.app ⟨x⟩
  naturality _ := by {
    rw [Functor.unop_map, Functor.unop_map, ← Category.Opposite.comp_def, ← α.naturality, Category.Opposite.comp_def]
  }

theorem op_inj {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {F G : C ⥤ D} (α β : F ⟹ G) (h : α.op = β.op) : α = β := by ext; apply congrFun (congrArg NatTrans.app h)

theorem unop_inj {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α β : F ⟹ G) (h : α.unop = β.unop) : α = β := by ext; apply congrFun (congrArg NatTrans.app h)

end UecInLean.CategoryTheory.NatTrans
