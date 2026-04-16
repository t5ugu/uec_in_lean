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
