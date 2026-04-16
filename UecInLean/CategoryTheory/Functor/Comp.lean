import UecInLean.CategoryTheory.Category.Functor
import UecInLean.CategoryTheory.NatTrans.Whiskering

namespace UecInLean.CategoryTheory.Functor

universe v v' v'' u u' u''
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E]

def Comp : (C ⥤ D) ⥤ (D ⥤ E) ⥤ (C ⥤ E) where
  obj F := {
    obj G := F ⋙ G
    map α := NatTrans.whiskerRight F α
    map_id _ := by apply NatTrans.ext; simp
    map_comp _ _ := by apply NatTrans.ext; simp
  }
  map α := {
    app F := {
      app x := F.map (α.app x)
      naturality f := by {
        rw [comp_map, comp_map, ← F.map_comp, ← F.map_comp]
        exact F.congrArg_map (α.naturality f)
      }
    }
    naturality β := by apply NatTrans.ext; simp
  }
  map_id _ := by apply NatTrans.ext; intros; apply NatTrans.ext; simp
  map_comp _ _ := by apply NatTrans.ext; intros; apply NatTrans.ext; simp

def compLeft (F : C ⥤ D) : (D ⥤ E) ⥤ (C ⥤ E) := Comp.obj F
def compRight (G : D ⥤ E) : (C ⥤ D) ⥤ (C ⥤ E) := {
  obj F := F ⋙ G
  map α := NatTrans.whiskerLeft α G
  map_id _ := by apply NatTrans.ext; simp
  map_comp _ _ := by apply NatTrans.ext; simp
}
