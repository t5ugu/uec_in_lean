import UecInLean.Category.Basic

namespace UecInLean

universe v v' u u'
variable {C : Type u} [Category.{v} C] {J : Type u'} [Category.{v'} J]

def Diagonal : C ⥤ J ⥤ C where
  obj c := {
    obj _ := c
    map _ := 𝟙 c
    map_id _ := by rfl
    map_comp _ _ := by rw [Category.comp_id]
  }
  map f := {
    app _ := f
    naturality _ := by simp
  }
  map_id c := NatTrans.ext (fun _ => rfl)
  map_comp f g := NatTrans.ext (fun _ => rfl)
