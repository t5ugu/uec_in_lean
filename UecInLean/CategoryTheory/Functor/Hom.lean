import UecInLean.CategoryTheory.Functor.toSet

namespace UecInLean.CategoryTheory.Functor
universe w v u
variable {C : Type u} [Category.{v} C]

-- ここが `Type v` であることによって、Kan 拡張では `Hom_D : Type v_C` や、Kan Lift では `Ob_D : Type u_C` などの制限が生まれた。非本質的と考え、`ULift` してある。
def Hom (a : C) : C ⥤ Type (max v w) where
  obj b := ULift (a ⟶ b)
  map f g := ⟨g.down ≫ f⟩
  map_id x := by {
    funext g
    cases g
    simp
  }
  map_comp := by simp

@[simp]
theorem Hom.obj_def (a b : C) : (Hom a).obj b = ULift (a ⟶ b) := rfl
@[simp]
theorem Hom.map_def {a b c : C} (f : b ⟶ c) (g : ULift (a ⟶ b)) : (Hom a).map f g = ⟨g.down ≫ f⟩ := rfl

end UecInLean.CategoryTheory.Functor
