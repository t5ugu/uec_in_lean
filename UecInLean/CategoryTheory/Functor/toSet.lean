import UecInLean.CategoryTheory.Category.Set
import UecInLean.CategoryTheory.Functor.Def

namespace UecInLean.CategoryTheory.Functor

universe u v
variable {C : Type u} [Category.{v} C]

@[simp]
theorem toSet_map_comp (F : C ⥤ Type v) {a b c : C} (f : a ⟶ b) (g : b ⟶ c) (x : F.obj a) : F.map (f ≫ g) x = F.map g (F.map f x) := by simp

end UecInLean.CategoryTheory.Functor
