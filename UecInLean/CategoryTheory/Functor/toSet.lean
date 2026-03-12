import UecInLean.CategoryTheory.Category.Set
import UecInLean.CategoryTheory.Functor.Def

namespace UecInLean.CategoryTheory

universe u v w
namespace Functor

variable {C : Type u} [Category.{v} C]

@[simp]
theorem toSet_map_id (F : C ⥤ Type w) {a : C} (x : F.obj a) : F.map (𝟙 a) x = x := by simp

@[simp]
theorem toSet_map_comp (F : C ⥤ Type w) {a b c : C} (f : a ⟶ b) (g : b ⟶ c) (x : F.obj a) : F.map (f ≫ g) x = F.map g (F.map f x) := by simp

end UecInLean.CategoryTheory.Functor
