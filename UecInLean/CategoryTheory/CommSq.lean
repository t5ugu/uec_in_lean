import UecInLean.CategoryTheory.Category.Def

namespace UecInLean.CategoryTheory

universe v u

/-- 第一引数に圏を取るのは、`autoImplicit` を使いやすくするため -/
def CommSq (C : Type u) [Category.{v} C] {a b c d : C} (up : a ⟶ b) (left : a ⟶ c) (right : b ⟶ d) (down : c ⟶ d) := up ≫ right = left ≫ down

namespace CommSq

set_option autoImplicit true

variable {C : Type u} [Category.{v} C]
theorem join_right (sq1 : CommSq C ab ad be de) (sq2 : CommSq C bc be cf ef) : CommSq C (ab ≫ bc) ad cf (de ≫ ef) := by rw [CommSq, Category.comp_assoc, sq2, ← Category.comp_assoc, sq1, Category.comp_assoc]
