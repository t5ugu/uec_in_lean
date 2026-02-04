import UecInLean.Category.Basic
import UecInLean.Category.Iso

namespace UecInLean

universe v u u'
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v} D]

class IsAdjunction (F : C ⥤ D) (G : D ⥤ C) where
  adj (c : C) (d : D) : (F.obj c ⟶ d) ≅ (c ⟶ G.obj d)

namespace Adjunction

def adj (F : C ⥤ D) (G : D ⥤ C) [IsAdjunction F G] (c : C) (d : D) := @IsAdjunction.adj C _ D _ F G _ c d

variable {F : C ⥤ D} {G : D ⥤ C} [IsAdjunction F G]
def rightAdjunct {c : C} {d : D} (f : F.obj c ⟶ d) : c ⟶ G.obj d :=
  (adj F G c d).hom f
def leftAdjunct {c : C} {d : D} (g : c ⟶ G.obj d) : F.obj c ⟶ d :=
  (adj F G c d).inv g

theorem comm_map  {c c' : C} {d d' : D} (f : F.obj c ⟶ d) (h : F.obj c' ⟶ d') (p : c ⟶ c') (q : d ⟶ d') : f ≫ q = F.map p ≫ h ↔ (rightAdjunct f) ≫ G.map q = p ≫ (rightAdjunct h) := by {
  constructor
  {
    intro eq
    unfold rightAdjunct
    rw []
    -- rw [← Iso.hom_eq_inv_eq, Category.assoc, eq, ← Category.assoc, Category.iso.inv_hom_eq]
  }
  {}
}

end UecInLean
