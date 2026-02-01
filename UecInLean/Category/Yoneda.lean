import UecInLean.Category.Basic
import UecInLean.Category.Opposite
import UecInLean.Category.Iso

namespace UecInLean

universe v u

def hom_co {C : Type u} [Category.{u} C] (A : C) : C ⥤ (Type u) where
  obj B := A ⟶ B
  map f g := g ≫ f
  map_id := by simp
  map_comp := by simp

def yoneda_map {C : Type u} [Category.{u} C] (A : C) (F : C ⥤ Type u) : (hom_co A ⟹ F) ≅ F.obj A where
  hom τ := τ.app A (𝟙 A)
  inv a := {
    app B g := F.map g a
    naturality g := by {
      simp only [hom_co, Category.Set_comp]
      conv => {
        lhs
        intro x
        rw [F.map_comp, Category.Set_comp]
        simp only
      }
    }
  }
  hom_inv_id := by {
    funext τ; ext a; funext g
    have := funext_iff.mp (τ.naturality g) (𝟙 A)
    simp only [hom_co, Category.Set_comp, Category.id_comp] at this
    exact this.symm
  }
  inv_hom_id := by simp

def yoneda_embedding {C : Type u} [Category.{u} C] {A B : C} : (hom_co A ⟹ hom_co B) ≅ ((⟨A⟩ : Cᵒᵖ) ⟶ ⟨B⟩) := Iso.trans (yoneda_map A (hom_co B)) (Iso.of_eq rfl)

-- def yoneda (C : Type u) [Category.{v} C] : C ⥤ (Cᵒᵖ ⥤ Type v) := {
--   obj a := {
--     obj := fun ⟨y⟩ => y ⟶ a
--     map f g := f ≫ g
--     map_id := by intro ⟨y⟩; simp
--     map_comp := by {
--       intro ⟨y⟩ ⟨z⟩ ⟨w⟩ f g
--       funext h
--       simp only [Category.Opposite_hom, Category.Set_comp] at f g h ⊢
--       exact Category.comp_assoc g f h
--     }
--   }
--   map f := {
--     app _ g := g ≫ f
--     naturality := by simp_all
--   }
--   map_id x := by {
--     apply NatTrans.ext
--     simp only [Category.comp_id, Category.Fun_id, NatTrans.id_app]
--     exact fun _ => rfl
--   }
--   map_comp f g := by {
--     apply NatTrans.ext
--     simp
--   }
-- }

-- def yoneda' (C : Type u) [Category.{v} C] : Cᵒᵖ ⥤ C ⥤ Type v := sorry

-- theorem Functor.toSet_map_comp {C : Type u} [Category.{v} C]
--   (F : C ⥤ Type v) {a b c : C} (f : a ⟶ b) (g : b ⟶ c) (x : F.obj a) : F.map (f ≫ g) x = F.map g (F.map f x) := by sorry

-- def yoneda_lemma {C : Type u} [Category.{u} C] {F : Cᵒᵖ ⥤ Type u} {a : C} : (yoneda C).obj a ⟹ F ≅ F.obj ⟨a⟩ := {
--   hom f := f.app ⟨a⟩ (𝟙 a)
--   inv f := {
--     app := by {
--       intro ⟨b⟩ g
--       simp only [yoneda] at g
--       exact F.map g f
--     }
--     naturality g := by {
--       funext p
--       simp only [yoneda, Category.Set_comp]
--       apply Functor.toSet_map_comp
--       done
--     }
--   }
--   hom_inv_id := by {
--     funext θ
--     ext ⟨b⟩
--     funext g
--     simp only [Category.Set_comp, Category.Set_id, id_eq, yoneda] at g ⊢


--   }
--   inv_hom_id := sorry
-- }
