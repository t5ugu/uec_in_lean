import UecInLean.CategoryTheory.Universality.Pullback
import UecInLean.CategoryTheory.Universality.Product
import UecInLean.CategoryTheory.Universality.Equalizer
import UecInLean.CategoryTheory.CommSq

namespace UecInLean.CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C]

set_option autoImplicit true

def CommSq.toPullback (sq : CommSq C p q r s) : Limit.Pullback r s := ⟨_, p, q, sq⟩
theorem CommSq.toPullback_fst (sq : CommSq C p q r s) : sq.toPullback.fst = p := rfl
theorem CommSq.toPullback_snd (sq : CommSq C p q r s) : sq.toPullback.snd = q := rfl

namespace Limit
open Pullback

def outer_pb_of_left_pb (left : CommSq C (f : a ⟶ b) ax mi xy) (right : CommSq C g mi cz yz) (rpb : right.toPullback.isLimit) (lpb : left.toPullback.isLimit) : (left.join_right right).toPullback.isLimit := by {
  intro d
  apply Unique.of_default_of_allEq
  {
    let dcyz : Pullback cz yz := ⟨d.pt, d.fst, d.snd ≫ xy, by simp [d.comm]⟩
    have db := (rpb dcyz).default
    let dbxy : Pullback mi xy := ⟨d.pt, db.hom, d.snd, db.comm_snd⟩
    have da := (lpb dbxy).default
    exact ⟨da.hom, by {
      rw [CommSq.toPullback_fst, ← Category.comp_assoc, show da.hom ≫ f = db.hom by exact da.comm_fst]
      exact db.comm_fst
    }, da.comm_snd⟩
  }
  {
    intro h h'

    have db_eq : h.hom ≫ f = h'.hom ≫ f := by {
      let dcyz : Pullback cz yz := ⟨d.pt, d.fst, d.snd ≫ xy, by simp [d.comm]⟩
      let db : dcyz ⟶ right.toPullback := ⟨h.hom ≫ f, by rw [CommSq.toPullback_fst, Category.comp_assoc]; exact h.comm_fst, by rw [CommSq.toPullback_snd, Category.comp_assoc, left, ← Category.comp_assoc]; exact Category.comp_congr_left h.comm_snd xy⟩
      let db' : dcyz ⟶ right.toPullback := ⟨h'.hom ≫ f, by rw [CommSq.toPullback_fst, Category.comp_assoc]; exact h'.comm_fst, by rw [CommSq.toPullback_snd, Category.comp_assoc, left, ← Category.comp_assoc]; exact Category.comp_congr_left h'.comm_snd xy⟩
      have db_eq := (rpb dcyz).allEq db db'
      rw [Hom_eq_iff] at db_eq
      exact db_eq
    }

    let dbxy : Pullback mi xy := ⟨d.pt, h.hom ≫ f, d.snd, by rw [Category.comp_assoc, left, ← Category.comp_assoc]; exact Category.comp_congr_left h.comm_snd xy⟩
    let da : dbxy ⟶ left.toPullback := ⟨h.hom, by rfl, h.comm_snd⟩
    let da' : dbxy ⟶ left.toPullback := ⟨h'.hom, by rw [left.toPullback_fst, ← db_eq], h'.comm_snd⟩
    have da_eq : da = da' := (lpb dbxy).allEq da da'
    rw [Hom_eq_iff] at da_eq ⊢
    exact da_eq
  }
}

def left_pb_of_outer_pb (left : CommSq C (f : a ⟶ b) ax mi xy) (right : CommSq C (g : b ⟶ c) mi cz yz) (rpb : right.toPullback.isLimit) (opb : (left.join_right right).toPullback.isLimit) : left.toPullback.isLimit := by {
  intro d
  apply Unique.of_default_of_allEq
  {
    let dcxz : Pullback cz (xy ≫ yz) := ⟨d.pt, d.fst ≫ g, d.snd, by rw [← Category.comp_assoc, ← d.comm, Category.comp_assoc, Category.comp_assoc, right]⟩
    have da := (opb dcxz).default
    let dcyz : Pullback cz yz := ⟨d.pt, d.fst ≫ g, d.snd ≫ xy, by rw [← d.comm, Category.comp_assoc, Category.comp_assoc, right]⟩
    let d_hf_b : dcyz ⟶ right.toPullback := ⟨da.hom ≫ f, by rw [Category.comp_assoc]; exact da.comm_fst, by rw [CommSq.toPullback_snd, Category.comp_assoc, left, ← Category.comp_assoc]; exact Category.comp_congr_left da.comm_snd xy⟩
    let d_fst_b : dcyz ⟶ right.toPullback := ⟨d.fst, by rfl, d.comm⟩
    have db_eq := (rpb dcyz).allEq d_hf_b d_fst_b
    rw [Hom_eq_iff] at db_eq
    exact ⟨da.hom, db_eq, da.comm_snd⟩
  }
  {
    intro h h'

    let dcxz : Pullback cz (xy ≫ yz) := ⟨d.pt, d.fst ≫ g, d.snd, by rw [← Category.comp_assoc, ← d.comm, Category.comp_assoc, Category.comp_assoc, right]⟩
    let da : dcxz ⟶ (left.join_right right).toPullback := ⟨h.hom, by {
      rw [CommSq.toPullback_fst, ← Category.comp_assoc]
      exact Category.comp_congr_left h.comm_fst g
    }, h.comm_snd⟩
    let da' : dcxz ⟶ (left.join_right right).toPullback := ⟨h'.hom, by {
      rw [CommSq.toPullback_fst, ← Category.comp_assoc]
      exact Category.comp_congr_left h'.comm_fst g
    }, h'.comm_snd⟩
    have da_eq : da = da' := (opb dcxz).allEq da da'
    rw [Hom_eq_iff] at da_eq ⊢
    exact da_eq
  }
}

def HasPullback_of_HasProduct_of_HasEqualizer [HasProduct C] [HasEqualizer C] : HasPullback C where
  pullback {a b c} f g := by {
    obtain ⟨p, p₀, p₁⟩ := a ⨯ b
    obtain ⟨u, e, comm⟩ := HasEqualizer.equalizer (p₀ ≫ f) (p₁ ≫ g)
    exact ⟨u, e ≫ p₀, e ≫ p₁, by rw [Category.comp_assoc, Category.comp_assoc, comm]⟩
  }
  isPullback {a b c} f g := by {
    intro ⟨v, q₀, q₁, comm⟩
    apply Unique.of_default_of_allEq
    {
      have ⟨h, h_comm_fst, h_comm_snd⟩ := (HasProduct.isProd a b ⟨v, q₀, q₁⟩).default
      have ⟨k, k_comm⟩ := (HasEqualizer.isEqualizer ((a ⨯ b).fst ≫ f) ((a ⨯ b).snd ≫ g) ⟨v, h, by {
        simp at h_comm_fst h_comm_snd
        rw [← Category.comp_assoc, h_comm_fst, ← Category.comp_assoc, h_comm_snd, comm]
      }⟩).default
      exact ⟨k, by {
        rw [← Category.comp_assoc, k_comm, h_comm_fst]
      }, by {
        rw [← Category.comp_assoc, k_comm, h_comm_snd]
      }⟩
    }
    {
      intro ⟨k, k_comm_fst, k_comm_snd⟩ ⟨k', k'_comm_fst, k'_comm_snd⟩
      simp only at k k' k_comm_fst k_comm_snd k'_comm_fst k'_comm_snd
      let e := (HasEqualizer.equalizer ((a ⨯ b).fst ≫ f) ((a ⨯ b).snd ≫ g)).fork
      have ek_ek' := (HasProduct.isProd a b ⟨v, q₀, q₁⟩).allEq
        ⟨k ≫ e, by rw [Category.comp_assoc, k_comm_fst], by rw [Category.comp_assoc, k_comm_snd]⟩
        ⟨k' ≫ e, by rw [Category.comp_assoc, k'_comm_fst], by rw [Category.comp_assoc, k'_comm_snd]⟩

      rw [Product.Hom_eq_iff] at ek_ek'
      simp at ek_ek'

      have := (HasEqualizer.isEqualizer ((a ⨯ b).fst ≫ f) ((a ⨯ b).snd ≫ g) ⟨v, k ≫ e, by rw [Category.comp_assoc, ← Category.comp_assoc _ _ f, ← Category.comp_assoc, k_comm_fst, comm, ← k_comm_snd]; simp [e]⟩).allEq
        ⟨k, by simp [e]⟩
        ⟨k', by simp [e, ek_ek']⟩
      rw [Equalizer.Hom_eq_iff] at this
      rw [Pullback.Hom_eq_iff]
      exact this
    }
  }

end Limit

open Limit

def Functor.prod_right {C : Type u} [Category.{v} C] [HasProduct C] (a : C) : Functor C C where
  obj b := (b ⨯ a).pt
  map {b c} f := (⟨
      (b ⨯ a).pt,
      (b ⨯ a).fst ≫ f,
      (b ⨯ a).snd
    ⟩ : Product c a).univHom.hom
  map_id b := by {
    rw [Category.comp_id, Product.univHom_self_eq_id, Product.id_hom_eq]
  }
  map_comp {b c d} f g := by {
    let qfg : Product d a := ⟨(b ⨯ a).pt, (b ⨯ a).fst ≫ f ≫ g, (b ⨯ a).snd⟩
    let qf : Product c a := ⟨(b ⨯ a).pt, (b ⨯ a).fst ≫ f, (b ⨯ a).snd⟩
    let qg : Product d a := ⟨(c ⨯ a).pt, (c ⨯ a).fst ≫ g, (c ⨯ a).snd⟩

    let h₂ : qfg ⟶ d ⨯ a := ⟨
      qf.univHom.hom ≫ qg.univHom.hom,
      by {
        rw [Category.comp_assoc, qg.univHom.comm₀, show qg.fst = (c ⨯ a).fst ≫ g by rfl, ← Category.comp_assoc, qf.univHom.comm₀]
        simp [qf, qfg]
      },
      by rw [Category.comp_assoc, qg.univHom.comm₁, qf.univHom.comm₁]
    ⟩

    rw [qfg.universality.allEq qfg.univHom h₂]
  }
