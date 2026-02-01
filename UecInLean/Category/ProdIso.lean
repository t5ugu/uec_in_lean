import UecInLean.Category.Prod
import UecInLean.Category.Iso
import UecInLean.Category.Equiv

namespace UecInLean

universe v v' v'' u u' u''
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E]

def Category.prod_swap : (C × D) ≃ (D × C) where
  fore := prod.Functor.swap C D
  back := prod.Functor.swap D C
  fore_back_id := Iso.of_eq rfl
  back_fore_id := Iso.of_eq rfl

def Category.prod_assoc : ((C × D) × E) ≃ (C × (D × E)) where
  fore := prod.associator
  back := prod.associator_inv
  fore_back_id := Iso.of_eq rfl
  back_fore_id := Iso.of_eq rfl
