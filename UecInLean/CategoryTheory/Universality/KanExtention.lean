import UecInLean.CategoryTheory.NatTrans
import UecInLean.CategoryTheory.Universality.Unique
import UecInLean.CategoryTheory.Iso.Def

namespace UecInLean.CategoryTheory.Universality

universe v v' v'' u u' u''
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {U : Type u''} [Category.{v''} U]

class HasLan (F : C ⥤ D) (E : C ⥤ U) where
  lan : D ⥤ U
  unit : E ⟹ F ⋙ lan
  universality (S : D ⥤ U) (θ : E ⟹ F ⋙ S) : ∃! τ : lan ⟹ S, θ = unit.vcomp (τ.whiskerRight F)

class HasRan (F : C ⥤ D) (E : C ⥤ U) where
  ran : D ⥤ U
  counit : F ⋙ ran ⟹ E
  universality (S : D ⥤ U) (θ : F ⋙ S ⟹ E) : ∃! τ : S ⟹ ran, θ = (τ.whiskerRight F).vcomp counit

class HasLanLift (F : D ⥤ C) (E : U ⥤ C) where
  lanLift : U ⥤ D
  unit : E ⟹ lanLift ⋙ F
  universality (S : U ⥤ D) (θ : E ⟹ S ⋙ F) : ∃! τ : lanLift ⟹ S, θ = unit.vcomp (τ.whiskerLeft F)

class HasRanLift (F : D ⥤ C) (E : U ⥤ C) where
  ranLift : U ⥤ D
  counit : ranLift ⋙ F ⟹ E
  universality (S : U ⥤ D) (θ : S ⋙ F ⟹ E) : ∃! τ : S ⟹ ranLift, θ = (τ.whiskerLeft F).vcomp counit
