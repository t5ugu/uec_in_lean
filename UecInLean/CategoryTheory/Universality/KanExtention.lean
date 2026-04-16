import UecInLean.CategoryTheory.Functor.Comp
import UecInLean.CategoryTheory.NatTrans.Opposite
import UecInLean.CategoryTheory.Universality.Object
import UecInLean.CategoryTheory.Iso.Def

namespace UecInLean.CategoryTheory.Universality

universe v v' v'' u u' u''
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {U : Type u''} [Category.{v''} U]

class HasLan (F : C ⥤ D) (E : C ⥤ U) extends HasUniversalArrow F.compLeft E

def HasLan.lan {F : C ⥤ D} {E : C ⥤ U} [h : HasLan F E] : D ⥤ U := h.repr
def HasLan.unit {F : C ⥤ D} {E : C ⥤ U} [h : HasLan F E] : E ⟹ F ⋙ h.lan := h.toHasUniversalArrow.unit

-- class HasLan (F : C ⥤ D) (E : C ⥤ U) where
--   lan : D ⥤ U
--   unit : E ⟹ F ⋙ lan
--   universality (S : D ⥤ U) (θ : E ⟹ F ⋙ S) : ∃! τ : lan ⟹ S, θ = unit.vcomp (τ.whiskerRight F)

class HasRan (F : C ⥤ D) (E : C ⥤ U) extends HasLan F.op E.op

def HasRan.ran {F : C ⥤ D} {E : C ⥤ U} [h : HasRan F E] : D ⥤ U := h.lan.unop
def HasRan.counit {F : C ⥤ D} {E : C ⥤ U} [h : HasRan F E] : F ⋙ h.ran ⟹ E
  := (Functor.op_comp F h.ran).symm ▸ h.unit |>.unop

-- class HasRan (F : C ⥤ D) (E : C ⥤ U) where
--   ran : D ⥤ U
--   counit : F ⋙ ran ⟹ E
--   universality (S : D ⥤ U) (θ : F ⋙ S ⟹ E) : ∃! τ : S ⟹ ran, θ = (τ.whiskerRight F).vcomp counit

class HasLanLift (F : D ⥤ C) (E : U ⥤ C) extends HasUniversalArrow F.compRight E

-- class HasLanLift (F : D ⥤ C) (E : U ⥤ C) where
--   lanLift : U ⥤ D
--   unit : E ⟹ lanLift ⋙ F
--   universality (S : U ⥤ D) (θ : E ⟹ S ⋙ F) : ∃! τ : lanLift ⟹ S, θ = unit.vcomp (τ.whiskerLeft F)

class HasRanLift (F : D ⥤ C) (E : U ⥤ C) extends HasUniversalArrow F.op.compRight E.op

-- class HasRanLift (F : D ⥤ C) (E : U ⥤ C) where
--   ranLift : U ⥤ D
--   counit : ranLift ⋙ F ⟹ E
--   universality (S : U ⥤ D) (θ : S ⋙ F ⟹ E) : ∃! τ : S ⟹ ranLift, θ = (τ.whiskerLeft F).vcomp counit
