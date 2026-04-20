import UecInLean.CategoryTheory.Functor.Comp
import UecInLean.CategoryTheory.NatTrans.Opposite
import UecInLean.CategoryTheory.Universality.Object
import UecInLean.CategoryTheory.Iso.Def

namespace UecInLean.CategoryTheory.Universality

universe v v' v'' u u' u''
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {U : Type u''} [Category.{v''} U]

class HasLan (F : C ⥤ D) (E : C ⥤ U) extends HasUniversalArrow F.compLeft E

def HasLan.lan {F : C ⥤ D} {E : C ⥤ U} [h : HasLan F E] : D ⥤ U := h.repr
def HasLan.unit {F : C ⥤ D} {E : C ⥤ U} [h : HasLan F E] : E ⟹ F ⋙ h.lan := h.arrow
def HasLan.default {F : C ⥤ D} {E : C ⥤ U} [h : HasLan F E] {S : D ⥤ U} (θ : E ⟹ F ⋙ S) : h.lan ⟹ S := h.hom S θ
theorem HasLan.universality {F : C ⥤ D} {E : C ⥤ U} [h : HasLan F E] {S : D ⥤ U} (θ : E ⟹ F ⋙ S) : θ = h.unit.vcomp ((h.default θ).whiskerRight F) := h.toHasUniversalArrow.universality S θ
theorem HasLan.unique {F : C ⥤ D} {E : C ⥤ U} [h : HasLan F E] {S : D ⥤ U} (θ : E ⟹ F ⋙ S) (τ : h.lan ⟹ S) (w : θ = h.unit.vcomp (τ.whiskerRight F)) : τ = h.default θ := h.toHasUniversalArrow.unique S θ τ w

class HasRan (F : C ⥤ D) (E : C ⥤ U) extends HasLan F.op E.op

def HasRan.ran {F : C ⥤ D} {E : C ⥤ U} [h : HasRan F E] : D ⥤ U := h.repr.unop
def HasRan.counit {F : C ⥤ D} {E : C ⥤ U} [h : HasRan F E] : F ⋙ h.ran ⟹ E := h.arrow.unop
def HasRan.default {F : C ⥤ D} {E : C ⥤ U} [h : HasRan F E] {S : D ⥤ U} (θ : F ⋙ S ⟹ E) : S ⟹ h.ran := h.hom S.op θ.op |>.unop
theorem HasRan.universality {F : C ⥤ D} {E : C ⥤ U} [h : HasRan F E] {S : D ⥤ U} (θ : F ⋙ S ⟹ E) : θ = ((h.default θ).whiskerRight F).vcomp h.counit := congrArg NatTrans.unop <| h.toHasUniversalArrow.universality S.op θ.op
theorem HasRan.unique {F : C ⥤ D} {E : C ⥤ U} [h : HasRan F E] {S : D ⥤ U} (θ : F ⋙ S ⟹ E) (τ : S ⟹ h.ran) (w : θ = ((τ.whiskerRight F).vcomp h.counit)) : τ = h.default θ := congrArg NatTrans.unop <| h.toHasUniversalArrow.unique S.op θ.op τ.op (congrArg NatTrans.op w)

class HasLanLift (F : D ⥤ C) (E : U ⥤ C) extends HasUniversalArrow F.compRight E

def HasLanLift.lanLift {F : D ⥤ C} {E : U ⥤ C} [h : HasLanLift F E] : U ⥤ D := h.repr
def HasLanLift.unit {F : D ⥤ C} {E : U ⥤ C} [h : HasLanLift F E] : E ⟹ h.lanLift ⋙ F := h.arrow
def HasLanLift.default {F : D ⥤ C} {E : U ⥤ C} [h : HasLanLift F E] {S : U ⥤ D} (θ : E ⟹ S ⋙ F) : h.lanLift ⟹ S := h.hom S θ
theorem HasLanLift.universality {F : D ⥤ C} {E : U ⥤ C} [h : HasLanLift F E] {S : U ⥤ D} (θ : E ⟹ S ⋙ F) : θ = h.unit.vcomp ((h.default θ).whiskerLeft F) := h.toHasUniversalArrow.universality S θ
theorem HasLanLift.unique {F : D ⥤ C} {E : U ⥤ C} [h : HasLanLift F E] {S : U ⥤ D} (θ : E ⟹ S ⋙ F) (τ : h.lanLift ⟹ S) (w : θ = h.unit.vcomp (τ.whiskerLeft F)) : τ = h.default θ := h.toHasUniversalArrow.unique S θ τ w

class HasRanLift (F : D ⥤ C) (E : U ⥤ C) extends HasLanLift F.op E.op

def HasRanLift.ranLift {F : D ⥤ C} {E : U ⥤ C} [h : HasRanLift F E] : U ⥤ D := h.repr.unop
def HasRanLift.counit {F : D ⥤ C} {E : U ⥤ C} [h : HasRanLift F E] : h.ranLift ⋙ F ⟹ E := h.arrow.unop
def HasRanLift.default {F : D ⥤ C} {E : U ⥤ C} [h : HasRanLift F E] {S : U ⥤ D} (θ : S ⋙ F ⟹ E) : S ⟹ h.ranLift := h.hom S.op θ.op |>.unop
theorem HasRanLift.universality {F : D ⥤ C} {E : U ⥤ C} [h : HasRanLift F E] {S : U ⥤ D} (θ : S ⋙ F ⟹ E) : θ = ((h.default θ).whiskerLeft F).vcomp h.counit := congrArg NatTrans.unop <| h.toHasUniversalArrow.universality S.op θ.op
theorem HasRanLift.unique {F : D ⥤ C} {E : U ⥤ C} [h : HasRanLift F E] {S : U ⥤ D} (θ : S ⋙ F ⟹ E) (τ : S ⟹ h.ranLift) (w : θ = ((τ.whiskerLeft F).vcomp h.counit)) : τ = h.default θ := congrArg NatTrans.unop <| h.toHasUniversalArrow.unique S.op θ.op τ.op (congrArg NatTrans.op w)
