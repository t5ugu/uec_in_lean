
namespace UecInLean

@[simp, grind =_]
theorem id_refl {α} : (fun x : α => x) = id := rfl

universe v v' v'' u u' u''

class CategoryStruct (C : Type u) where
  hom : C → C → Type v
  id (x : C) : hom x x
  comp {x y z : C} : hom x y → hom y z → hom x z

class Category (C : Type u) extends CategoryStruct.{v} C where
  id_comp {x y : C} (f : hom x y) : comp (id x) f = f := by grind
  comp_id {x y : C} (f : hom x y) : comp f (id y) = f := by grind
  comp_assoc {w x y z : C} (f : hom x y) (g : hom y z) (h : hom z w) :
    comp (comp f g) h = comp f (comp g h) := by grind

infixr:80 " ⟶ " => CategoryStruct.hom
prefix:100 "𝟙 " => CategoryStruct.id
infixr:90 " ≫ " => CategoryStruct.comp

attribute [simp, grind =] Category.id_comp Category.comp_id Category.comp_assoc

structure Functor (C : Type u) (D : Type u') [Category.{v} C] [Category.{v'} D] where
  obj : C → D
  map {x y : C} : (x ⟶ y) → (obj x ⟶ obj y)
  map_id (x : C) : map (𝟙 x) = 𝟙 (obj x) := by grind
  map_comp {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    map (f ≫ g) = (map f) ≫ (map g) := by grind

infixr:30 " ⥤ " => Functor

attribute [simp, grind =] Functor.map_id Functor.map_comp

def Functor.id (C : Type u) [Category C] : C ⥤ C where
  obj x := x
  map f := f
  map_id x := by rfl
  map_comp f g := by rfl

@[simp, grind =]
theorem Functor.id_obj {C : Type u} [Category C] (x : C) :
  (Functor.id C).obj x = x := rfl
@[simp, grind =]
theorem Functor.id_map {C : Type u} [Category C] {x y : C} (f : x ⟶ y) :
  (Functor.id C).map f = f := rfl

def Functor.comp {A : Type u} {B : Type u'} {C : Type u''}
  [Category.{v} A] [Category.{v'} B] [Category.{v''} C]
  (F : A ⥤ B) (G : B ⥤ C) : A ⥤ C where
    obj x := G.obj (F.obj x)
    map f := G.map (F.map f)
    map_id x := by rw [Functor.map_id F, Functor.map_id G]
    map_comp f g := by rw [Functor.map_comp F, Functor.map_comp G]
infixr:90 " ⋙ " => Functor.comp

@[simp, grind =]
theorem Functor.comp_obj {A : Type u} {B : Type u'} {C : Type u''}
  [Category.{v} A] [Category.{v'} B] [Category.{v''} C]
  (F : A ⥤ B) (G : B ⥤ C) (x : A) :
  (F ⋙ G).obj x = G.obj (F.obj x) := rfl
@[simp, grind =]
theorem Functor.comp_map {A : Type u} {B : Type u'} {C : Type u''}
  [Category.{v} A] [Category.{v'} B] [Category.{v''} C]
  {x y : A} (f : x ⟶ y)
  (F : A ⥤ B) (G : B ⥤ C) :
  (F ⋙ G).map f = G.map (F.map f) := rfl

structure NatTrans {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  (F G : C ⥤ D) where
  app (x : C) : F.obj x ⟶ G.obj x
  naturality {x y : C} (f : x ⟶ y) :
    F.map f ≫ app y = app x ≫ G.map f := by grind

infixr:80 " ⟹ " => NatTrans

attribute [simp, grind =] NatTrans.naturality

def NatTrans.id {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  (F : C ⥤ D) : F ⟹ F where
    app x := 𝟙 (F.obj x)
    naturality f := by rw [Category.comp_id, Category.id_comp]

@[simp, grind =]
theorem NatTrans.id_app {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  (F : C ⥤ D) (x : C)
: (NatTrans.id F).app x = 𝟙 (F.obj x) := rfl

def NatTrans.vcomp {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  {F G H : C ⥤ D} (η : F ⟹ G) (θ : G ⟹ H)
: F ⟹ H where
  app x := η.app x ≫ θ.app x
  naturality f := by rw [← Category.comp_assoc, η.naturality f, Category.comp_assoc, θ.naturality f, ← Category.comp_assoc]

@[simp, grind =]
theorem NatTrans.vcomp_app {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  {F G H : C ⥤ D} (η : F ⟹ G) (θ : G ⟹ H) (x : C)
: (NatTrans.vcomp η θ).app x = η.app x ≫ θ.app x := rfl

@[ext 9000, grind ext]
theorem NatTrans.ext {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  {F G : C ⥤ D} {η θ : F ⟹ G} (h : ∀ x : C, η.app x = θ.app x)
: η = θ := by {
  cases η; cases θ;
  congr
  exact funext h
}

instance Category.Set : Category.{u} (Type u) where
  hom A B := A → B
  id _ := _root_.id
  comp f g := fun x => g (f x)
  id_comp f := by rfl
  comp_id f := by rfl
  comp_assoc f g h := by rfl

@[simp, grind =]
theorem Category.Set_hom {A B : Type u} : A ⟶ B = (A → B) := rfl
@[simp, grind =]
theorem Category.Set_id {A : Type u} : 𝟙 A = _root_.id := rfl
@[simp, grind =]
theorem Category.Set_comp {A B C : Type u} (f : A ⟶ B) (g : B ⟶ C) : f ≫ g = fun x => g (f x) := rfl

instance Category.Fun (C : Type u) (D : Type u') [Category.{v} C] [Category.{v'} D] : Category (C ⥤ D) where
  hom := NatTrans
  id := .id
  comp := .vcomp
  id_comp _ := by ext; rw [NatTrans.vcomp_app, NatTrans.id_app, Category.id_comp]
  comp_id _ := by ext; rw [NatTrans.vcomp_app, NatTrans.id_app, Category.comp_id]
  comp_assoc _ _ _ := by ext; rw [NatTrans.vcomp_app, NatTrans.vcomp_app, NatTrans.vcomp_app, NatTrans.vcomp_app, Category.comp_assoc]
#print axioms Category.Fun

@[simp, grind =]
theorem Category.Fun_hom {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  (F G : C ⥤ D) : F ⟶ G = F ⟹ G := rfl
@[simp, grind =]
theorem Category.Fun_id {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  (F : C ⥤ D) : 𝟙 F = NatTrans.id F := rfl
@[simp, grind =]
theorem Category.Fun_comp {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  {F G H : C ⥤ D} (η : F ⟶ G) (θ : G ⟶ H) : η ≫ θ = NatTrans.vcomp η θ := rfl

instance (P : Type u) [LE P] [Std.IsPreorder P] : Category.{v} P where
  hom x y := ULift <| PLift (x ≤ y)
  id x := ⟨⟨Std.le_refl x⟩⟩
  comp := fun ⟨⟨hxy⟩⟩ ⟨⟨hyz⟩⟩ => ⟨⟨Std.le_trans hxy hyz⟩⟩
  id_comp := fun ⟨⟨_⟩⟩ => rfl
  comp_id := fun ⟨⟨_⟩⟩ => rfl
  comp_assoc := fun ⟨⟨_⟩⟩ ⟨⟨_⟩⟩ ⟨⟨_⟩⟩ => rfl

instance {P : Type u} [LE P] [Std.IsPreorder P]
  {x y : P} : Subsingleton (x ⟶ y) where
  allEq := fun ⟨⟨_⟩⟩ ⟨⟨_⟩⟩ => rfl -- by proof irrelevance
