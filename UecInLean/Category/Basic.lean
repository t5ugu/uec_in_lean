
namespace UecInLean

universe v u u₀ v₀ u₁ v₁

class Category (C : Type u) where
  hom : C → C → Type v
  id (x : C) : hom x x
  comp {x y z : C} : hom x y → hom y z → hom x z
  id_comp {x y : C} (f : hom x y) : comp (id x) f = f
  comp_id {x y : C} (f : hom x y) : comp f (id y) = f
  comp_assoc {w x y z : C} (f : hom x y) (g : hom y z) (h : hom z w) :
    comp (comp f g) h = comp f (comp g h)

infixr:80 " ⟶ " => Category.hom
infixr:90 " ≫ " => Category.comp

abbrev Hom (C : Type u) [Category C] (x y : C) : Type v := x ⟶ y

attribute [grind =] Category.id_comp Category.comp_id Category.comp_assoc

structure Functor (C D : Type u) [Category C] [Category D] where
  obj : C → D
  map {x y : C} : (x ⟶ y) → (obj x ⟶ obj y)
  map_id {x : C} : map (Category.id x) = Category.id (obj x)
  map_comp {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    map (f ≫ g) = (map f) ≫ (map g)

infixr:80 " ⥤ " => Functor

attribute [grind =] Functor.map_id Functor.map_comp

structure NatTrans {C D : Type u} [Category C] [Category D]
  (F G : C ⥤ D) where
  app (x : C) : F.obj x ⟶ G.obj x
  naturality {x y : C} (f : x ⟶ y) :
    F.map f ≫ app y = app x ≫ G.map f

infixr:80 " ⟹ " => NatTrans

attribute [grind =] NatTrans.naturality

def NatTrans.id {C D : Type u} [Category C] [Category D]
  (F : C ⥤ D) : F ⟹ F where
    app x := Category.id (F.obj x)
    naturality f := by grind
@[grind =]
theorem NatTrans.id_app {C D : Type u} [Category C] [Category D]
  (F : C ⥤ D) (x : C) : (NatTrans.id F).app x = Category.id (F.obj x) := rfl

def NatTrans.vcomp {C D : Type u} [Category C] [Category D]
  {F G H : C ⥤ D}
  (η : F ⟹ G) (θ : G ⟹ H) : F ⟹ H where
    app x := η.app x ≫ θ.app x
    naturality f := by rw [← Category.comp_assoc]; grind
@[grind =]
theorem NatTrans.vcomp_app {C D : Type u} [Category C] [Category D]
  {F G H : C ⥤ D}
  (η : F ⟹ G) (θ : G ⟹ H) (x : C) :
  (NatTrans.vcomp η θ).app x = η.app x ≫ θ.app x := rfl

@[ext]
def NatTrans.ext {C D : Type u} [Category C] [Category D]
  {F G : C ⥤ D} (η θ : F ⟹ G)
  (h : ∀ x : C, η.app x = θ.app x) : η = θ := by {
    cases η; cases θ; congr; funext; apply h
  }

instance Set : Category (Type u) where
  hom A B := A → B
  id _ := id
  comp f g := fun x => g (f x)
  id_comp _ := rfl
  comp_id _ := rfl
  comp_assoc _ _ _ := rfl

instance Fun (C D : Type u) [Category C] [Category D] : Category (C ⥤ D) where
  hom := NatTrans
  id := .id
  comp := .vcomp
  id_comp η := by ext; grind
  comp_id η := by ext; grind
  comp_assoc η θ ζ := by ext; grind



end UecInLean
