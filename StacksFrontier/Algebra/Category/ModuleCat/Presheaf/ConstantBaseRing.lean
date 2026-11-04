module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.Sheaf
public import StacksCore.Tactic.StacksAttribute

/-!
# Presheaves of modules over the constant presheaf of rings

Let `Λ` be a ring and `C` a category. A presheaf `Cᵒᵖ ⥤ ModuleCat Λ` of `Λ`-modules is the same
thing as a presheaf of modules over the constant presheaf of rings with value `Λ`: the
restriction maps are already `Λ`-linear, and restriction of scalars along the identity of `Λ`
is the identity functor up to the canonical isomorphism. On the chaotic site every presheaf is
a sheaf, so such a presheaf is equally a sheaf of modules over the constant sheaf of rings.

## Main definitions

* `Stacks.PresheafOfModules.constRing`: the constant presheaf of rings with value `Λ`, and
  `Stacks.PresheafOfModules.constRingSheaf` the constant sheaf of rings on the chaotic site.
* `Stacks.PresheafOfModules.ofFunctor`: a `ModuleCat Λ`-valued presheaf as a presheaf of
  modules over `constRing Λ`, additively and functorially.
* `Stacks.PresheafOfModules.ofFunctorSheaf`: the same as a sheaf of modules over
  `constRingSheaf Λ`.

## Implementation notes

Mathlib's `PresheafOfModules.constFunctor` builds the presheaf of modules whose value is one
fixed module at every object, from a cocone on the presheaf of rings, and carries cofiltered
and smallness hypotheses on the index category; it does not cover a presheaf whose value
varies, which is what an inverse system of modules is.

`PreservesZeroMorphisms` is recorded explicitly for both functors. Instance search derives it
from `Additive`, but left to itself on `SheafOfModules` over this sheaf of rings it does not
terminate.
-/
@[expose] public noncomputable section

open CategoryTheory Opposite

universe a u v₁ u₁

namespace Stacks.PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] (Λ : Type u) [Ring Λ]

/-- The constant presheaf of rings with value `Λ`. -/
abbrev constRing : Cᵒᵖ ⥤ RingCat.{u} := (Functor.const Cᵒᵖ).obj (RingCat.of Λ)

/-- Every restriction map of `constRing Λ` is the identity ring homomorphism of `Λ`. -/
theorem constRing_map_hom {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ((constRing (C := C) Λ).map f).hom = RingHom.id Λ := rfl

/-- A `ModuleCat Λ`-valued presheaf, read as a presheaf of modules over the constant presheaf
of rings with value `Λ`. -/
def ofFunctorObj (F : Cᵒᵖ ⥤ ModuleCat.{a} Λ) :
    _root_.PresheafOfModules.{a} (constRing (C := C) Λ) where
  obj X := F.obj X
  map {X Y} f := F.map f ≫
    (ModuleCat.restrictScalarsId' _ (constRing_map_hom (C := C) Λ f)).inv.app (F.obj Y)

/-- The value of `ofFunctorObj Λ F` at `X` is `F.obj X`. -/
@[simp]
theorem ofFunctorObj_obj (F : Cᵒᵖ ⥤ ModuleCat.{a} Λ) (X : Cᵒᵖ) :
    (ofFunctorObj (C := C) Λ F).obj X = F.obj X := rfl

/-- The restriction maps of `ofFunctorObj Λ F` act on elements as those of `F`. -/
@[simp]
theorem ofFunctorObj_map_apply (F : Cᵒᵖ ⥤ ModuleCat.{a} Λ) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.obj X) : (ofFunctorObj (C := C) Λ F).map f x = F.map f x := rfl

/-- A `ModuleCat Λ`-valued presheaf, read as a presheaf of modules over the constant presheaf
of rings with value `Λ`, functorially. -/
def ofFunctor : (Cᵒᵖ ⥤ ModuleCat.{a} Λ) ⥤ _root_.PresheafOfModules.{a} (constRing (C := C) Λ) where
  obj F := ofFunctorObj Λ F
  map {F G} α :=
    { app X := α.app X
      naturality := fun {X Y} f => by
        ext x
        exact ConcreteCategory.congr_hom (α.naturality f) x }

/-- The functor `ofFunctor Λ` sends `F` to `ofFunctorObj Λ F`. -/
@[simp]
theorem ofFunctor_obj (F : Cᵒᵖ ⥤ ModuleCat.{a} Λ) :
    (ofFunctor (C := C) Λ).obj F = ofFunctorObj Λ F := rfl

/-- The component at `X` of `(ofFunctor Λ).map α` is `α.app X`. -/
@[simp]
theorem ofFunctor_map_app {F G : Cᵒᵖ ⥤ ModuleCat.{a} Λ} (α : F ⟶ G) (X : Cᵒᵖ) :
    ((ofFunctor (C := C) Λ).map α).app X = α.app X := rfl

/-- The functor `ofFunctor Λ` is additive. -/
instance : (ofFunctor.{a} (C := C) Λ).Additive where

/-- A presheaf of modules over the constant presheaf of rings with value `Λ`, read as a
`ModuleCat Λ`-valued presheaf: the restriction maps are semilinear along the identity of `Λ`,
hence already `Λ`-linear. -/
def toFunctorObj (M : _root_.PresheafOfModules.{a} (constRing (C := C) Λ)) :
    Cᵒᵖ ⥤ ModuleCat.{a} Λ where
  obj X := M.obj X
  map {_ Y} f := M.map f ≫
    (ModuleCat.restrictScalarsId' _ (constRing_map_hom (C := C) Λ f)).hom.app (M.obj Y)
  map_id X := by ext x; simp
  map_comp {_ _ _} f g := by ext x; exact M.map_comp_apply f g x

/-- The value of `toFunctorObj Λ M` at `X` is `M.obj X`. -/
@[simp]
theorem toFunctorObj_obj (M : _root_.PresheafOfModules.{a} (constRing (C := C) Λ)) (X : Cᵒᵖ) :
    (toFunctorObj (C := C) Λ M).obj X = M.obj X := rfl

/-- The restriction maps of `toFunctorObj Λ M` act on elements as those of `M`. -/
@[simp]
theorem toFunctorObj_map_apply (M : _root_.PresheafOfModules.{a} (constRing (C := C) Λ))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : M.obj X) :
    (toFunctorObj (C := C) Λ M).map f x = M.map f x := rfl

/-- A presheaf of modules over the constant presheaf of rings with value `Λ`, read as a
`ModuleCat Λ`-valued presheaf, functorially. -/
def toFunctor :
    _root_.PresheafOfModules.{a} (constRing (C := C) Λ) ⥤ (Cᵒᵖ ⥤ ModuleCat.{a} Λ) where
  obj M := toFunctorObj Λ M
  map {M N} φ :=
    { app X := φ.app X
      naturality := fun {X Y} f => by
        ext x
        exact _root_.PresheafOfModules.naturality_apply φ f x }

/-- The component at `X` of `(toFunctor Λ).map φ` is `φ.app X`. -/
@[simp]
theorem toFunctor_map_app {M N : _root_.PresheafOfModules.{a} (constRing (C := C) Λ)} (φ : M ⟶ N)
    (X : Cᵒᵖ) : ((toFunctor (C := C) Λ).map φ).app X = φ.app X := rfl

/-- Reading a `ModuleCat Λ`-valued presheaf as a presheaf of modules over the constant presheaf
of rings and back is the identity. -/
def ofFunctorCompToFunctor :
    ofFunctor.{a} (C := C) Λ ⋙ toFunctor.{a} (C := C) Λ ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun _ => NatIso.ofComponents (fun _ => Iso.refl _) (by intro X Y f; ext x; rfl))
    (by intro F G α; ext X x; rfl)

/-- Reading a presheaf of modules over the constant presheaf of rings as a `ModuleCat Λ`-valued
presheaf and back is the identity. -/
def toFunctorCompOfFunctor :
    toFunctor.{a} (C := C) Λ ⋙ ofFunctor.{a} (C := C) Λ ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun _ => _root_.PresheafOfModules.isoMk (fun _ => Iso.refl _) (by intro X Y f; ext x; rfl))
    (by intro M N φ; ext X x; rfl)

/-- **A presheaf of modules over the constant presheaf of rings with value `Λ` is the same thing
as a `ModuleCat Λ`-valued presheaf.**  The restriction maps of such a presheaf of modules are
semilinear along the identity of `Λ`, which is to say `Λ`-linear, and that is the only data a
`ModuleCat Λ`-valued presheaf carries. -/
def ofFunctorEquivalence :
    (Cᵒᵖ ⥤ ModuleCat.{a} Λ) ≌ _root_.PresheafOfModules.{a} (constRing (C := C) Λ) where
  functor := ofFunctor Λ
  inverse := toFunctor Λ
  unitIso := (ofFunctorCompToFunctor (C := C) Λ).symm
  counitIso := toFunctorCompOfFunctor (C := C) Λ

/-- The functor `ofFunctor Λ` is an equivalence of categories. -/
instance : (ofFunctor.{a} (C := C) Λ).IsEquivalence :=
  (ofFunctorEquivalence.{a} (C := C) Λ).isEquivalence_functor

/-- The functor `toFunctor Λ` is an equivalence of categories. -/
instance : (toFunctor.{a} (C := C) Λ).IsEquivalence :=
  (ofFunctorEquivalence.{a} (C := C) Λ).isEquivalence_inverse

/-- Reading a `ModuleCat Λ`-valued presheaf as a presheaf of modules over the constant presheaf
of rings is fully faithful. -/
def ofFunctorFullyFaithful : (ofFunctor.{a} (C := C) Λ).FullyFaithful :=
  (ofFunctorEquivalence.{a} (C := C) Λ).fullyFaithfulFunctor

/-- The functor `toFunctor Λ` is additive. -/
instance : (toFunctor.{a} (C := C) Λ).Additive where

/-- The constant sheaf of rings with value `Λ` on the chaotic site: for the bottom topology
every presheaf is a sheaf. -/
def constRingSheaf : Sheaf (⊥ : GrothendieckTopology C) RingCat.{u} :=
  ⟨constRing Λ, Presheaf.isSheaf_bot _⟩

/-- The underlying presheaf of `constRingSheaf Λ` is `constRing Λ`. -/
@[simp]
theorem constRingSheaf_obj : (constRingSheaf (C := C) Λ).obj = constRing Λ := rfl

/-- A `ModuleCat Λ`-valued presheaf, read as a sheaf of modules over the constant sheaf of
rings with value `Λ` on the chaotic site. -/
def ofFunctorSheaf :
    (Cᵒᵖ ⥤ ModuleCat.{a} Λ) ⥤ SheafOfModules.{a} (constRingSheaf (C := C) Λ) where
  obj F := ⟨(ofFunctor Λ).obj F, Presheaf.isSheaf_bot _⟩
  map α := ⟨(ofFunctor Λ).map α⟩

/-- The underlying presheaf of modules of `(ofFunctorSheaf Λ).obj F` is `ofFunctorObj Λ F`. -/
@[simp]
theorem ofFunctorSheaf_obj_val (F : Cᵒᵖ ⥤ ModuleCat.{a} Λ) :
    ((ofFunctorSheaf (C := C) Λ).obj F).val = ofFunctorObj Λ F := rfl

/-- The underlying morphism of `(ofFunctorSheaf Λ).map α` is `(ofFunctor Λ).map α`. -/
@[simp]
theorem ofFunctorSheaf_map_val {F G : Cᵒᵖ ⥤ ModuleCat.{a} Λ} (α : F ⟶ G) :
    ((ofFunctorSheaf (C := C) Λ).map α).val = (ofFunctor Λ).map α := rfl

/-- The functor `ofFunctorSheaf Λ` is additive. -/
instance : (ofFunctorSheaf.{a} (C := C) Λ).Additive where

/-- The functor `ofFunctorSheaf Λ` preserves zero morphisms. -/
instance : (ofFunctorSheaf.{a} (C := C) Λ).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-- The functor `ofFunctor Λ` preserves zero morphisms. -/
instance : (ofFunctor.{a} (C := C) Λ).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-- On the chaotic site every presheaf is a sheaf, so composing a sheaf with any functor gives
a sheaf. -/
instance botHasSheafCompose {A : Type*} [Category A] {B : Type*} [Category B] (G : A ⥤ B) :
    (⊥ : GrothendieckTopology C).HasSheafCompose G :=
  ⟨fun _ _ => Presheaf.isSheaf_bot _⟩

/-- The constant sheaf of commutative rings with value `Λ` on the chaotic site. -/
def constCommRingSheaf (Λ : Type u) [CommRing Λ] :
    Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u} :=
  ⟨(Functor.const Cᵒᵖ).obj (CommRingCat.of Λ), Presheaf.isSheaf_bot _⟩


end Stacks.PresheafOfModules

end
