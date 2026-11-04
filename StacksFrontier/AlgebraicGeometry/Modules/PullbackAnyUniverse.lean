module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackContinuousUnivLE
public import StacksFrontier.CategoryTheory.Sites.LocallyBijectiveUniverse

/-!
# Pullback of sheaves of modules on schemes, with sections in any larger universe

For a morphism of schemes `f : X ⟶ Y` with `X Y : Scheme.{u}`, Mathlib's
`AlgebraicGeometry.Scheme.Modules.pullback f` is the pullback of sheaves of modules whose
sections lie in the universe `u` of the schemes. A sheaf of modules on `X` may have its sections
in a larger universe `max u v` — the sheaf associated to a module whose carrier lies in
`Type v`, say — and the pullback along `f` is then the left adjoint of
`SheafOfModules.pushforward.{max u v} f.toRingCatSheafHom`. This file shows that this left adjoint
exists, so that `SheafOfModules.pullback.{max u v} f.toRingCatSheafHom` is defined, and that when
`f` is an isomorphism the pushforward is an equivalence of categories, so the counit of the
pullback–pushforward adjunction is invertible.

At `v = u` nothing new is defined: `SheafOfModules.pullback.{u} f.toRingCatSheafHom` is
`AlgebraicGeometry.Scheme.Modules.pullback f` by definition.

## Main results

* `AlgebraicGeometry.Scheme.Hom.pushforward_isRightAdjoint_anyUniverse`: the pushforward of
  sheaves of modules with sections in `max u v` along a morphism of schemes has a left adjoint.
* `AlgebraicGeometry.Scheme.Hom.pushforwardEquivalenceOfIsIso`: along an isomorphism, the
  pushforward is an equivalence, with inverse the pushforward along the inverse.
* `AlgebraicGeometry.Scheme.Hom.isIso_pullbackPushforwardAdjunction_counit`: along an
  isomorphism, the counit of the pullback–pushforward adjunction is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

/-- Presheaves of abelian groups with sections in `max u v` on the opens of a scheme in
`Scheme.{u}` admit a sheafification. -/
theorem hasWeakSheafify_opens_anyUniverse (X : Scheme.{u}) :
    HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v} :=
  have : EssentiallySmall.{max u v} (TopologicalSpace.Opens X) := essentiallySmall_lift.{v, u} _
  hasWeakSheafify_addCommGrpCat_of_essentiallySmall.{max u v} _

/-- Sheafification of presheaves of abelian groups with sections in `max u v` on the opens of a
scheme in `Scheme.{u}` inverts exactly the locally bijective morphisms. -/
theorem wEqualsLocallyBijective_opens_anyUniverse (X : Scheme.{u}) :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v} :=
  have : EssentiallySmall.{max u v} (TopologicalSpace.Opens X) := essentiallySmall_lift.{v, u} _
  wEqualsLocallyBijective_addCommGrpCat_of_essentiallySmall.{max u v} _

/-- **The pushforward of sheaves of modules along a morphism of schemes has a left adjoint**,
for sheaves whose sections lie in any universe `max u v` containing that of the schemes. The
left adjoint is the pullback `SheafOfModules.pullback.{max u v} f.toRingCatSheafHom`. -/
instance pushforward_isRightAdjoint_anyUniverse (f : X ⟶ Y) :
    (SheafOfModules.pushforward.{max u v} f.toRingCatSheafHom).IsRightAdjoint :=
  have := hasWeakSheafify_opens_anyUniverse.{u, v} X
  have := wEqualsLocallyBijective_opens_anyUniverse.{u, v} X
  SheafOfModules.pushforward_isRightAdjoint_of_univLE.{max u v} f.toRingCatSheafHom

/-- At the universe of the schemes the pullback is Mathlib's pullback of sheaves of modules on
schemes. -/
theorem pullback_anyUniverse_eq (f : X ⟶ Y) :
    SheafOfModules.pullback.{u} f.toRingCatSheafHom = Scheme.Modules.pullback f :=
  rfl

/-- The pushforward of sheaves of modules along a composite of morphisms of schemes is the
composite of the pushforwards. -/
def pushforwardCompIso {Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    SheafOfModules.pushforward.{max u v} f.toRingCatSheafHom ⋙
        SheafOfModules.pushforward.{max u v} g.toRingCatSheafHom ≅
      SheafOfModules.pushforward.{max u v} (f ≫ g).toRingCatSheafHom :=
  SheafOfModules.pushforwardComp _ _

/-- Pushforwards of sheaves of modules along equal morphisms of schemes are isomorphic. -/
def pushforwardEqIso {f g : X ⟶ Y} (h : f = g) :
    SheafOfModules.pushforward.{max u v} f.toRingCatSheafHom ≅
      SheafOfModules.pushforward.{max u v} g.toRingCatSheafHom :=
  eqToIso (congrArg (fun k : X ⟶ Y ↦ SheafOfModules.pushforward.{max u v} k.toRingCatSheafHom) h)

/-- The pushforward of sheaves of modules along the identity of a scheme is the identity. -/
def pushforwardIdIso (X : Scheme.{u}) :
    SheafOfModules.pushforward.{max u v} (Scheme.Hom.toRingCatSheafHom (𝟙 X)) ≅ 𝟭 _ :=
  SheafOfModules.pushforwardId _

/-- **Along an isomorphism of schemes, the pushforward of sheaves of modules is an equivalence**,
with inverse the pushforward along the inverse isomorphism. -/
def pushforwardEquivalenceOfIsIso (f : X ⟶ Y) [IsIso f] :
    SheafOfModules.{max u v} X.ringCatSheaf ≌ SheafOfModules.{max u v} Y.ringCatSheaf :=
  CategoryTheory.Equivalence.mk (SheafOfModules.pushforward.{max u v} f.toRingCatSheafHom)
    (SheafOfModules.pushforward.{max u v} (inv f).toRingCatSheafHom)
    ((pushforwardIdIso.{u, v} X).symm ≪≫ (pushforwardEqIso.{u, v} (IsIso.hom_inv_id f)).symm ≪≫
      (pushforwardCompIso.{u, v} f (inv f)).symm)
    (pushforwardCompIso.{u, v} (inv f) f ≪≫ pushforwardEqIso.{u, v} (IsIso.inv_hom_id f) ≪≫
      pushforwardIdIso.{u, v} Y)

/-- Along an isomorphism of schemes, the pushforward of sheaves of modules is an equivalence of
categories. -/
instance pushforward_isEquivalence_of_isIso (f : X ⟶ Y) [IsIso f] :
    (SheafOfModules.pushforward.{max u v} f.toRingCatSheafHom).IsEquivalence :=
  (pushforwardEquivalenceOfIsIso.{u, v} f).isEquivalence_functor

/-- **Along an isomorphism of schemes, the counit of the pullback–pushforward adjunction of
sheaves of modules is an isomorphism**, for sections in any universe `max u v`. -/
instance isIso_pullbackPushforwardAdjunction_counit (f : X ⟶ Y) [IsIso f] :
    IsIso (SheafOfModules.pullbackPushforwardAdjunction.{max u v} f.toRingCatSheafHom).counit :=
  inferInstance

end AlgebraicGeometry.Scheme.Hom
