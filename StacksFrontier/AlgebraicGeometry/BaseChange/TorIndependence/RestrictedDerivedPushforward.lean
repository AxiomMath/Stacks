module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedBaseChangeGlobal

/-!
# The derived pushforward of a restriction, and the vertices of the relative Mayer–Vietoris
triangle

Let `f : X ⟶ Y` be a morphism of ringed spaces and let `i : W ⟶ X` be an open immersion.  The
underived functor "restrict along `i`, then push forward along `i ≫ f`" is
`Stacks.Cohomology.RelativeMayerVietoris.restrictedPushforwardAlong f i`, and its chosen total
right derived functor on the unbounded derived category is what the relative Mayer–Vietoris
triangle of Stacks 08HZ has at its vertices — in the form
`Stacks.Cohomology.DerivedBaseChange.openDerivedPushforward f U`, for `U` an open subset of `X`.

This module identifies that vertex with a composite of the derived functors the base-change map is
built from:

`R(f|_U)_*((-)|_U)  ≅  Li^* ⋙ R(i ≫ f)_*  ≅  Li^* ⋙ Ri_* ⋙ Rf_*`

where `i` is the inclusion of the open subspace cut out by `U`.  This is the form in which the
vertices enter the cover step of Stacks 0DJ9, which is stated for a natural transformation of
functors on `D(𝒪_X)`.

Both sides are right derived functors of "restrict, then push forward": the right-hand side
because restriction along an open immersion carries K-injective complexes to K-injective
complexes (`Stacks.Cohomology.openImmersionModulePullback_preservesKInjective`, one of the two
exactness inputs of Stacks 08FE).

## Main definitions

All in the namespace `Stacks.Cohomology.DerivedBaseChange`.

* `derivedRestrictPushforwardUnit` — the unit exhibiting `Li^* ⋙ R(i ≫ f)_*` as a right derived
  functor of `restrictedPushforwardAlong f i`.
* `restrictedPushforwardAlongHomotopyIso` — the comparison between the two spellings of the
  underived composite on the homotopy category: applied degreewise as one functor, or as the
  composite of the two degreewise functors.

## Main results

* `derivedRestrictPushforward_isRightDerivedFunctor` — `Li^* ⋙ R(i ≫ f)_*` is a right derived
  functor of `restrictedPushforwardAlong f i`.
* `openDerivedPushforwardIso` — **the identification of the Mayer–Vietoris vertex**:
  `openDerivedPushforward f U ≅ Li^* ⋙ R(i ≫ f)_*` for `i` the inclusion of the open subspace
  cut out by `U`.
* `openDerivedPushforwardIsoComp` — the same with `R(i ≫ f)_*` broken up by the composition
  isomorphism of Stacks 079W: `R(f|_U)_*(K|_U) ≅ Rf_*(Ri_*(K|_U))`.

## Implementation notes

The statements are made for an arbitrary open immersion `i : W ⟶ X` of ringed spaces, and only
`openDerivedPushforwardIso` specialises to the inclusion of the open subspace cut out by an open
subset; instance search does not find `SheafedSpace.IsOpenImmersion (openSubspaceInclusion X U)`,
so that instance is supplied there by hand.

`Functor.mapHomotopyCategory` of a composite of additive functors is not definitionally the
composite of the two `mapHomotopyCategory`s — it is built through `CategoryTheory.Quotient.lift` —
so the unit of `Stacks.Cohomology.composite_isRightDerivedFunctor` lives on the second spelling
while `openDerivedPushforwardUnit` lives on the first; `restrictedPushforwardAlongHomotopyIso`
passes between them.  The two types are convertible at default transparency but not at the
`instances` transparency `apply` uses, which is why the composition lemma is applied in term mode.

Everything is at `CategoryTheory.HasDerivedCategory.standard`, installed as a file-local instance,
because the derived-functor instances of
`Stacks.Cohomology.DerivedBaseChange.openDerivedPushforward` are found only there.  Nothing is
stated at the locally small model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`.

## References

* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
* [Stacks Project, Tag 08HZ](https://stacks.math.columbia.edu/tag/08HZ)
* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.RelativeMayerVietoris

universe u

namespace Stacks.Cohomology.DerivedBaseChange

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] pullbackOnHomotopy_hasRightDerivedFunctor
  openImmersionDerivedPullback_isRightDerivedFunctor restrictedPushforward_hasRightDerivedFunctor

/-! ### The composite `Li^* ⋙ R(i ≫ f)_*` as a right derived functor -/

section Along

variable {X Y W : RingedSpace.{u, u}} (f : X ⟶ Y) (i : W ⟶ X)
  [SheafedSpace.IsOpenImmersion i]

/-- The unit exhibiting `Li^* ⋙ R(i ≫ f)_*` as a right derived functor of "restrict along `i`,
then push forward along `i ≫ f`": the unit of the chosen derived pushforward along `i ≫ f`,
whiskered by degreewise restriction, followed by the unit of
`openImmersionDerivedPullback_isRightDerivedFunctor`, whiskered by the derived pushforward. -/
def derivedRestrictPushforwardUnit :
    ((modulePullback i).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (modulePushforward (i ≫ f)).mapHomotopyCategory (ComplexShape.up ℤ)) ⋙
      DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (derivedPullback i ⋙ derivedPushforward (i ≫ f)) :=
  Functor.whiskerLeft ((modulePullback i).mapHomotopyCategory (ComplexShape.up ℤ))
      (derivedPushforwardUnit (i ≫ f)) ≫
    Functor.whiskerRight (openImmersionDerivedPullbackUnit i) (derivedPushforward (i ≫ f))

/-- **Restriction to an open subspace followed by derived pushforward is a right derived functor
of restriction followed by pushforward**, with unit `derivedRestrictPushforwardUnit f i`.  The
input is that restriction along an open immersion carries a K-injective complex to a K-injective
complex, as in Stacks 08FE. -/
theorem derivedRestrictPushforward_isRightDerivedFunctor :
    (derivedPullback i ⋙ derivedPushforward (i ≫ f)).IsRightDerivedFunctor
      (derivedRestrictPushforwardUnit f i)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)) :=
  have hG : ∀ I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ, I.IsKInjective →
      IsIso ((derivedPushforwardUnit (i ≫ f)).app
        (((modulePullback i).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
            (ComplexShape.up ℤ)).obj I))) := fun K _ =>
    isIso_derivedPushforwardUnit_app_of_isKInjective (i ≫ f)
      (((modulePullback i).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
      (Stacks.Cohomology.openImmersionModulePullback_preservesKInjective i K)
  Stacks.Cohomology.composite_isRightDerivedFunctor
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective X)
    (modulePullback i) (modulePushforward (i ≫ f)) (derivedPullback i)
    (derivedPushforward (i ≫ f)) (openImmersionDerivedPullbackUnit i)
    (derivedPushforwardUnit (i ≫ f)) hG

/-- The two spellings of the underived composite on the homotopy category: applying
`restrictedPushforwardAlong f i` degreewise, or applying degreewise restriction and then
degreewise pushforward.  The two functors are isomorphic but not definitionally equal, since
`CategoryTheory.Functor.mapHomotopyCategory` of a composite is built through
`CategoryTheory.Quotient.lift`. -/
def restrictedPushforwardAlongHomotopyIso :
    homotopyToDerived (restrictedPushforwardAlong f i) ≅
      ((modulePullback i).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (modulePushforward (i ≫ f)).mapHomotopyCategory (ComplexShape.up ℤ)) ⋙
        DerivedCategory.Qh :=
  Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso
    (Iso.refl (modulePullback i ⋙ modulePushforward (i ≫ f))) (ComplexShape.up ℤ)).symm
      DerivedCategory.Qh

end Along

/-! ### The vertices of the relative Mayer–Vietoris triangle -/

section Vertices

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (U : Opens X)

/-- **The identification of the vertices of the relative Mayer–Vietoris triangle.**  The chosen
derived pushforward of the restriction of `f` to an open `U` of its source — the functor
`Stacks.Cohomology.DerivedBaseChange.openDerivedPushforward` appearing at the vertices of
`exists_canonicalRelativeMayerVietorisTriangle` — is the composite of the canonical derived
restriction to the open subspace cut out by `U` with the canonical derived pushforward along the
restriction of `f`:

`R(f|_U)_*((-)|_U)  ≅  Li^* ⋙ R(i ≫ f)_*`.

The right-hand side is a composite of the derived functors from which the base-change map of
Stacks 08HY is built, as in the cover step of Stacks 0DJ9
(`isIso_derivedBaseChangeNatTrans_app_of_distTriang`). -/
def openDerivedPushforwardIso :
    openDerivedPushforward f U ≅
      derivedPullback (openSubspaceInclusion X U) ⋙
        derivedPushforward (openSubspaceInclusion X U ≫ f) :=
  letI : SheafedSpace.IsOpenImmersion (openSubspaceInclusion X U) :=
    SheafedSpace.IsOpenImmersion.ofRestrict X U.isOpenEmbedding
  haveI := derivedRestrictPushforward_isRightDerivedFunctor f (openSubspaceInclusion X U)
  Functor.rightDerivedNatIso (openDerivedPushforward f U) _
    (openDerivedPushforwardUnit f U)
    (derivedRestrictPushforwardUnit f (openSubspaceInclusion X U))
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    (restrictedPushforwardAlongHomotopyIso f (openSubspaceInclusion X U))

/-- `openDerivedPushforwardIso` with the derived pushforward along `i ≫ f` broken up by the
composition isomorphism of Stacks 079W, in the shape of the cover step of Stacks 0DJ9:

`R(f|_U)_*(K|_U)  ≅  Rf_*(Ri_*(K|_U))`. -/
def openDerivedPushforwardIsoComp :
    openDerivedPushforward f U ≅
      derivedPullback (openSubspaceInclusion X U) ⋙
        (derivedPushforward (openSubspaceInclusion X U) ⋙ derivedPushforward f) :=
  openDerivedPushforwardIso f U ≪≫
    Functor.isoWhiskerLeft (derivedPullback (openSubspaceInclusion X U))
      (derivedPushforwardCompIso (openSubspaceInclusion X U) f).symm

end Vertices

end Stacks.Cohomology.DerivedBaseChange

end
