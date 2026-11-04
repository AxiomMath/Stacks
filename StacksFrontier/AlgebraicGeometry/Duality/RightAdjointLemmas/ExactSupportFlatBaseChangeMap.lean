module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportFlatBaseChange
import all StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportFlatBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.ClosedImmersionBaseChangeMergeCoherence
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.ClosedQuotient
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportBaseChangeDerived
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedPushforwardConservative
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedTensorHomMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.PseudoCoherent

/-!
# Base change for sheaf Hom with exact support along a flat morphism

Consider a cartesian diagram of schemes

```
Z' --i'--> X'
|g         |f
Z --i----> X
```

in which `i` is a closed immersion and `Z`, `X'` are Tor independent over `X`. Then `i'` is a
closed immersion too, both `i` and `i'` present their sources as closed quotients of ringed
spaces, and the right adjoint `R ℰom(𝒪_Z, -)` of [Stacks, Tag 0A76] is available on both. The
section of the source opened by [Stacks, Tag 0E2J] attaches to this situation a canonical map

`Lg^* R ℰom(𝒪_Z, K) ⟶ R ℰom(𝒪_{Z'}, Lf^*K)`

in `D(𝒪_{Z'})`, functorial in `K`; that map is [Stacks, Tag 0E2K], and
`baseChangeSheafHomExactSupportMap` below is it, as a morphism of functors of `K`.
[Stacks, Tag 0E2M] asserts that it is invertible when `f` is flat, `i` is pseudo-coherent and
`K` lies in `D⁺_QCoh(𝒪_X)`; that is proved in
`StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportFlatBaseChangeIso`.

## Main definitions

* `closedQuotientOfBaseChange` presents the base change `i'` of the closed immersion as a
  closed quotient morphism of ringed spaces, so that the right adjoint of [Stacks, Tag 0A76] is
  available on the left-hand column of the square.
* `pushforwardBaseChangeIso` is the identification `Ri'_* ∘ Lg^* ≅ Lf^* ∘ Ri_*` of
  [Stacks, Tag 0E23], read in the model of pushforward the adjunction of [Stacks, Tag 0A76] is
  stated for; it is the one place the square and the Tor independence enter.
* `baseChangeSheafHomExactSupportMap` is the map of [Stacks, Tag 0E2K], functorial in `K`.

## Main results

* `baseChangeSheafHomExactSupportMap_app` spells out the component at `K` as the source builds it.
* `isIso_baseChangeSheafHomExactSupportMap_app_iff`: the map of [Stacks, Tag 0E2K] is an
  isomorphism exactly when the map
  `Lf^* R SheafHom_{𝒪_X}(𝒪_Z, K) ⟶ R SheafHom_{𝒪_{X'}}(𝒪_{Z'}, Lf^*K)`
  read off its pushforward along `i'` is — the source's reduction of [Stacks, Tag 0E2L]; the tag,
  with the map of [Stacks, Tag 08I3], is
  `isIso_baseChangeSheafHomExactSupportMap_app_iff_isIso_derivedPullbackSheafHomMap` in
  `StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportBaseChangeInternalHom`.
* `isIso_of_isIso_modulePushforward_map` is the step "since `i'_*` is exact and faithful it
  suffices to show the map is an isomorphism after applying `Ri'_*`" of the source's proof of
  [Stacks, Tag 0E2L], read off the conservativity of derived pushforward along a closed
  quotient morphism.

## Implementation notes

**How the map is built.** The source constructs the map of [Stacks, Tag 0E2K] by adjointness:
under `Ri'_* ⊣ R ℰom(𝒪_{Z'}, -)` of [Stacks, Tag 0A76] on the left column, a map
`Lg^* R ℰom(𝒪_Z, K) ⟶ R ℰom(𝒪_{Z'}, Lf^*K)` is the same thing as a map
`Ri'_* Lg^* R ℰom(𝒪_Z, K) ⟶ Lf^*K`; Tor independence turns `Ri'_* ∘ Lg^*` into `Lf^* ∘ Ri_*`,
and then `Lf^*` of the counit `Ri_* R ℰom(𝒪_Z, K) ⟶ K` does it. The general construction, for an
arbitrary identification `Ri'_* ∘ Lg^* ≅ Lf^* ∘ Ri_*`, is
`RingedSpaceModuleAdjunction.ClosedQuotientBaseChange.rightAdjointBaseChange`; the map of the tag
is that construction at `pushforwardBaseChangeIso`, and `baseChangeSheafHomExactSupportMap_app`
unfolds it to the composite above.

**The two models of pushforward.** The adjunction of [Stacks, Tag 0A76] has the functor induced
on derived categories by the exact functor `i_*` as its left adjoint, while the base-change map
of [Stacks, Tag 08HY] is stated for the total right derived functor `Ri_*`. The composite
passes through `derivedPushforwardComparison`, the identification of the two models, in both
directions — once on each column of the square.

**Hypotheses.** The map is stated at exactly the hypotheses of the source: a cartesian square
`sq` with `i` a closed immersion, and `Z`, `X'` Tor independent over `X`. That `i'` is a closed
immersion is derived from `sq`, not assumed. [Stacks, Tag 0E23] enters through the unconditional
`Stacks.Cohomology.ClosedImmersionBaseChange.derivedBaseChangeSquareIso`.

## References

* [Stacks Project, Tag 0E2J](https://stacks.math.columbia.edu/tag/0E2J)
* [Stacks Project, Tag 0E2K](https://stacks.math.columbia.edu/tag/0E2K)
* [Stacks Project, Tag 0E2L](https://stacks.math.columbia.edu/tag/0E2L)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedBaseChange
open Stacks.Cohomology.ClosedImmersionBaseChange
open Stacks.ClosedImmersion

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Duality.ExactSupportBaseChange

/-! ### Conservativity of pushforward along a closed quotient morphism -/

/-! ### The situation of Stacks 0E2J -/

variable {Z' X' Z X : Scheme.{u}} {i' : Z' ⟶ X'} {g : Z' ⟶ Z} {f : X' ⟶ X} {i : Z ⟶ X}

/-- **[Stacks, Tag 0E23], in the model of pushforward of [Stacks, Tag 0A76].** For a cartesian
square with `i` a closed immersion and `Z`, `X'` Tor independent over `X`, the identification
`Ri'_* ∘ Lg^* ≅ Lf^* ∘ Ri_*` of functors `D(𝒪_Z) ⥤ D(𝒪_{X'})`.

It is the inverse of the Tor-independent base-change isomorphism
`Stacks.Cohomology.ClosedImmersionBaseChange.derivedBaseChangeSquareIso`, conjugated on both legs
by `derivedPushforwardComparison`, which passes between the functor induced by the exact
functor `i_*` (the left adjoint of [Stacks, Tag 0A76]) and the total right derived functor `Ri_*`
(the one [Stacks, Tag 0E23] is stated for). -/
def pushforwardBaseChangeIso (sq : IsPullback i' g f i) [IsClosedImmersion i]
    (htor : AlgebraicGeometry.TorIndependent i f) :
    derivedPullback g.toLRSHom.toShHom ⋙
        (modulePushforward (closedQuotientOfBaseChange sq).i).mapDerivedCategory ≅
      (modulePushforward (closedQuotientOfClosedImmersion i).i).mapDerivedCategory ⋙
        derivedPullback f.toLRSHom.toShHom :=
  Functor.isoWhiskerLeft _ (closedQuotientOfBaseChange sq).derivedPushforwardComparison ≪≫
    (derivedBaseChangeSquareIso sq htor).symm ≪≫
    Functor.isoWhiskerRight (closedQuotientOfClosedImmersion i).derivedPushforwardComparison.symm _

/-! ### The base-change map of Stacks 0E2K -/

/-- **Stacks Project, Tag 0E2K.** The canonical base-change map

`Lg^* R ℰom(𝒪_Z, K) ⟶ R ℰom(𝒪_{Z'}, Lf^*K)`

in `D(𝒪_{Z'})`, functorial in `K ∈ D(𝒪_X)`, for a cartesian square whose right-hand column `i`
is a closed immersion and whose corners `Z`, `X'` are Tor independent over `X`.

Its component at `K` corresponds, under the adjunction `Ri'_* ⊣ R ℰom(𝒪_{Z'}, -)` of
[Stacks, Tag 0A76] on the left-hand column, to the composite

`Ri'_* Lg^* R ℰom(𝒪_Z, K) = Lf^* Ri_* R ℰom(𝒪_Z, K) ⟶ Lf^*K`

whose equality is the Tor-independent base-change isomorphism of [Stacks, Tag 0E23]
(`pushforwardBaseChangeIso`), and whose arrow is `Lf^*` of the counit of [Stacks, Tag 0A76];
`baseChangeSheafHomExactSupportMap_app` spells this out. -/
@[stacks 0E2K "the canonical base-change map, functorial in K"]
def baseChangeSheafHomExactSupportMap (sq : IsPullback i' g f i) [IsClosedImmersion i]
    (htor : AlgebraicGeometry.TorIndependent i f) :
    (closedQuotientOfClosedImmersion i).derivedSheafHomExactSupport ⋙
        derivedPullback g.toLRSHom.toShHom ⟶
      derivedPullback f.toLRSHom.toShHom ⋙
        (closedQuotientOfBaseChange sq).derivedSheafHomExactSupport :=
  ClosedQuotientBaseChange.rightAdjointBaseChange (closedQuotientOfClosedImmersion i)
    (closedQuotientOfBaseChange sq) (derivedPullback f.toLRSHom.toShHom)
    (derivedPullback g.toLRSHom.toShHom) (pushforwardBaseChangeIso sq htor)

/-- The component at `K` of the map of [Stacks, Tag 0E2K], as the source constructs it: the
transpose under `Ri'_* ⊣ R ℰom(𝒪_{Z'}, -)` of the inverse of the Tor-independent base-change
isomorphism of [Stacks, Tag 0E23] at `R ℰom(𝒪_Z, K)` — whose forward map is, by definition, the
derived base-change map of [Stacks, Tag 08HY] there — followed by `Lf^*` of the counit
`Ri_* R ℰom(𝒪_Z, K) ⟶ K`, with `derivedPushforwardComparison` passing between the two models of
pushforward on each column. -/
theorem baseChangeSheafHomExactSupportMap_app (sq : IsPullback i' g f i) [IsClosedImmersion i]
    (htor : AlgebraicGeometry.TorIndependent i f)
    (K : DerivedCategory
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    (baseChangeSheafHomExactSupportMap sq htor).app K =
      ((closedQuotientOfBaseChange sq).derivedSheafHomAdjunction.homEquiv _ _)
        (((closedQuotientOfBaseChange sq).derivedPushforwardComparison.hom.app _ ≫
          (derivedBaseChangeSquareIso sq htor).inv.app _ ≫
          (derivedPullback f.toLRSHom.toShHom).map
            ((closedQuotientOfClosedImmersion i).derivedPushforwardComparison.inv.app _)) ≫
          (derivedPullback f.toLRSHom.toShHom).map
            ((closedQuotientOfClosedImmersion i).derivedSheafHomAdjunction.counit.app K)) :=
  rfl

/-! ### Stacks 0E2L, after pushforward along `i'` -/

/-- **The map of [Stacks, Tag 0E2K] is an isomorphism exactly when its pushforward is.** In the
situation of [Stacks, Tag 0E2J] — a cartesian square whose right-hand column `i` is a closed
immersion, with `Z` and `X'` Tor independent over `X` — the map
`Lg^* R ℰom(𝒪_Z, K) ⟶ R ℰom(𝒪_{Z'}, Lf^*K)` of [Stacks, Tag 0E2K] is an isomorphism if and only if
the map

`Lf^* R SheafHom_{𝒪_X}(𝒪_Z, K) ⟶ R SheafHom_{𝒪_{X'}}(𝒪_{Z'}, Lf^*K)`

obtained from it is one: its pushforward along `i'`, read through the identification
`Ri'_* ∘ Lg^* ≅ Lf^* ∘ Ri_*` of [Stacks, Tag 0E23] (`pushforwardBaseChangeIso`) and the two
identifications of [Stacks, Tag 0A77]. Both directions: `Ri'_*` carries isomorphisms to
isomorphisms, and it reflects them, `i'_*` being exact and faithful.

The hypotheses are exactly the source's; nothing is carried. This is the source's reduction of
[Stacks, Tag 0E2L] to `Ri'_*`; the tag itself, with the base change map of Cohomology,
Remark [Stacks, Tag 08I3], is
`isIso_baseChangeSheafHomExactSupportMap_app_iff_isIso_derivedPullbackSheafHomMap`. -/
theorem isIso_baseChangeSheafHomExactSupportMap_app_iff (sq : IsPullback i' g f i)
    [IsClosedImmersion i] (htor : AlgebraicGeometry.TorIndependent i f)
    (K : DerivedCategory
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    IsIso ((baseChangeSheafHomExactSupportMap sq htor).app K) ↔
      IsIso (ClosedQuotientBaseChange.derivedSheafHomBaseChangeMap
        (closedQuotientOfClosedImmersion i) (closedQuotientOfBaseChange sq)
        (derivedPullback f.toLRSHom.toShHom) (derivedPullback g.toLRSHom.toShHom)
        (pushforwardBaseChangeIso sq htor) K) :=
  ClosedQuotientBaseChange.isIso_rightAdjointBaseChangeMap_iff
    (closedQuotientOfClosedImmersion i) (closedQuotientOfBaseChange sq)
    (derivedPullback f.toLRSHom.toShHom) (derivedPullback g.toLRSHom.toShHom)
    (pushforwardBaseChangeIso sq htor) K

end Stacks.Duality.ExactSupportBaseChange

end
