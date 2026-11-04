module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.ClosedQuotient
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionRegular
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionAssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeExactSequence
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerived
public import
  StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedTensorHomMap
public import StacksCore.Tactic.StacksAttribute

/-!
# Derived sheaf Hom along an effective Cartier divisor

Let `X` be a scheme and `D ⊆ X` an effective Cartier divisor, with closed immersion
`i : D ⟶ X`, ideal sheaf `ℐ_D`, associated invertible sheaf `𝒪_X(D) = ℐ_D^∨` and normal sheaf
`𝒩 = i^* 𝒪_X(D)`. [Stacks, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B) asserts that
there is a canonical isomorphism

`R ℰom(𝒪_D, 𝒪_X) = 𝒩[-1]` in `D(𝒪_D)`,

where `R ℰom(𝒪_D, -) : D(𝒪_X) ⥤ D(𝒪_D)` is the right adjoint of derived pushforward of
[Stacks, Tag 0A76] — derived sheaf Hom *with exact support*, not the derived internal Hom on
`X` — and `[-1]` is the cohomological shift that places `𝒩` in degree `1`.

This file constructs the canonical comparison morphism `𝒩[-1] ⟶ R ℰom(𝒪_D, 𝒪_X)` of that
assertion, with a body and no choices, together with the canonical map

`Li^*K ⊗^L_{𝒪_D} 𝒩[-1] ⟶ R ℰom(𝒪_D, K)` in `D(𝒪_D)`

of [Stacks, Tag 0AA4](https://stacks.math.columbia.edu/tag/0AA4) that it feeds: the comparison
morphism tensored with `Li^*K`, followed by the canonical map (48.14.1.1) of
[Stacks, Tag 0B4C]. That the two maps are isomorphisms is
`Stacks.Divisors.isIso_normalSheafShiftToDerivedSheafHomExactSupport` and
`Stacks.Divisors.isIso_normalTensorDerivedSheafHomMap`, proved in files importing this one.

## The canonical map

The source identifies `𝒩` as `i^* 𝒪_X(D)` and `D` as the zero scheme of the canonical section
`1_D` of `𝒪_X(D)`, so the normal short exact sequence

`0 ⟶ 𝒪_X ⟶ 𝒪_X(D) ⟶ i_* 𝒩 ⟶ 0`

is [Stacks, Tag 0C6K] at the regular section `1_D`
(`AlgebraicGeometry.shortExact_zeroScheme_of_isRegularSection`,
`Stacks.Divisors.zeroScheme_canonicalSection`, `Stacks.Divisors.canonicalSection_isRegular`);
this is `Stacks.Divisors.normalShortComplex_shortExact` below.

Its connecting morphism in `D(𝒪_X)` is a morphism `i_* 𝒩 ⟶ 𝒪_X⟦1⟧`, equivalently a morphism
`i_*(𝒩[-1]) ⟶ 𝒪_X`, and the adjunction `Ri_* ⊣ R ℰom(𝒪_D, -)` of [Stacks, Tag 0A76] turns the
latter into `𝒩[-1] ⟶ R ℰom(𝒪_D, 𝒪_X)`. Nothing is chosen along the way: the connecting
morphism of a short exact sequence is Mathlib's `ShortComplex.ShortExact.singleδ`, pushforward
is exact so `Ri_*` is `Functor.mapDerivedCategory`, and the three identifications used to move
`i_*(𝒩[-1])` onto `(i_* 𝒩)⟦-1⟧` are the shift isomorphism of the single functors, the
`CommShift` of `Functor.mapDerivedCategory` and `Functor.mapDerivedCategorySingleFunctor`.

## Main definitions

* `Stacks.Divisors.normalShortComplex`: the short complex `0 ⟶ 𝒪_X ⟶ 𝒪_X(D) ⟶ i_* 𝒩 ⟶ 0`.
* `Stacks.Divisors.normalExtensionClass`: its connecting morphism `i_* 𝒩 ⟶ 𝒪_X⟦1⟧` in
  `D(𝒪_X)`, the canonical class of the extension.
* `Stacks.Divisors.pushforwardNormalShiftToStructureSheaf`: the morphism
  `Ri_*(𝒩[-1]) ⟶ 𝒪_X` obtained from it.
* `Stacks.Divisors.normalShiftToDerivedSheafHomExactSupport`: the canonical comparison
  morphism `(i^* 𝒪_X(D))[-1] ⟶ R ℰom(𝒪_D, 𝒪_X)`, its adjunct.
* `Stacks.Divisors.normalSheafShiftToDerivedSheafHomExactSupport`: the same morphism written
  with the normal sheaf `Stacks.Divisors.normalSheaf` of the closed immersion, through the
  normal-sheaf clause of [Stacks, Tag 0B3P].
* `Stacks.Divisors.normalTensorDerivedPullback`: the functor `K ↦ Li^*K ⊗^L_{𝒪_D} 𝒩[-1]`, the
  source of the formula of [Stacks, Tag 0AA4].
* `Stacks.Divisors.normalTensorDerivedSheafHomMap`: the canonical map
  `Li^*K ⊗^L_{𝒪_D} 𝒩[-1] ⟶ R ℰom(𝒪_D, K)` of [Stacks, Tag 0AA4].

## Main results

* `Stacks.Divisors.normalShortComplex_shortExact`: the normal sequence is short exact.
* `Stacks.Divisors.normalShiftToDerivedSheafHomExactSupport_adjunct`: the comparison morphism
  is the adjunct of `pushforwardNormalShiftToStructureSheaf`, which is what pins it down.
* `Stacks.Divisors.normalTensorDerivedSheafHomMap_mate`: the map of [Stacks, Tag 0AA4] satisfies
  the adjunction equation of [Stacks, Tag 0B4C], which is what pins *it* down.

## Implementation notes

The comparison morphism is *defined* as an adjunct on the `D` side, so a computation on `X` sees
it only through the counit of [Stacks, Tag 0A76]. That counit is the isomorphism of
[Stacks, Tag 0A77] followed by the map `R ℰom_{𝒪_X}(i_* 𝒪_D, K) ⟶ K` induced by the unit
`𝒪_X ⟶ i_* 𝒪_D`, which is the triangle of [Stacks, Tag 0B6M],
`…derivedModulePushforwardDerivedSheafHomExactSupportIso_hom_comp_derivedEvaluationAtOne`. The
source proves that the comparison morphism is an isomorphism by applying `i_*`, which is exact
and fully faithful ([Stacks, Tag 08KS]), and computing `R ℰom_{𝒪_X}(i_* 𝒪_D, 𝒪_X)` from the
ideal sequence `0 ⟶ ℐ_D ⟶ 𝒪_X ⟶ i_* 𝒪_D ⟶ 0` (`Stacks.IdealSheafSequence.divisorIdeal_shortExact`).

## References

* [Stacks Project, Tag 0AA4](https://stacks.math.columbia.edu/tag/0AA4)
* [Stacks Project, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B)
* [Stacks Project, Tag 0B4C](https://stacks.math.columbia.edu/tag/0B4C)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
* [Stacks Project, Tag 0B3P](https://stacks.math.columbia.edu/tag/0B3P)
* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 08I0](https://stacks.math.columbia.edu/tag/08I0)
* [Stacks Project, Tag 0E2K](https://stacks.math.columbia.edu/tag/0E2K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite RingedSpaceModuleAdjunction

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]

/-! ### The normal short exact sequence -/

/-- The normal short complex `0 ⟶ 𝒪_X ⟶ 𝒪_X(D) ⟶ i_*(i^* 𝒪_X(D)) ⟶ 0` of an effective Cartier
divisor: the first map is multiplication by the canonical section `1_D` of `𝒪_X(D)`, the second
the unit of the pullback–pushforward adjunction along the closed immersion of `D`.

It is short exact by `Stacks.Divisors.normalShortComplex_shortExact`. -/
def normalShortComplex : ShortComplex X.Modules :=
  ShortComplex.mk ((divisorSheaf D).unitHomEquiv.symm (canonicalSection' D))
    ((Scheme.Modules.pullbackPushforwardAdjunction D.subschemeι).unit.app (divisorSheaf D))
    (by
      have h := AlgebraicGeometry.section_comp_unit_zeroScheme_eq_zero X (divisorSheaf D)
        (canonicalSection' D)
      rw [zeroScheme_canonicalSection D] at h
      exact h)

/-- **The normal short exact sequence of an effective Cartier divisor,**
`0 ⟶ 𝒪_X ⟶ 𝒪_X(D) ⟶ i_*(i^* 𝒪_X(D)) ⟶ 0`.

`D` is the zero scheme of the canonical section `1_D` of `𝒪_X(D)`
(`Stacks.Divisors.zeroScheme_canonicalSection`) and `1_D` is a regular section
(`Stacks.Divisors.canonicalSection_isRegular`, [Stacks, Tag 01X0]), so this is the second
assertion of [Stacks, Tag 0C6K] at `1_D`. -/
theorem normalShortComplex_shortExact : (normalShortComplex D).ShortExact := by
  have h := AlgebraicGeometry.shortExact_zeroScheme_of_isRegularSection X (divisorSheaf D)
    (canonicalSection' D) (canonicalSection_isRegular D)
  rw [zeroScheme_canonicalSection D] at h
  exact h.2

/-- The canonical class of the normal extension: the connecting morphism
`i_*(i^* 𝒪_X(D)) ⟶ 𝒪_X⟦1⟧` in `D(𝒪_X)` of the normal short exact sequence. -/
def normalExtensionClass :
    (DerivedCategory.singleFunctor X.Modules 0).obj (normalShortComplex D).X₃ ⟶
      ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X))⟦(1 : ℤ)⟧ :=
  (normalShortComplex_shortExact D).singleδ

/-! ### The canonical comparison morphism of Tag 0B4B -/

/-- The closed immersion of an effective Cartier divisor, bundled as a closed quotient
morphism of ringed spaces, which is the form the adjunction of [Stacks, Tag 0A76] consumes.
This is `Stacks.ClosedImmersion.closedQuotientOfClosedImmersion` at `D.subschemeι`. -/
abbrev closedQuotient : ClosedQuotientMorphismOfRingedSpaces.{u} :=
  Stacks.ClosedImmersion.closedQuotientOfClosedImmersion D.subschemeι

/-- The morphism `Ri_*(𝒩[-1]) ⟶ 𝒪_X` in `D(𝒪_X)` determined by the normal extension class,
where `𝒩 = i^* 𝒪_X(D)`.

Derived pushforward along the closed immersion commutes with the shift and carries a single
complex to a single complex, so `Ri_*(𝒩[-1])` is `(i_* 𝒩)⟦-1⟧`; the morphism is the shift by
`-1` of `Stacks.Divisors.normalExtensionClass`, read through those two identifications and the
identification of `𝒩[-1]` with `𝒩⟦-1⟧`. -/
def pushforwardNormalShiftToStructureSheaf :
    (modulePushforward (closedQuotient D).i).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor D.subscheme.Modules 1).obj
          ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D))) ⟶
      (DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X) :=
  (modulePushforward (closedQuotient D).i).mapDerivedCategory.map
      (((DerivedCategory.singleFunctors D.subscheme.Modules).shiftIso (-1) 1 0
        (by ring)).inv.app ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D))) ≫
    ((modulePushforward (closedQuotient D).i).mapDerivedCategory.commShiftIso (-1 : ℤ)).hom.app
      ((DerivedCategory.singleFunctor D.subscheme.Modules 0).obj
        ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D))) ≫
    ((((modulePushforward (closedQuotient D).i).mapDerivedCategorySingleFunctor 0).hom.app
      ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D)))⟦(-1 : ℤ)⟧') ≫
    ((normalExtensionClass D)⟦(-1 : ℤ)⟧') ≫
    (shiftFunctorCompIsoId (DerivedCategory X.Modules) (1 : ℤ) (-1) (by ring)).hom.app
      ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X))

/-- **The canonical comparison morphism of [Stacks, Tag 0B4B]**, at the description
`𝒩 = i^* 𝒪_X(D)` of the normal sheaf:

`(i^* 𝒪_X(D))[-1] ⟶ R ℰom(𝒪_D, 𝒪_X)` in `D(𝒪_D)`.

It is the adjunct of `Stacks.Divisors.pushforwardNormalShiftToStructureSheaf` under the
adjunction `Ri_* ⊣ R ℰom(𝒪_D, -)` of [Stacks, Tag 0A76], so it is determined by the canonical
class of the normal extension and nothing is chosen. [Stacks, Tag 0B4B] asserts that it is an
isomorphism; at the normal sheaf of the closed immersion that is
`Stacks.Divisors.isIso_normalSheafShiftToDerivedSheafHomExactSupport`. -/
def normalShiftToDerivedSheafHomExactSupport :
    (DerivedCategory.singleFunctor D.subscheme.Modules 1).obj
        ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D)) ⟶
      (closedQuotient D).derivedSheafHomExactSupport.obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X)) :=
  ((closedQuotient D).derivedModulePushforwardSheafHomExactSupportAdjunction.homEquiv _ _)
    (pushforwardNormalShiftToStructureSheaf D)

/-- The comparison morphism of [Stacks, Tag 0B4B] is the adjunct of the morphism determined by
the normal extension class. This is what pins it down. -/
theorem normalShiftToDerivedSheafHomExactSupport_adjunct :
    ((closedQuotient D).derivedModulePushforwardSheafHomExactSupportAdjunction.homEquiv _ _).symm
        (normalShiftToDerivedSheafHomExactSupport D) =
      pushforwardNormalShiftToStructureSheaf D :=
  Equiv.symm_apply_apply _ _

/-- **[Stacks, Tag 0B4B], the canonical comparison morphism** written with the normal sheaf
`𝒩_{D/X}` of the closed immersion of `D`, the dual of its conormal sheaf:

`𝒩_{D/X}[-1] ⟶ R ℰom(𝒪_D, 𝒪_X)` in `D(𝒪_D)`.

This is `Stacks.Divisors.normalShiftToDerivedSheafHomExactSupport` precomposed with the
normal-sheaf clause of [Stacks, Tag 0B3P]
(`Stacks.Divisors.normalSheafIsoInvertibleSheaf`), which identifies `𝒩_{D/X}` with
`i^* 𝒪_X(D)` — the description of `𝒩` that the section fixes before stating the lemma.

[Stacks, Tag 0B4B] asserts that this morphism is an isomorphism; that is
`Stacks.Divisors.isIso_normalSheafShiftToDerivedSheafHomExactSupport`. -/
def normalSheafShiftToDerivedSheafHomExactSupport :
    (DerivedCategory.singleFunctor D.subscheme.Modules 1).obj (normalSheaf D.subschemeι) ⟶
      (closedQuotient D).derivedSheafHomExactSupport.obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X)) :=
  (DerivedCategory.singleFunctor D.subscheme.Modules 1).map
      (normalSheafIsoInvertibleSheaf D).hom ≫
    normalShiftToDerivedSheafHomExactSupport D

/-! ### The normal-sheaf formula for derived sheaf Hom -/

/-- The source of the formula of [Stacks, Tag 0AA4], as a functor `D(𝒪_X) ⥤ D(𝒪_D)`:

`K ↦ Li^*K ⊗^L_{𝒪_D} 𝒩[-1]`,

with the tensor factors in the order of the source's display. It is the functor
`RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.derivedPullbackTensorSheafHom`
of [Stacks, Tag 0B4C] with `R ℰom(𝒪_D, 𝒪_X)` replaced by the shifted normal sheaf. -/
abbrev normalTensorDerivedPullback :
    DerivedCategory X.Modules ⥤ DerivedCategory D.subscheme.Modules :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback (closedQuotient D).i ⋙
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        (closedQuotient D).Z.sheaf).flip.obj
      ((DerivedCategory.singleFunctor D.subscheme.Modules 1).obj (normalSheaf D.subschemeι))

/-- **[Stacks, Tag 0AA4], the canonical map**

`Li^*K ⊗^L_{𝒪_D} 𝒩[-1] ⟶ R ℰom(𝒪_D, K)` in `D(𝒪_D)`,

for `K` in `D(𝒪_X)`: the canonical map (48.14.1.1) of [Stacks, Tag 0B4C] precomposed with the
comparison morphism `𝒩[-1] ⟶ R ℰom(𝒪_D, 𝒪_X)` of [Stacks, Tag 0B4B] tensored with `Li^*K`.
This is the composite the source forms; that it is an isomorphism is
`Stacks.Divisors.isIso_normalTensorDerivedSheafHomMap`, and that it is natural in `K` is
`Stacks.Divisors.normalTensorDerivedSheafHomMap_natural`. -/
@[stacks 0AA4 "the canonical map Li^*K ⊗ᴸ 𝒩[-1] ⟶ R ℰom(𝒪_D, K) only, unconditionally; that \
the map is an isomorphism is not proved, since that needs the isomorphism assertion of Tag 0B4B, \
which this file states only as a map, and functoriality in K is not proved either"]
def normalTensorDerivedSheafHomMap
    (K : DerivedCategory X.Modules) :
    (normalTensorDerivedPullback D).obj K ⟶
      (closedQuotient D).derivedSheafHomExactSupport.obj K :=
  ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        (closedQuotient D).Z.sheaf).flip.map
      (normalSheafShiftToDerivedSheafHomExactSupport D)).app
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (closedQuotient D).i).obj K) ≫
    (closedQuotient D).derivedPullbackTensorSheafHomMap K

/-- The map of [Stacks, Tag 0AA4] is pinned down by the adjunction equation of
[Stacks, Tag 0B4C]: pushing it forward and composing with the counit of [Stacks, Tag 0A76]
gives the displayed composite of that tag, precomposed with the comparison morphism of
[Stacks, Tag 0B4B] tensored with `Li^*K`. -/
theorem normalTensorDerivedSheafHomMap_mate
    (K : DerivedCategory X.Modules) :
    (modulePushforward (closedQuotient D).i).mapDerivedCategory.map
          (normalTensorDerivedSheafHomMap D K) ≫
        (closedQuotient D).derivedSheafHomAdjunction.counit.app K =
      (modulePushforward (closedQuotient D).i).mapDerivedCategory.map
          (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
                (closedQuotient D).Z.sheaf).flip.map
              (normalSheafShiftToDerivedSheafHomExactSupport D)).app
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
              (closedQuotient D).i).obj K)) ≫
        (closedQuotient D).derivedPullbackTensorSheafHomMateMap K := by
  rw [normalTensorDerivedSheafHomMap]
  exact ((congrArg (fun t => t ≫ (closedQuotient D).derivedSheafHomAdjunction.counit.app K)
        ((modulePushforward (closedQuotient D).i).mapDerivedCategory.map_comp _ _)).trans
      (Category.assoc _ _ _)).trans
    (congrArg (fun t => (modulePushforward (closedQuotient D).i).mapDerivedCategory.map
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
                (closedQuotient D).Z.sheaf).flip.map
              (normalSheafShiftToDerivedSheafHomExactSupport D)).app
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            (closedQuotient D).i).obj K)) ≫ t)
      ((closedQuotient D).derivedPullbackTensorSheafHomMap_mate K))

end Stacks.Divisors

end
