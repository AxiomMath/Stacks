module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorChartRatioFlatDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicChartHartogsGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionIntegralChartTrivialization
public import StacksFrontier.AlgebraicGeometry.Spaces.Normal

/-!
# The geometric claim of Stacks 0EPX

Let `X` be a normal, locally Noetherian, integral, decent algebraic space over a scheme `S`, let
`ℒ` be an invertible `𝒪_X`-module and let `t` be a regular meromorphic section of `ℒ`. If the
canonical ratio of `t` at the generic point of **every** prime divisor of `X` is the image of a
unit of the henselian local ring there, then `t` trivializes `ℒ`: its Picard class is zero.

That is the claim the source of Stacks 0EPX makes and calls the whole content of the lemma, and
it is proved here. Nothing is left as a hypothesis beyond the source's own.

## How it is assembled

The covering family of étale charts that are affine, integral and carry a free generator of `ℒ`
reduces the claim to one chart
(`AlgebraicGeometry.Space.picardClass_eq_zero_of_generatesOnChart_isAffine_isIntegral`). Over
such a chart `V` the section generates `ℒ` as soon as its ratio `t / e` against the free
generator, read as a rational function of `chartScheme V`, is nonzero and has order of vanishing
zero at every coheight-one point of that scheme — algebraic Hartogs,
`AlgebraicGeometry.Space.generatesOnChart_of_forall_ord_eq_zero`. The nonvanishing is regularity
of `t` (`AlgebraicGeometry.Space.chartRatio_ne_zero_of_isRegularMeromorphicSection`), and the
vanishing of the order is step three of the flat-descent route,
`AlgebraicGeometry.Space.ord_chartRatio_eq_zero_of_forall_isUnit_canonicalGenericRatio`.

The three instance hypotheses the chart must satisfy beyond the two the covering family provides
hold of *every* chart: local Noetherianness is
`AlgebraicGeometry.Space.isLocallyNoetherian_chartScheme` and normality is
`AlgebraicGeometry.Space.isNormal_iff_forall_etale` read at the chart — the direct producer
`AlgebraicGeometry.Space.isNormal_chartScheme` being `private` to its module. The two conditions
of Stacks 0EN6, part (2), which identify the meromorphic functions of an integral affine chart
with the function field of its scheme, are conclusions on such an `X` and are discharged here:
`AlgebraicGeometry.Space.weaklyAssociatedPointsOfSpace_eq_setOf_localRingDimension_eq_zero` from
reducedness, which integrality supplies, and
`AlgebraicGeometry.Space.hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian`.

The route never leaves universe `u` and never passes through the étale local ring `𝒪_{X, x̄}`: the
weaker reductions
`AlgebraicGeometry.Space.picardClass_eq_zero_of_forall_isUnit_mul_canonicalGenericRatio` and
`AlgebraicGeometry.Space.picardClass_eq_zero_of_forall_isUnit_functionFieldToEtaleFractionRing`
read the ratio there and are not used.

## Main results

* `AlgebraicGeometry.Space.picardClass_eq_zero_of_forall_isUnit_canonicalGenericRatio`: the
  statement above.

## References

* [Stacks Project, Tag 0EN6](https://stacks.math.columbia.edu/tag/0EN6)
* [Stacks Project, Tag 0EPX](https://stacks.math.columbia.edu/tag/0EPX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Order

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] meromorphicSectionModuleRingedSiteModule
attribute [local instance] nonempty_top_chartScheme
attribute [local instance] chartMeromorphicFunctionAlgebra chartFunctionFieldAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : AlgebraicSpaces B S hS}
    (hdec : IsDecentSpace B S hS X.1)
    (hInt : IsIntegralSpace B S hS X.1)
    (hN : HasEtaleLocalProperty B S hS X.1 (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))

/-- **The geometric claim of Stacks 0EPX.** On a normal, locally Noetherian, integral, decent
algebraic space `X`, a regular meromorphic section `t` of an invertible `𝒪_X`-module `ℒ` whose
canonical ratio at the generic point of every prime divisor is the image of a unit of the
henselian local ring there has trivial Picard class — that is, `t` trivializes `ℒ`.

This is the claim the source of Stacks 0EPX makes and calls the whole content of the lemma. It is
the covering family of integral affine trivializing charts
(`AlgebraicGeometry.Space.picardClass_eq_zero_of_generatesOnChart_isAffine_isIntegral`) fed, on
each member, with algebraic Hartogs
(`AlgebraicGeometry.Space.generatesOnChart_of_forall_ord_eq_zero`) whose order-of-vanishing
hypothesis is step three of the flat-descent route,
`AlgebraicGeometry.Space.ord_chartRatio_eq_zero_of_forall_isUnit_canonicalGenericRatio`. -/
theorem picardClass_eq_zero_of_forall_isUnit_canonicalGenericRatio
    (hNormal : IsNormal B S hS X.1)
    (L : Modules.{u, u} B S hS X.1 X.2) (hL : IsInvertibleModule (B := B) X L)
    (t : MeromorphicSection.{u, u} B S hS X.1 X.2 L)
    (hreg : IsRegularMeromorphicSection.{u, u} B S hS X.1 X.2 L t)
    (hgen : ∀ W : PrimeDivisor B S hS X.1,
      ∃ v : ↥(W.genericHenselianLocalRing B S hS X.2 hdec), IsUnit v ∧
        W.canonicalGenericRatio B S hS X.2 hdec L hL hInt hN t =
          algebraMap ↥(W.genericHenselianLocalRing B S hS X.2 hdec)
            (W.genericTotalFractionRing B S hS X.2 hdec) v) :
    picardClass (B := B) X L hL = 0 := by
  -- The two conditions of Stacks 0EN6, part (2), on such an `X`.
  have hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X,
      localRingDimension B S hS z = 0 := by
    intro z hz
    rwa [weaklyAssociatedPointsOfSpace_eq_setOf_localRingDimension_eq_zero B S hS X
      (hInt.hasEtaleLocalProperty_isReduced B S hS X.1)] at hz
  have hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1 :=
    hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X.1 X.2 hN
  refine picardClass_eq_zero_of_generatesOnChart_isAffine_isIntegral B S hS X.2 hNormal hInt
    L hL t fun V hV hVint ⟨e, hecompat, hebij⟩ => ?_
  have : AlgebraicGeometry.IsIntegral (chartScheme V) := hVint
  have : IsLocallyNoetherian (chartScheme V) := isLocallyNoetherian_chartScheme B S hS X hN V
  have : AlgebraicGeometry.IsNormal (chartScheme V) :=
    (isNormal_iff_forall_etale B S hS X.1 X.2).mp hNormal V.obj.left V.obj.hom V.property
  exact generatesOnChart_of_forall_ord_eq_zero B S hS X L V e hecompat hebij t hwa hfin hV
    (chartRatio_ne_zero_of_isRegularMeromorphicSection B S hS X L V e hecompat hebij t hwa hfin
      hV hreg)
    fun z hz => ord_chartRatio_eq_zero_of_forall_isUnit_canonicalGenericRatio B S hS hwa hfin
      hdec hInt hN hNormal L hL t V hV e hecompat hebij hgen z hz

end AlgebraicGeometry.Space

end
