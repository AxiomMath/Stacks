module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicChartFlatDescentTrivialization
public import StacksFrontier.AlgebraicGeometry.Spaces.Normal
public import StacksFrontier.AlgebraicGeometry.Spaces.PicardWeilDivisorClassHom

/-!
# Stacks 0EPX: injectivity of `Pic(X) ⟶ Cl(X)` on a normal space

Let `X` be a locally Noetherian integral algebraic space over a scheme `S`, and let `X` be
normal. Stacks 0EPX asserts that the homomorphism

`Pic(X) ⟶ Cl(X)`

of Stacks 0EPW — here `AlgebraicGeometry.Space.canonicalPicardToWeilDivisorClassHom`, which
takes no auxiliary data — is injective. That is proved here, with no hypothesis beyond the
source's own.

## Main results

* `AlgebraicGeometry.Space.injective_canonicalPicardToWeilDivisorClassHom`: **Stacks 0EPX.**

## What discharges what

The statement is the source's, with the source's binders and no others: `X` an algebraic space
over the scheme `S` (`hX`), integral (`hInt`), locally Noetherian (`hN`) and normal (`hNormal`).
There is no auxiliary embedding, no divisor data, no instance hypotheses on the henselian local
rings at the generic points of the prime divisors, and no decency hypothesis — Stacks 0AD4 puts
decency *inside* integrality (`IsIntegralSpace` is reducedness, decency and irreducibility of
the space of points), so `AlgebraicGeometry.Space.IsIntegralSpace.isDecentSpace` supplies it
where the development's `𝒪^h_{X, ξ}` needs it. The same is true of the two carriers of Stacks
0EPW.

* No auxiliary `AlgebraicGeometry.Space.GenericFractionEmbedding` or
  `AlgebraicGeometry.Space.PicardDivisorData` is used, the homomorphism being the closed term
  of Stacks 0EPW; the two remaining obligations of that closed term,
  `AlgebraicGeometry.Space.canonicalRatioIsUnitOnGeneratingChart` and the tensor identity fed by
  `AlgebraicGeometry.Space.hasCanonicalTensorProductSection`, are proved.
* The three instance hypotheses on the henselian local rings at the generic points of the prime
  divisors — nontriviality, Noetherianness and Krull dimension at most one — are conclusions of
  Stacks 0ENK on such an `X`, and are supplied with `have` below. They are `Prop`-valued
  classes, hence definitionally unique, so that needs no transport — exactly as in
  `StacksFrontier/AlgebraicGeometry/Spaces/PicardWeilDivisorClassHom.lean`.
* The rescaling `t = f⁻¹ s` of a regular meromorphic section by an invertible rational function
  is, in this namespace,
  `exists_isRegularMeromorphicSection_canonicalLocalRatio_eq_genericEmb_mul`.
* The *arithmetic* half of the claim of the source — that `0 = ord_{Z, ℒ}(t)` makes the ratio a
  unit of `𝒪^h_{X, ξ}`, which is legitimate because normality makes that ring a discrete
  valuation ring — is, in this namespace,
  `PrimeDivisor.exists_isUnit_canonicalGenericRatio_of_orderOfVanishingSection_eq_zero`.
* The *geometric* half — the claim the source makes and calls the whole content of the lemma,
  that a regular meromorphic section of an invertible `𝒪_X`-module which generates that module
  at the generic point of every prime divisor trivializes it — is
  `AlgebraicGeometry.Space.picardClass_eq_zero_of_forall_isUnit_canonicalGenericRatio`
  (`StacksFrontier/AlgebraicGeometry/Spaces/MeromorphicChartFlatDescentTrivialization.lean`), and
  is what the next section records.

## The geometric claim, and the route that proves it

The source's argument is étale-local: shrink to an affine chart `U = Spec(A)` with `A` a normal
Noetherian domain over which `ℒ` is free on `s_U`, write `t|_U = f · s_U` with `f` in the
function field of `U`, deduce from the unit hypothesis at each prime divisor that `f` is a unit
of `A_𝔭` at every height-one prime `𝔭`, conclude `f ∈ A^×` by algebraic Hartogs, and glue. The
development follows it in that order.

**The covering family.** `AlgebraicGeometry.Space.exists_coversTop_isAffine_isIntegral_generator`
(`StacksFrontier/AlgebraicGeometry/Spaces/NormalIntegralChartCoveringFamily.lean`) produces the
`CategoryTheory.GrothendieckTopology.CoversTop` family of étale charts with affine integral
scheme over each of which `ℒ` is free on a compatible family of generators: the affine charts
(`AlgebraicGeometry.Space.SmallEtale.coversTop_affineCharts`) refined twice by
`Stacks.Sites.coversTop_bind` — first by the trivializing sieve of
`AlgebraicGeometry.Space.exists_generator_cover_smul_of_isInvertible`, then by the integral
affine charts of `AlgebraicGeometry.Space.exists_isAffine_isIntegral_ofArrows`, which runs the
shrinking step of Stacks 0AYH on an affine *open* of each member
(`AlgebraicGeometry.Space.exists_isAffine_isIntegral_chart_mem_range`), that step wanting an
affine chart and the members not being affine. Normality and local Noetherianness of the members
are not in the conclusion because they hold of *every* chart.

*Why the order of the two refinements is forced.* Refining an integral chart by charts
trivializing `ℒ` destroys integrality — an étale scheme over an integral scheme need not be
integral — and nothing re-establishes it, integrality not being étale-local. The source does it
the other way round, trivializing first and *then* arranging the chart integral (its appeal to
Properties of Spaces, Lemma 28.7.5 comes after the choice of `U`), which works because an
integral affine open of a chart carrying a free generator still carries one by restriction. Do
not invert this to make a step go through.

**From generation over the family to triviality of the class.**
`AlgebraicGeometry.Space.picardClass_eq_zero_of_generatesOnChart_coversTop`
(`StacksFrontier/AlgebraicGeometry/Spaces/MeromorphicSectionCoveringTrivialization.lean`): a
meromorphic section generating an invertible `ℒ` over every member of a covering family
trivializes it. `Stacks.SheafOfModules.nonempty_iso_unit_of_bijective_smul_of_coversTop` wants a
*global* section of `ℒ` and `AlgebraicGeometry.Space.GeneratesOnChart` supplies one over each
member only; the descent is that the chartwise sections *agree*, which
`AlgebraicGeometry.Space.eq_of_eval_eq_toMeromorphicSectionSheaf_one_tmul` proves — two free
generators over one chart differ by a unit of the regular functions
(`AlgebraicGeometry.Space.exists_isUnit_smul_of_bijective_smul`), a free generator reads the
meromorphic sections injectively
(`AlgebraicGeometry.Space.injective_toMeromorphicSectionSheaf_tmul`), and
`AlgebraicGeometry.Space.injective_toMeromorphicFunctionSheaf` kills the unit. The gluing itself
is then Mathlib's
`CategoryTheory.Presheaf.FamilyOfElementsOnObjects.IsCompatible.existsUnique_section`, the
sections of a presheaf of modules being by definition those of its underlying presheaf of abelian
groups. Nothing of this uses regularity of the section, integrality, decency or Noetherianness.
Joined with the covering family it is
`AlgebraicGeometry.Space.picardClass_eq_zero_of_generatesOnChart_isAffine_isIntegral`, so the
claim becomes a statement about **one** chart.

**Algebraic Hartogs on one chart.**
`AlgebraicGeometry.Space.generatesOnChart_of_forall_ord_eq_zero`
(`StacksFrontier/AlgebraicGeometry/Spaces/MeromorphicChartHartogsGenerator.lean`): on an integral
affine normal locally Noetherian étale chart over which `ℒ` is free on `e`, a meromorphic section
whose nonzero ratio against `e` has order of vanishing zero at every codimension-one point of the
chart scheme generates `ℒ` over that chart. It is
`AlgebraicGeometry.Space.exists_isUnit_chartRatio_of_forall_ord_eq_zero` — Hartogs
(`Stacks.AlgebraicGeometry.UnitsNormalProper.exists_globalSection_of_forall_ord_eq_zero`) applied
to the rational function and to its inverse, making it a unit regular function — followed by
`AlgebraicGeometry.Space.generatesOnChart_of_chartRatio_eq_algebraMap`. Its nonvanishing
hypothesis is `AlgebraicGeometry.Space.chartRatio_ne_zero_of_isRegularMeromorphicSection`: a zero
ratio makes every multiple of `t` over the chart the image of `0 ⊗ e`, so multiplication by `t`
on `𝒦_X(V)` is constant, and injectivity of that map forces `1 = 0` in `𝒦_X(V)` — impossible,
that ring being the function field of an integral affine chart.

**The ratio on a prescribed chart, and the change of base ring.** A meromorphic section of `ℒ`
is, over a chart `V` carrying a free generator `e`, the product of exactly one meromorphic
function with `e` — `AlgebraicGeometry.Space.chartRatio`, with
`AlgebraicGeometry.Space.eval_eq_toMeromorphicSectionSheaf_tmul_chartRatio` and
`AlgebraicGeometry.Space.chartRatio_eq_of_eval_eq` for its defining property and its uniqueness.
Hartogs is stated against `AlgebraicGeometry.Scheme.ord`, so the ratio has to be read as a
rational function of the chart scheme: that is
`AlgebraicGeometry.Space.chartMeromorphicFunctionFieldEquiv`
(`StacksFrontier/AlgebraicGeometry/Spaces/MeromorphicChartFunctionField.lean`), uniqueness of the
total ring of fractions between Stacks 0EN6, part (2)
(`AlgebraicGeometry.Space.isFractionRing_meromorphicFunctionSheaf_obj`) and **Mathlib's**
`AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen` at the open `⊤`. The two
hypotheses of Stacks 0EN6 are conclusions on such an `X`:
`AlgebraicGeometry.Space.weaklyAssociatedPointsOfSpace_eq_setOf_localRingDimension_eq_zero` for
the weakly associated points and
`AlgebraicGeometry.Space.hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian` for the
irreducible components.

**The order of vanishing of that ratio: the flat-descent route.** What the unit hypothesis of the
source gives is about a *different* ratio — `t` divided by the generator `s_ξ` of `ℒ` over
`Z.genericStalkChart`, read in `Q(𝒪^h_{X, ξ})`
(`AlgebraicGeometry.Space.PrimeDivisor.canonicalGenericRatio`). Identifying the two is the whole
content of the step, and it is done along the *flat* leg
`j : Spec(𝒪_{U, u}) ⟶ X`, in three steps, assembled by
`AlgebraicGeometry.Space.ord_chartRatio_eq_zero_of_forall_isUnit_canonicalGenericRatio`
(`StacksFrontier/AlgebraicGeometry/Spaces/Decent/PrimeDivisorChartRatioFlatDescent.lean`).

1. `AlgebraicGeometry.Space.PrimeDivisor.exists_isUnit_genericStalkCoefficient_of_isUnit`
   (`StacksFrontier/AlgebraicGeometry/Spaces/Decent/PrimeDivisorGenericStalkNormalDescent.lean`):
   the coefficient of Stacks 0EPR is the image of a **unit of `𝒪_{U, u}`** as soon as the
   canonical ratio is the image of a unit of `𝒪^h_{X, ξ}`. The arithmetic is
   `Stacks.ValuationRing.exists_isUnit_algebraMap_eq_of_isUnit_map`
   (`StacksFrontier/RingTheory/ValuationRing/UnitFractionLocalHom.lean`): a fraction of a valuation
   ring whose image under a *local* homomorphism is a unit is already the image of a unit. The
   locality is
   `AlgebraicGeometry.Space.PrimeDivisor.isLocalHom_genericStalkSectionsToHenselian`, Stacks 0EMY
   specialized to `Z.genericChart`; and `𝒪_{U, u}` —
   `AlgebraicGeometry.Space.PrimeDivisor.genericStalkRing` — is a **discrete valuation ring**
   (`AlgebraicGeometry.Space.PrimeDivisor.exists_isDiscreteValuationRing_genericStalkRing`),
   being the stalk of a scheme, so that
   `AlgebraicGeometry.isDiscreteValuationRing_stalk_of_coheight_eq_one` applies with its three
   hypotheses available:
   `AlgebraicGeometry.Space.PrimeDivisor.isNormal_genericChart` (which is
   `AlgebraicGeometry.Space.isNormal_iff_forall_etale` read there),
   `AlgebraicGeometry.Space.PrimeDivisor.isLocallyNoetherian_chart` and
   `AlgebraicGeometry.Space.PrimeDivisor.coheight_genericChart_point`. No integrality of that
   chart is needed. Two readings of this development recorded the step as impossible; the first
   missed the one-line specialization of Stacks 0EMY, the second the one-line
   `isNormal_genericChart`. **Absence of a declaration is not absence of the fact.**
2. `AlgebraicGeometry.Space.PrimeDivisor.exists_sieve_isUnit_baseChangeChartRatio`
   (`StacksFrontier/AlgebraicGeometry/Spaces/Decent/PrimeDivisorBaseChangeChartRatioUnit.lean`):
   over the charts of a covering sieve of the base change of `V` along `j` the pullback of
   `chartRatio` is a **unit regular function**. It joins step 1 to the comparison of the two
   ratios over a common chart,
   `AlgebraicGeometry.Space.PrimeDivisor.exists_sieve_genericStalkCoefficient_eq_mul_chartRatio`,
   through the per-chart naturality of `AlgebraicGeometry.Space.toMeromorphicFunctionSheaf`,
   `AlgebraicGeometry.Space.meromorphicFunctionSheaf_map_algebraMap`.
3. The descent back to `𝒪_{V, z}`, at a point `z` of `chartScheme V` of coheight one. The
   comparison of step 2 is made over a chart `Q` of `Spec(𝒪_{U, u})`, which is **not** an object
   of the small étale site of `X`: `j` is only *flat*
   (`AlgebraicGeometry.Space.PrimeDivisor.isFlat_genericStalkMorphism`), and nothing stronger is
   true, `Spec` of a local ring of a scheme being a filtered limit of opens and not étale over
   it. So the étale naturality does not reach `Q` and the comparison has to come down along
   flatness. The ingredients:
   * *the germ square*,
     `AlgebraicGeometry.Space.PrimeDivisor.lift_chartMeromorphicFunctionFieldEquiv_eq`
     (`StacksFrontier/AlgebraicGeometry/Spaces/Decent/PrimeDivisorBaseChangeGermSquare.lean`): the
     two readings of one meromorphic function of `V` in `Frac(𝒪_{Q, q})` — one through the
     function field of `V` and its stalk at `z`, the other through the flat pullback to `𝒦(Q)`
     and its germ at `q` — agree. Nothing in the library related
     `AlgebraicGeometry.Space.chartMeromorphicPullbackHom` to a stalk before it;
   * *the fractions on both sides*: Mathlib's instance over
     `AlgebraicGeometry.stalkFunctionFieldAlgebra` for `𝒪_{V, z}` and its function field, which
     is the instance `AlgebraicGeometry.Scheme.ord` is elaborated with, and
     `AlgebraicGeometry.Space.PrimeDivisor.isFractionRing_genericStalkChartMeromorphic` — Stacks
     0EN6, part (2) at an arbitrary affine chart of `Spec(𝒪_{U, u})`, the identity-chart case
     `isFractionRing_genericStalkMeromorphic` alone not reaching a sieve member;
   * *flatness*, `AlgebraicGeometry.Space.PrimeDivisor.flat_genericStalkBaseChangeSchemeMap`, a
     morphism of étale charts of `Spec(𝒪_{U, u})` being étale beneath (Stacks 03EC, part (2),
     `AlgebraicGeometry.Space.etale_toOver_map_of_smallEtale`) and so flat, composed with
     `AlgebraicGeometry.Space.PrimeDivisor.flat_genericStalkBaseChangeDiagram_g`;
     `AlgebraicGeometry.Flat.stalkMap` then makes the stalk map flat and
     `mem_nonZeroDivisors_algebraMap_of_flat` makes it preserve nonzerodivisors, which is what
     builds the two localization lifts the germ square takes as hypotheses;
   * *the point `q`*, in this namespace
     `PrimeDivisor.exists_points_genericStalkBaseChangeChart`, with the point of `chartScheme V`
     *prescribed* as `z` and both projections of one point kept
     — `AlgebraicGeometry.Space.PrimeDivisor.exists_mem_range_genericStalkBaseChangeChart` ran
     the same construction but chose the point of `V` and discarded the projection to it;
   * *refining the sieve to an affine member containing it*,
     `AlgebraicGeometry.Space.SmallEtale.exists_affine_mem_range_of_mem_topology`;
   * *the descent itself*, `exists_isUnit_eq_algebraMap_of_isUnit_of_faithfullyFlat`
     (`StacksFrontier/RingTheory/FaithfullyFlatFractionUnit.lean`), which descends unit-ness of a
     *total fraction* along a faithfully flat algebra outright. **The flat leg needs no valuation
     ring**: `𝒪_{V, z} → 𝒪_{Q, q}` is faithfully flat for free — flat as above and local because
     it is a stalk map, which is `Module.FaithfullyFlat.of_flat_of_isLocalHom`. The discrete
     valuation ring is wanted in step 1, where the leg is a henselization, and nowhere here;
   * and `AlgebraicGeometry.Scheme.ord_algebraMap_of_isUnit`, which turns a unit of the local ring
     at a coheight-one point into order of vanishing zero.

   The coheight-one point of the chart determines the prime divisor at which the hypothesis is
   read: `AlgebraicGeometry.Space.exists_primeDivisor_genericPoint_eq_chartSchemeToPoints`
   (`StacksFrontier/AlgebraicGeometry/Spaces/Decent/PrimeDivisorChartPointNeighborhood.lean`).

## Two remarks on the route

*Why the flat and étale legs do not join at `𝒪_{X, x̄}`.* It looks as though step 2's unit of
`𝒪_Q` could be carried into the étale local ring at a geometric point and fed to
`AlgebraicGeometry.Space.ord_eq_zero_of_functionFieldToEtaleFractionRing_eq_algebraMap`, which
already packages locality of `𝒪_{V, z} → 𝒪_{X, x̄}`
(`AlgebraicGeometry.Space.isLocalHom_chartLocalRingToEtaleLocalRing`) with the discrete valuation
ring at `z`. The map `𝒪_Q → 𝒪_{X, x̄}` it would need exists only through
`AlgebraicGeometry.exists_lift_of_strictlyHenselian_of_weaklyEtale`, which supplies a
*non-canonical* lift; the compatibility square the comparison then requires is a statement about
the canonical structure map and cannot be had for an arbitrary lift. So the flat route finishes
at `Frac(𝒪_{Q, q})` and never leaves universe `u`.

*The étale route is kept, and its `ψ` is existential.* The parallel reduction
`AlgebraicGeometry.Space.picardClass_eq_zero_of_forall_isUnit_mul_canonicalGenericRatio`
(`StacksFrontier/AlgebraicGeometry/Spaces/MeromorphicChartEtaleUnitTrivialization.lean`) reads both
ratios in `Q(𝒪_{X, x̄})` and is **not** used by the proof below. Its comparison map `ψ` is
*existentially* quantified, and must stay so: a ring homomorphism `𝒪^h_{X, ξ} → 𝒪_{X, x̄}`
preserving nonzerodivisors need not be the structure map of Stacks 0EMZ, and the comparison is a
statement about that structure map, so quantifying over every such homomorphism would state
something no proof can give. Also kept are the étale-route order-of-vanishing facts
`AlgebraicGeometry.Space.PrimeDivisor.ord_mk'_eq_ord_mk'_chart` (Stacks 0ENM on an arbitrary
étale chart, which `AlgebraicGeometry.Space.PrimeDivisor.ord_functionFieldToTotalFractionRing`
does not give) and
`AlgebraicGeometry.Space.chartMeromorphicToEtaleFractionRing_restrict`, together with the
naturality
`AlgebraicGeometry.Space.functionFieldToEtaleFractionRing_chartFunctionFieldMap_stalkMap`.

## Flagged duplicates, left alone

`Stacks.Sites.coversTop_of_exists_hom` duplicates
`CategoryTheory.GrothendieckTopology.CoversTop.of_exists_hom`;
`AlgebraicGeometry.Space.isLocallyNoetherian_chartScheme` is declared twice with the same
statement; `AlgebraicGeometry.Scheme.ord_algebraMap_of_isUnit` is duplicated as
`Stacks.AlgebraicGeometry.MeromorphicConstant.ord_algebraMap_of_isUnit`; and
`AlgebraicGeometry.isDiscreteValuationRing_stalk_of_coheight_eq_one` as
`Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk`. Note also that
`AlgebraicGeometry.Space.isNormal_chartScheme` is `private` to its module and so unusable;
`AlgebraicGeometry.Space.isNormal_iff_forall_etale` is the replacement.

## References

* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EPQ](https://stacks.math.columbia.edu/tag/0EPQ)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0EPV](https://stacks.math.columbia.edu/tag/0EPV)
* [Stacks Project, Tag 0EPW](https://stacks.math.columbia.edu/tag/0EPW)
* [Stacks Project, Tag 0EPX](https://stacks.math.columbia.edu/tag/0EPX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule
attribute [local instance] PrimeDivisor.genericStalkMeromorphicAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
variable (hInt : IsIntegralSpace B S hS X)
variable (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))

/-- **Stacks 0EPX.** On a normal, locally Noetherian, integral algebraic space `X` over a scheme
`S`, the homomorphism

`Pic(X) ⟶ Cl(X)`

of Stacks 0EPW — `AlgebraicGeometry.Space.canonicalPicardToWeilDivisorClassHom`, which takes no
auxiliary data — is injective.

The binders are the source's and nothing else: `X` an algebraic space over the scheme `S`
(`hX`), integral (`hInt`), locally Noetherian (`hN`) and normal (`hNormal`). There is no
auxiliary embedding, no divisor data, no decency hypothesis — Stacks 0AD4 puts decency *inside*
integrality, so `AlgebraicGeometry.Space.IsIntegralSpace.isDecentSpace` supplies it — no instance
hypotheses on the henselian local rings at the generic points of the prime divisors, and nothing
left of the claim the source makes and calls the whole content of the lemma: that is
`AlgebraicGeometry.Space.picardClass_eq_zero_of_forall_isUnit_canonicalGenericRatio`, passed
below. See the module docstring for what each of those discharges is.

Triviality of `ℒ` is written as the vanishing of its class in `Pic(X)`, which by
`AlgebraicGeometry.Space.picardClass_eq_zero_iff` says that `ℒ` is isomorphic to `𝒪_X`. -/
@[stacks 0EPX "injectivity of Pic(X) → Cl(X) — the homomorphism of Stacks 0EPW at the canonical
  choices, which takes no auxiliary data — on a normal, locally Noetherian, integral algebraic
  space over a scheme. No hypothesis beyond the source's: decency comes from integrality by
  `IsIntegralSpace.isDecentSpace`, the claim of the source is
  `picardClass_eq_zero_of_forall_isUnit_canonicalGenericRatio`, the rescaling t = f⁻¹ s is
  `exists_isRegularMeromorphicSection_canonicalLocalRatio_eq_genericEmb_mul`, and the three
  instance hypotheses on the henselian local rings at the generic points of the prime divisors
  are conclusions of Stacks 0ENK"]
theorem injective_canonicalPicardToWeilDivisorClassHom (hNormal : IsNormal B S hS X) :
    Function.Injective (canonicalPicardToWeilDivisorClassHom B S hS hX hInt hN) := by
  have hdec : IsDecentSpace B S hS X := hInt.isDecentSpace B S hS X
  have : ∀ W : PrimeDivisor B S hS X,
      Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
    W.nontrivial_genericHenselianLocalRing B S hS hX hdec hInt hN
  have : ∀ W : PrimeDivisor B S hS X,
      IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
    W.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hN
  have : ∀ W : PrimeDivisor B S hS X,
      Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
    W.krullDimLE_genericHenselianLocalRing B S hS hX hdec hInt hN
  exact injective_canonicalPicardToWeilDivisorClassGroup B S hS hX hdec hInt hN hNormal
    (canonicalRatioIsUnitOnGeneratingChart B S hS hX hdec hInt hN)
    (canonicalTensorDivisorIdentity_of_exists_product B S hS hX hdec hInt hN
      (hasCanonicalTensorProductSection B S hS hX hdec hInt hN))
    fun L hL t hreg hgen =>
      picardClass_eq_zero_of_forall_isUnit_canonicalGenericRatio B S hS
        (X := ⟨X, hX⟩) hdec hInt hN hNormal L hL t hreg hgen

end AlgebraicGeometry.Space

end
