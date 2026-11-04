module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorCanonicalRatio
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorChartPointNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicChartHartogsGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionIntegralChartTrivialization
public import StacksFrontier.AlgebraicGeometry.Spaces.Normal
public import StacksFrontier.AlgebraicGeometry.Spaces.OrderOfVanishingEtaleChart

/-!
# A unit chart ratio in the étale local rings trivializes an invertible module

Let `X` be a normal, locally Noetherian, integral algebraic space over a scheme `S`, let `ℒ` be
an invertible `𝒪_X`-module and let `t` be a regular meromorphic section of `ℒ`. The geometric
claim of Stacks 0EPX — that `t` trivializes `ℒ` as soon as it generates `ℒ` at the generic point
of every prime divisor — is reduced here to a statement about **one** rational function read in
**one** étale local ring:

> for every étale chart `V` of `X` with affine integral scheme carrying a free generator `e` of
> `ℒ`, every geometric point `x̄` of `X` lifted to `V`, and the point `z` of `chartScheme V`
> beneath that lift, if `z` has coheight one then the image of the ratio `t / e`
> (`AlgebraicGeometry.Space.chartRatio`) in `Q(𝒪_{X, x̄})` is the image of a **unit** of
> `𝒪_{X, x̄}`.

That is the hypothesis `hunit` of the two results below. It is the *identification of the two
ratios* which the roadmap of
`StacksFrontier/AlgebraicGeometry/Spaces/PicardWeilDivisorClassInjective.lean` records as the last
obligation of Stacks 0EPX: the unit hypothesis of the source is about the ratio of `t` against
the generator chosen at the generic point of a prime divisor, read in `𝒪^h_{X, ξ}`, and `hunit`
is that statement transported to the ratio against `e`, read in `𝒪_{X, x̄}`. Everything between
`hunit` and the triviality of the Picard class is discharged here.

## What each step is

* The point `z` is the chart point of a small étale neighbourhood of a geometric point with
  chart exactly `V`:
  `AlgebraicGeometry.Space.exists_geometricPoint_chartPoint_eq`.
* A unit in `𝒪_{X, x̄}` forces order of vanishing zero at `z`:
  `AlgebraicGeometry.Space.ord_eq_zero_of_functionFieldToEtaleFractionRing_eq_algebraMap`.
  Neither Noetherianness nor a dimension bound on `𝒪_{X, x̄}` is needed.
* Order of vanishing zero at every coheight-one point makes `t` generate `ℒ` over `V`, by
  algebraic Hartogs: `AlgebraicGeometry.Space.generatesOnChart_of_forall_ord_eq_zero`, whose
  nonvanishing hypothesis comes from regularity of `t`
  (`AlgebraicGeometry.Space.chartRatio_ne_zero_of_isRegularMeromorphicSection`).
* Generation over every such chart kills the Picard class:
  `AlgebraicGeometry.Space.picardClass_eq_zero_of_generatesOnChart_isAffine_isIntegral`.

The instance hypotheses on the chart scheme are conclusions on such an `X`: local
Noetherianness is `AlgebraicGeometry.Space.isLocallyNoetherian_chartScheme` and normality is
`AlgebraicGeometry.Space.isNormal_iff_forall_etale` read at the chart — the direct producer
`AlgebraicGeometry.Space.isNormal_chartScheme` being `private` to its module.

The hypotheses `hwa` and `hfin` are the two conditions of Stacks 0EN6, part (2), which identify
the meromorphic functions of an integral affine chart with the function field of its scheme
(`AlgebraicGeometry.Space.chartMeromorphicFunctionFieldEquiv`). They are carried rather than
derived because the *statement* of `hunit` names that identification; on such an `X` they are
`AlgebraicGeometry.Space.weaklyAssociatedPointsOfSpace_eq_setOf_localRingDimension_eq_zero` and
`AlgebraicGeometry.Space.hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian`, and
being `Prop`-valued they do not affect the identification.

## The form the source's hypothesis has

`hunit` asks for a unit outright, and so does not mention the source's hypothesis. The third
result below is the same reduction with that hypothesis — `hgen`, the unit form of the canonical
ratio at the generic point of every prime divisor — restored, so that what is left to prove is
exactly the *comparison*: the image of `t / e` in `Q(𝒪_{X, x̄})` is a unit of `𝒪_{X, x̄}` times the
image there of `AlgebraicGeometry.Space.PrimeDivisor.canonicalGenericRatio`. The two further
ingredients that needs are available: the coheight-one chart point determines the prime divisor
(`AlgebraicGeometry.Space.exists_primeDivisor_genericPoint_eq_chartSchemeToPoints`), and the
comparison map `Q(𝒪^h_{X, ξ}) → Q(𝒪_{X, x̄})` exists at any geometric point above `ξ`
(`AlgebraicGeometry.Space.exists_ringHom_ord_henselianLocalRing`).

## Main results

* `AlgebraicGeometry.Space.generatesOnChart_of_forall_isUnit_functionFieldToEtaleFractionRing`:
  the chart-level statement.
* `AlgebraicGeometry.Space.picardClass_eq_zero_of_forall_isUnit_functionFieldToEtaleFractionRing`:
  the global one.
* `AlgebraicGeometry.Space.picardClass_eq_zero_of_forall_isUnit_mul_canonicalGenericRatio`: the
  global one with the source's hypothesis restored, leaving the comparison of the two ratios as
  the single obligation.

Deliberately untagged: `hunit` and the comparison are unproved, so none of the three proves
Stacks 0EPX.

## References

* [Stacks Project, Tag 0EN6](https://stacks.math.columbia.edu/tag/0EN6)
* [Stacks Project, Tag 0EPX](https://stacks.math.columbia.edu/tag/0EPX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Order
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule
attribute [local instance] nonempty_top_chartScheme
attribute [local instance] chartMeromorphicFunctionAlgebra chartFunctionFieldAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)

/-! ### The chart-level reduction -/

variable (L : Modules.{u, u} B S hS X.1 X.2) (V : SmallEtale B S hS X.1)
    (e : (W : SmallEtale B S hS X.1) → (W ⟶ V) → L.val.obj (op W))
    (hcompat : ∀ (W W' : SmallEtale B S hS X.1) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hfree : ∀ (W : SmallEtale B S hS X.1) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X.1 X.2 W ↦ r • e W k)
    (t : MeromorphicSection.{u, u} B S hS X.1 X.2 L)

/-- **The chart-level step of Stacks 0EPX from a unit chart ratio in the étale local rings.** On
an integral, affine, normal, locally Noetherian étale chart `V` over which `ℒ` is free on `e`, a
*regular* meromorphic section `t` generates `ℒ` over `V` as soon as, at every lift of a geometric
point of `X` to `V` whose chart point `z` has coheight one, the image of the ratio `t / e` in
`Q(𝒪_{X, x̄})` is the image of a unit of `𝒪_{X, x̄}`.

The unit forces the order of vanishing at `z` to be zero
(`AlgebraicGeometry.Space.ord_eq_zero_of_functionFieldToEtaleFractionRing_eq_algebraMap`), every
coheight-one point of `chartScheme V` is such a chart point
(`AlgebraicGeometry.Space.exists_geometricPoint_chartPoint_eq`), and algebraic Hartogs then makes
`t` a generator (`AlgebraicGeometry.Space.generatesOnChart_of_forall_ord_eq_zero`); the
nonvanishing of the ratio that Hartogs needs is regularity of `t`
(`AlgebraicGeometry.Space.chartRatio_ne_zero_of_isRegularMeromorphicSection`). -/
theorem generatesOnChart_of_forall_isUnit_functionFieldToEtaleFractionRing
    [AlgebraicGeometry.IsIntegral (chartScheme V)]
    [IsLocallyNoetherian (chartScheme V)]
    [AlgebraicGeometry.IsNormal (chartScheme V)]
    (hV : IsAffine (chartScheme V))
    (hreg : IsRegularMeromorphicSection.{u, u} B S hS X.1 X.2 L t)
    (hunit : ∀ (z : chartScheme V) (xbar : GeometricPoint B S hS X.1)
      (p : xbar.val.siteObject ⟶ V.obj.left)
      (hp : V.obj.hom.app (op xbar.val.siteObject) p = xbar.val.value),
      chartPoint B S hS X.1 (⟨V, p, hp⟩ : SmallEtaleNeighborhood xbar) = z →
      xbar.image = chartSchemeToPoints B S hS X.1 V z → coheight z = 1 →
      ∃ w : (etaleLocalRing B S hS X.1 xbar : Type (u + 1)), IsUnit w ∧
        functionFieldToEtaleFractionRing B S hS X.1 X.2
            (⟨V, p, hp⟩ : SmallEtaleNeighborhood xbar)
            (chartMeromorphicFunctionFieldEquiv B S hS X hwa hfin V hV
              (chartRatio B S hS X.1 X.2 L V e hcompat hfree t)) =
          algebraMap ((etaleLocalRing B S hS X.1 xbar : Type (u + 1)))
            (FractionRing ((etaleLocalRing B S hS X.1 xbar : Type (u + 1)))) w) :
    GeneratesOnChart B S hS X.2 L t V := by
  have hne := chartRatio_ne_zero_of_isRegularMeromorphicSection B S hS X L V e hcompat hfree t
    hwa hfin hV hreg
  have hne' : chartMeromorphicFunctionFieldEquiv B S hS X hwa hfin V hV
      (chartRatio B S hS X.1 X.2 L V e hcompat hfree t) ≠ 0 := fun h =>
    hne ((chartMeromorphicFunctionFieldEquiv B S hS X hwa hfin V hV).injective
      (h.trans (map_zero (chartMeromorphicFunctionFieldEquiv B S hS X hwa hfin V hV)).symm))
  refine generatesOnChart_of_forall_ord_eq_zero B S hS X L V e hcompat hfree t hwa hfin hV hne
    fun z hz => ?_
  obtain ⟨xbar, p, hp, hpt, hxbar⟩ := exists_geometricPoint_chartPoint_eq B S hS X.2 V z
  have hco : coheight (chartPoint B S hS X.1 (⟨V, p, hp⟩ : SmallEtaleNeighborhood xbar)) = 1 := by
    rw [hpt]; exact hz
  obtain ⟨w, hw, hwe⟩ := hunit z xbar p hp hpt hxbar hz
  have hord := ord_eq_zero_of_functionFieldToEtaleFractionRing_eq_algebraMap B S hS X.1 X.2
    (⟨V, p, hp⟩ : SmallEtaleNeighborhood xbar) hco _ hne' hw hwe
  rwa [hpt] at hord

/-! ### The global reduction -/

/-- **The geometric claim of Stacks 0EPX from a unit chart ratio in the étale local rings.** On a
normal, locally Noetherian, integral algebraic space `X`, a regular meromorphic section `t` of an
invertible `𝒪_X`-module `ℒ` has trivial Picard class as soon as, over every étale chart `V` with
affine integral scheme carrying a free generator `e` of `ℒ`, at every lift of a geometric point
of `X` to `V` whose chart point has coheight one, the image of the ratio `t / e` in `Q(𝒪_{X, x̄})`
is the image of a unit of `𝒪_{X, x̄}`.

This is
`AlgebraicGeometry.Space.generatesOnChart_of_forall_isUnit_functionFieldToEtaleFractionRing` on
each member of the covering family of such charts, fed to
`AlgebraicGeometry.Space.picardClass_eq_zero_of_generatesOnChart_isAffine_isIntegral`. The
instances on the chart scheme it needs beyond the two that family provides are local
Noetherianness (`AlgebraicGeometry.Space.isLocallyNoetherian_chartScheme`) and normality
(`AlgebraicGeometry.Space.isNormal_iff_forall_etale`), which hold of *every* chart. -/
theorem picardClass_eq_zero_of_forall_isUnit_functionFieldToEtaleFractionRing
    (hNormal : IsNormal B S hS X.1) (hintegral : IsIntegralSpace B S hS X.1)
    (hN : HasEtaleLocalProperty B S hS X.1 (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
    (hL : IsInvertibleModule (B := B) X L)
    (hreg : IsRegularMeromorphicSection.{u, u} B S hS X.1 X.2 L t)
    (hunit : ∀ (V : SmallEtale B S hS X.1) [AlgebraicGeometry.IsIntegral (chartScheme V)]
      (hV : IsAffine (chartScheme V))
      (e : (W : SmallEtale B S hS X.1) → (W ⟶ V) → L.val.obj (op W))
      (hcompat : ∀ (W W' : SmallEtale B S hS X.1) (k : W ⟶ V) (g : W' ⟶ W),
        (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
      (hfree : ∀ (W : SmallEtale B S hS X.1) (k : W ⟶ V),
        Function.Bijective fun r : chartRing B S hS X.1 X.2 W ↦ r • e W k)
      (z : chartScheme V) (xbar : GeometricPoint B S hS X.1)
      (p : xbar.val.siteObject ⟶ V.obj.left)
      (hp : V.obj.hom.app (op xbar.val.siteObject) p = xbar.val.value),
      chartPoint B S hS X.1 (⟨V, p, hp⟩ : SmallEtaleNeighborhood xbar) = z →
      xbar.image = chartSchemeToPoints B S hS X.1 V z → coheight z = 1 →
      ∃ w : (etaleLocalRing B S hS X.1 xbar : Type (u + 1)), IsUnit w ∧
        functionFieldToEtaleFractionRing B S hS X.1 X.2
            (⟨V, p, hp⟩ : SmallEtaleNeighborhood xbar)
            (chartMeromorphicFunctionFieldEquiv B S hS X hwa hfin V hV
              (chartRatio B S hS X.1 X.2 L V e hcompat hfree t)) =
          algebraMap ((etaleLocalRing B S hS X.1 xbar : Type (u + 1)))
            (FractionRing ((etaleLocalRing B S hS X.1 xbar : Type (u + 1)))) w) :
    picardClass (B := B) X L hL = 0 := by
  refine picardClass_eq_zero_of_generatesOnChart_isAffine_isIntegral B S hS X.2 hNormal hintegral
    L hL t fun V hV hVint ⟨e, hcompat, hfree⟩ => ?_
  have : AlgebraicGeometry.IsIntegral (chartScheme V) := hVint
  have : IsLocallyNoetherian (chartScheme V) := isLocallyNoetherian_chartScheme B S hS X hN V
  have : AlgebraicGeometry.IsNormal (chartScheme V) :=
    (isNormal_iff_forall_etale B S hS X.1 X.2).mp hNormal V.obj.left V.obj.hom V.property
  exact generatesOnChart_of_forall_isUnit_functionFieldToEtaleFractionRing B S hS X hwa hfin L V
    e hcompat hfree t hV hreg (hunit V hV e hcompat hfree)

/-! ### The reduction to the identification of the two ratios -/

/-- **The geometric claim of Stacks 0EPX, reduced to the identification of the two ratios.** On a
normal, locally Noetherian, integral, decent algebraic space `X`, a regular meromorphic section
`t` of an invertible `𝒪_X`-module `ℒ` whose canonical ratio at the generic point of every prime
divisor is the image of a unit of `𝒪^h_{X, ξ}` — the antecedent `hgen`, which is the hypothesis
of the source — has trivial Picard class, as soon as its two ratios agree up to a unit: that is
`hcomp`, which asks that over an integral affine chart `V` carrying a free generator `e` of `ℒ`,
at a coheight-one chart point `z` under a lift of a geometric point `x̄` above the generic point
of a prime divisor `Z`, the image in `Q(𝒪_{X, x̄})` of the ratio `t / e`
(`AlgebraicGeometry.Space.chartRatio`) is a unit of `𝒪_{X, x̄}` times the image there of
`AlgebraicGeometry.Space.PrimeDivisor.canonicalGenericRatio`, the ratio of `t` against the
generator chosen at `ξ`.

That is the whole of what the proof of Stacks 0EPX still owes. Everything else is discharged:
the coheight-one point of the chart determines the prime divisor
(`AlgebraicGeometry.Space.exists_primeDivisor_genericPoint_eq_chartSchemeToPoints`) and the
geometric point above it
(`AlgebraicGeometry.Space.exists_geometricPoint_chartPoint_eq`); the comparison map
`Q(𝒪^h_{X, ξ}) → Q(𝒪_{X, x̄})` along which the two ratios are read carries the unit of `hgen` to a
unit
(`AlgebraicGeometry.Space.PrimeDivisor.genericTotalFractionRingToEtaleFractionRing_algebraMap`),
so the product of the two units discharges the hypothesis of
`AlgebraicGeometry.Space.picardClass_eq_zero_of_forall_isUnit_functionFieldToEtaleFractionRing`.

The comparison map `ψ` is *existentially* quantified in `hcomp`, and deliberately so: a ring
homomorphism `𝒪^h_{X, ξ} → 𝒪_{X, x̄}` preserving nonzerodivisors need not be the structure map of
Stacks 0EMZ, and the comparison of the two ratios is a statement about that structure map and not
about every such homomorphism. Whatever discharges `hcomp` supplies the map, and
`AlgebraicGeometry.Space.exists_ringHom_ord_henselianLocalRing` is where it comes from — at any
geometric point above `ξ`, which the hypothesis `xbar.image = ξ` provides. Nothing below depends
on which map is supplied: a unit has unit image under any ring homomorphism. -/
theorem picardClass_eq_zero_of_forall_isUnit_mul_canonicalGenericRatio
    (hL : IsInvertibleModule (B := B) X L)
    (hdec : IsDecentSpace B S hS X.1) (hInt : IsIntegralSpace B S hS X.1)
    (hN : HasEtaleLocalProperty B S hS X.1 (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
    (hNormal : IsNormal B S hS X.1)
    (hreg : IsRegularMeromorphicSection.{u, u} B S hS X.1 X.2 L t)
    (hcomp : ∀ (V : SmallEtale B S hS X.1) [AlgebraicGeometry.IsIntegral (chartScheme V)]
      (hV : IsAffine (chartScheme V))
      (e : (W : SmallEtale B S hS X.1) → (W ⟶ V) → L.val.obj (op W))
      (hcompat : ∀ (W W' : SmallEtale B S hS X.1) (k : W ⟶ V) (g : W' ⟶ W),
        (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
      (hfree : ∀ (W : SmallEtale B S hS X.1) (k : W ⟶ V),
        Function.Bijective fun r : chartRing B S hS X.1 X.2 W ↦ r • e W k)
      (z : chartScheme V) (xbar : GeometricPoint B S hS X.1)
      (p : xbar.val.siteObject ⟶ V.obj.left)
      (hp : V.obj.hom.app (op xbar.val.siteObject) p = xbar.val.value),
      chartPoint B S hS X.1 (⟨V, p, hp⟩ : SmallEtaleNeighborhood xbar) = z → coheight z = 1 →
      ∀ Z : PrimeDivisor B S hS X.1, xbar.image = Z.genericPoint B S hS X.1 →
      ∃ (ψ : ↥(Z.genericHenselianLocalRing B S hS X.2 hdec) →+*
            (etaleLocalRing B S hS X.1 xbar : Type (u + 1)))
        (hψ₀ : ∀ r ∈ (↥(Z.genericHenselianLocalRing B S hS X.2 hdec))⁰,
          ψ r ∈ ((etaleLocalRing B S hS X.1 xbar : Type (u + 1)))⁰)
        (y : (etaleLocalRing B S hS X.1 xbar : Type (u + 1))), IsUnit y ∧
        functionFieldToEtaleFractionRing B S hS X.1 X.2
            (⟨V, p, hp⟩ : SmallEtaleNeighborhood xbar)
            (chartMeromorphicFunctionFieldEquiv B S hS X hwa hfin V hV
              (chartRatio B S hS X.1 X.2 L V e hcompat hfree t)) =
          algebraMap ((etaleLocalRing B S hS X.1 xbar : Type (u + 1)))
              (FractionRing ((etaleLocalRing B S hS X.1 xbar : Type (u + 1)))) y *
            Z.genericTotalFractionRingToEtaleFractionRing B S hS X.1 X.2 hdec ψ hψ₀
              (Z.canonicalGenericRatio B S hS X.2 hdec L hL hInt hN t))
    (hgen : ∀ Z : PrimeDivisor B S hS X.1,
      ∃ v : ↥(Z.genericHenselianLocalRing B S hS X.2 hdec), IsUnit v ∧
        Z.canonicalGenericRatio B S hS X.2 hdec L hL hInt hN t =
          algebraMap ↥(Z.genericHenselianLocalRing B S hS X.2 hdec)
            (Z.genericTotalFractionRing B S hS X.2 hdec) v) :
    picardClass (B := B) X L hL = 0 := by
  refine picardClass_eq_zero_of_forall_isUnit_functionFieldToEtaleFractionRing B S hS X hwa hfin
    L t hNormal hInt hN hL hreg
    fun V _ hV e hcompat hfree z xbar p hp hpt hxbar hco => ?_
  obtain ⟨Z, hZ⟩ :=
    exists_primeDivisor_genericPoint_eq_chartSchemeToPoints B S hS X.2 hdec V z hco
  have hlies : xbar.image = Z.genericPoint B S hS X.1 := hxbar.trans hZ.symm
  obtain ⟨ψ, hψ₀, y, hy, hyeq⟩ := hcomp V hV e hcompat hfree z xbar p hp hpt hco Z hlies
  obtain ⟨v, hv, hveq⟩ := hgen Z
  refine ⟨y * ψ v, hy.mul (hv.map ψ), ?_⟩
  rw [hyeq, hveq,
    Z.genericTotalFractionRingToEtaleFractionRing_algebraMap B S hS X.1 X.2 hdec ψ hψ₀ v,
    ← map_mul]

end AlgebraicGeometry.Space

end
