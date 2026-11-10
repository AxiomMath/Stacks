module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicChartFunctionField
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGeneratingLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionSheafGenerator
public import StacksFrontier.AlgebraicGeometry.UnitsNormalProper.Hartogs

/-!
# Algebraic Hartogs on an étale chart: a meromorphic section generates there

Let `X` be an algebraic space over a scheme `S` satisfying the two standing hypotheses of
Stacks 0EN6, let `V` be an étale chart of `X` whose scheme is integral, affine, normal and
locally Noetherian, and let `t` be a meromorphic section of an `𝒪_X`-module `ℒ` which is free
over `V` on the compatible family `e`. The ratio of `t` against `e` is
`AlgebraicGeometry.Space.chartRatio`, a meromorphic function on `V`, which Stacks 0EN6, part (2)
reads as a rational function of the chart scheme.

This file carries the step of the proof of Stacks 0EPX that **turns the order-of-vanishing
information into a trivialization**: if that rational function has order of vanishing zero at
every codimension-one point of the chart, then it is a *unit* regular function there, by
algebraic Hartogs applied to it and to its inverse; and then `t` is a unit multiple of `e` over
`V`, so `t` generates `ℒ` over `V` in the sense of
`AlgebraicGeometry.Space.GeneratesOnChart`.

Nothing here is about a prime divisor: the order-of-vanishing hypothesis is at the points of the
chart scheme, which is where
`AlgebraicGeometry.Space.PrimeDivisor.ord_chart_eq_zero_of_isUnit_of_etaleFractionRing_eq`
delivers it.

## Main results

* `AlgebraicGeometry.Space.generatesOnChart_of_chartRatio_eq_algebraMap`: a meromorphic section
  whose ratio against a free generator over a chart is the image of a *unit* regular function
  generates the module over that chart. The witnessing generator is the unit times `e`.
* `AlgebraicGeometry.Space.exists_isUnit_chartRatio_of_forall_ord_eq_zero`: **algebraic Hartogs
  on the chart.** A nonzero chart ratio whose order of vanishing is zero at every
  codimension-one point of an integral affine normal locally Noetherian chart is the image of a
  unit regular function.
* `AlgebraicGeometry.Space.generatesOnChart_of_forall_ord_eq_zero`: the two combined — the form
  the proof of Stacks 0EPX consumes.

## Implementation notes

Hartogs is applied twice, to the rational function and to its inverse, exactly as in
`Stacks.AlgebraicGeometry.UnitsBoundaryValuations.boundaryOrd_eq_zero_iff`: the two global
sections obtained multiply to a global section with germ `1` at the generic point, and the germ
of an integral scheme is injective, so that product is `1` and the first section is a unit. The
order of vanishing of the inverse is zero because `AlgebraicGeometry.Scheme.ord_mul` makes the
two orders add to the order of `1`, which is zero by
`AlgebraicGeometry.Scheme.ord_of_isUnit`.

The hypothesis `hne` that the chart ratio is nonzero is not redundant and is not derived here.
It is the content at this chart of regularity of the section — over a chart carrying a free
generator, multiplication by the section is injective exactly when the ratio is a nonzerodivisor
of `𝒦_X(V)`, which on an integral chart means nonzero;
`AlgebraicGeometry.Space.PrimeDivisor.mem_nonZeroDivisors_genericStalkCoefficient` is that
statement at the chart `Spec(𝒪_{U, u})` of a prime divisor. A consumer holding
`AlgebraicGeometry.Space.IsRegularMeromorphicSection` supplies it there.

Affineness of the chart is needed only for the identification of `𝒦_X(V)` with the function
field (Stacks 0EN6, part (2) is a statement about an affine chart); Hartogs itself needs no
affineness.

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
    (X : AlgebraicSpaces B S hS) (L : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS X.1)
    (e : (W : SmallEtale B S hS X.1) → (W ⟶ V) → L.val.obj (op W))
    (hcompat : ∀ (W W' : SmallEtale B S hS X.1) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hfree : ∀ (W : SmallEtale B S hS X.1) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X.1 X.2 W ↦ r • e W k)
    (t : MeromorphicSection.{u, u} B S hS X.1 X.2 L)

/-- **A unit ratio against a free generator makes the section a generator.** If the ratio of `t`
against the free generator `e` over the chart `V` is the image of a unit regular function `y` on
`V`, then `t` generates `ℒ` over `V`: the witnessing family is `y · e`, again free because `y`
is a unit, and the ratio of `t` against *it* is `1`.

This is the second half of the step of the proof of Stacks 0EPX that algebraic Hartogs produces,
and it is the construction already made inside
`AlgebraicGeometry.Space.exists_generatesOnChart_of_isRegularMeromorphicSection` for a unit
coefficient arising for a different reason, isolated so that the Hartogs route can use it. -/
theorem generatesOnChart_of_chartRatio_eq_algebraMap
    (y : chartRing B S hS X.1 X.2 V) (hyu : IsUnit y)
    (hy : chartRatio B S hS X.1 X.2 L V e hcompat hfree t =
      algebraMap (chartRing B S hS X.1 X.2 V)
        ((meromorphicChartSheaf B S hS X.1 X.2).obj.obj (op V)) y) :
    GeneratesOnChart B S hS X.2 L t V := by
  refine ⟨fun Z j ↦ chartRestrict (hF := X.2) j y • e Z j, ?_, ?_, ?_⟩
  · intro Z Z' j g
    change (L.val.map g.op).hom (chartRestrict (hF := X.2) j y • e Z j) =
      chartRestrict (hF := X.2) (g ≫ j) y • e Z' (g ≫ j)
    refine Eq.trans
      (L.val.map_smul g.op (chartRestrict (hF := X.2) j y) (e Z j)) ?_
    rw [hcompat Z Z' j g]
    exact congrArg (fun v : chartRing B S hS X.1 X.2 Z' ↦ v • e Z' (g ≫ j))
      (DFunLike.congr_fun (chartRestrict_comp (hF := X.2) j g) y).symm
  · intro Z j
    change Function.Bijective fun r : chartRing B S hS X.1 X.2 Z ↦
      r • (chartRestrict (hF := X.2) j y • e Z j)
    have huZ : IsUnit (chartRestrict (hF := X.2) j y) := hyu.map (chartRestrict (hF := X.2) j)
    have hmul : Function.Bijective
        fun r : chartRing B S hS X.1 X.2 Z ↦ r * chartRestrict (hF := X.2) j y :=
      IsUnit.isUnit_iff_mulRight_bijective.mp huZ
    have heq : (fun r : chartRing B S hS X.1 X.2 Z ↦
          r • (chartRestrict (hF := X.2) j y • e Z j)) =
        (fun w : chartRing B S hS X.1 X.2 Z ↦ w • e Z j) ∘
          fun r : chartRing B S hS X.1 X.2 Z ↦ r * chartRestrict (hF := X.2) j y :=
      funext fun r ↦ smul_smul r (chartRestrict (hF := X.2) j y) (e Z j)
    rw [heq]
    exact (hfree Z j).comp hmul
  · change t.eval (op V) = toMeromorphicSectionSheaf B S hS X.1 X.2 L V
      ((1 : (Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS X.1 X.2).O).obj.obj (op V)) ⊗ₜ[
        chartRing B S hS X.1 X.2 V] (chartRestrict (hF := X.2) (𝟙 V) y • e V (𝟙 V)) :
        (meromorphicSectionModule B S hS X.1 X.2 L).obj (op V))
    have hidr : chartRestrict (hF := X.2) (𝟙 V) y = y :=
      DFunLike.congr_fun (chartRestrict_id (hF := X.2) V) y
    rw [hidr]
    refine Eq.trans
      (eval_eq_toMeromorphicSectionSheaf_tmul_chartRatio B S hS X.1 X.2 L V e hcompat hfree t) ?_
    refine congrArg (toMeromorphicSectionSheaf B S hS X.1 X.2 L V) ?_
    refine Eq.trans (congrArg
      (fun w : (Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS X.1 X.2).O).obj.obj (op V) ↦
        (w ⊗ₜ[chartRing B S hS X.1 X.2 V] e V (𝟙 V) :
          (meromorphicSectionModule B S hS X.1 X.2 L).obj (op V)))
      (hy.trans (mul_one (algebraMap (chartRing B S hS X.1 X.2 V)
        ((meromorphicChartSheaf B S hS X.1 X.2).obj.obj (op V)) y)).symm))
      (meromorphicSectionModule_tmul_smul B S hS X.1 X.2 L V y 1 (e V (𝟙 V))).symm

variable (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)

open Stacks.AlgebraicGeometry.UnitsNormalProper in
/-- **Algebraic Hartogs on an étale chart.** On an integral, affine, normal, locally Noetherian
étale chart `V` of `X`, a nonzero ratio of a meromorphic section against a free generator whose
order of vanishing is zero at every codimension-one point of the chart scheme is the image of a
unit regular function on `V`.

Hartogs
(`Stacks.AlgebraicGeometry.UnitsNormalProper.exists_globalSection_of_forall_ord_eq_zero`) is
applied to the rational function and to its inverse; the two global sections it produces multiply
to a global section whose germ at the generic point is `1`, and the germ of an integral scheme is
injective, so their product is `1`. -/
theorem exists_isUnit_chartRatio_of_forall_ord_eq_zero
    [AlgebraicGeometry.IsIntegral (chartScheme V)]
    [IsLocallyNoetherian (chartScheme V)]
    [AlgebraicGeometry.IsNormal (chartScheme V)]
    (hV : IsAffine (chartScheme V))
    (hne : chartRatio B S hS X.1 X.2 L V e hcompat hfree t ≠ 0)
    (h0 : ∀ z : chartScheme V, coheight z = 1 →
      (chartScheme V).ord (chartMeromorphicFunctionFieldEquiv B S hS X hwa hfin V hV
        (chartRatio B S hS X.1 X.2 L V e hcompat hfree t)) z = 0) :
    ∃ y : chartRing B S hS X.1 X.2 V, IsUnit y ∧
      chartRatio B S hS X.1 X.2 L V e hcompat hfree t =
        algebraMap (chartRing B S hS X.1 X.2 V)
          ((meromorphicChartSheaf B S hS X.1 X.2).obj.obj (op V)) y := by
  have hz0 : chartMeromorphicFunctionFieldEquiv B S hS X hwa hfin V hV
      (chartRatio B S hS X.1 X.2 L V e hcompat hfree t) ≠ 0 := fun h =>
    hne ((chartMeromorphicFunctionFieldEquiv B S hS X hwa hfin V hV).injective
      (h.trans (map_zero _).symm))
  have hone : ∀ z : chartScheme V,
      (chartScheme V).ord (1 : ↥(chartScheme V).functionField) z = 0 := fun z =>
    (congrArg (fun w : ↥(chartScheme V).functionField ↦ (chartScheme V).ord w z)
      (map_one ((chartScheme V).germToFunctionField ⊤).hom).symm).trans
      (Scheme.ord_of_isUnit (U := ⊤) isUnit_one trivial)
  have h0inv : ∀ z : chartScheme V, coheight z = 1 →
      (chartScheme V).ord (chartMeromorphicFunctionFieldEquiv B S hS X hwa hfin V hV
        (chartRatio B S hS X.1 X.2 L V e hcompat hfree t))⁻¹ z = 0 := by
    intro z hz
    have hsum := Scheme.ord_mul (X := chartScheme V) (x := z) hz0 (inv_ne_zero hz0)
    rw [mul_inv_cancel₀ hz0, h0 z hz, zero_add] at hsum
    exact hsum.symm.trans (hone z)
  obtain ⟨a, ha⟩ := exists_globalSection_of_forall_ord_eq_zero (X := chartScheme V) hz0 h0
  obtain ⟨b, hb⟩ :=
    exists_globalSection_of_forall_ord_eq_zero (X := chartScheme V) (inv_ne_zero hz0) h0inv
  have hab : a * b = 1 := by
    refine germ_injective_of_isIntegral (X := chartScheme V) (U := ⊤)
      (genericPoint (chartScheme V)) trivial ?_
    rw [map_mul, ha, hb, map_one, mul_inv_cancel₀ hz0]
  refine ⟨a, IsUnit.of_mul_eq_one b hab,
    (chartMeromorphicFunctionFieldEquiv B S hS X hwa hfin V hV).injective ?_⟩
  refine ha.symm.trans ?_
  exact (chartMeromorphicFunctionFieldEquiv_algebraMap B S hS X hwa hfin V hV a).symm

/-- **The step of the proof of Stacks 0EPX that algebraic Hartogs provides.** On an integral,
affine, normal, locally Noetherian étale chart `V` of `X` over which `ℒ` is free on `e`, a
meromorphic section whose nonzero ratio against `e` has order of vanishing zero at every
codimension-one point of the chart scheme generates `ℒ` over `V`.

This is
`AlgebraicGeometry.Space.exists_isUnit_chartRatio_of_forall_ord_eq_zero` followed by
`AlgebraicGeometry.Space.generatesOnChart_of_chartRatio_eq_algebraMap`. What the proof of Stacks
0EPX still owes between the unit hypothesis at the generic points of the prime divisors and this
is the identification of the two ratios, which supplies `h0` through
`AlgebraicGeometry.Space.PrimeDivisor.ord_chart_eq_zero_of_isUnit_of_etaleFractionRing_eq`. -/
theorem generatesOnChart_of_forall_ord_eq_zero
    [AlgebraicGeometry.IsIntegral (chartScheme V)]
    [IsLocallyNoetherian (chartScheme V)]
    [AlgebraicGeometry.IsNormal (chartScheme V)]
    (hV : IsAffine (chartScheme V))
    (hne : chartRatio B S hS X.1 X.2 L V e hcompat hfree t ≠ 0)
    (h0 : ∀ z : chartScheme V, coheight z = 1 →
      (chartScheme V).ord (chartMeromorphicFunctionFieldEquiv B S hS X hwa hfin V hV
        (chartRatio B S hS X.1 X.2 L V e hcompat hfree t)) z = 0) :
    GeneratesOnChart B S hS X.2 L t V :=
  let ⟨y, hyu, hy⟩ := exists_isUnit_chartRatio_of_forall_ord_eq_zero B S hS X L V e hcompat
    hfree t hwa hfin hV hne h0
  generatesOnChart_of_chartRatio_eq_algebraMap B S hS X L V e hcompat hfree t y hyu hy

/-! ### The nonvanishing of the ratio, from regularity of the section -/

include hwa hfin in
/-- **A regular meromorphic section has nonzero ratio against a free generator over an integral
affine chart.** This is the hypothesis `hne` of
`AlgebraicGeometry.Space.generatesOnChart_of_forall_ord_eq_zero`, discharged from
`AlgebraicGeometry.Space.IsRegularMeromorphicSection`.

If the ratio were zero then every multiple of `t` over `V` would be the image of `0 ⊗ e`, so
multiplication by `t` on `𝒦_X(V)` would be a constant map; regularity of `t` says that map is
injective, which forces `1 = 0` in `𝒦_X(V)`. But over an integral affine chart `𝒦_X(V)` is the
function field of the chart scheme by Stacks 0EN6, part (2)
(`AlgebraicGeometry.Space.chartMeromorphicFunctionFieldEquiv`), and that is a field. -/
theorem chartRatio_ne_zero_of_isRegularMeromorphicSection
    [AlgebraicGeometry.IsIntegral (chartScheme V)] (hV : IsAffine (chartScheme V))
    (hreg : IsRegularMeromorphicSection.{u, u} B S hS X.1 X.2 L t) :
    chartRatio B S hS X.1 X.2 L V e hcompat hfree t ≠ 0 := by
  intro h
  have hconst : ∀ r : (Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS X.1 X.2).O).obj.obj (op V),
      r • t.eval (op V) = toMeromorphicSectionSheaf B S hS X.1 X.2 L V
        ((0 : (Stacks.SheafOfModules.Tensor.ringSheaf
            (meromorphicRingedSite B S hS X.1 X.2).O).obj.obj (op V))
          ⊗ₜ[chartRing B S hS X.1 X.2 V] e V (𝟙 V)) := by
    intro r
    refine Eq.trans (congrArg
      (fun z : (meromorphicSectionSheaf.{u, u} B S hS X.1 X.2 L).val.obj (op V) ↦ r • z)
      (eval_eq_toMeromorphicSectionSheaf_tmul_chartRatio B S hS X.1 X.2 L V e hcompat
        hfree t)) ?_
    refine Eq.trans (toMeromorphicSectionSheaf_smul B S hS X.1 X.2 L V r
      (chartRatio B S hS X.1 X.2 L V e hcompat hfree t ⊗ₜ[chartRing B S hS X.1 X.2 V]
          e V (𝟙 V) :
        (meromorphicSectionModule B S hS X.1 X.2 L).obj (op V))).symm ?_
    refine congrArg (toMeromorphicSectionSheaf B S hS X.1 X.2 L V) ?_
    refine (meromorphicSectionModule_smul_tmul B S hS X.1 X.2 L V _ r
      (chartRatio B S hS X.1 X.2 L V e hcompat hfree t) (e V (𝟙 V)) rfl).trans ?_
    exact congrArg (fun z : (Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS X.1 X.2).O).obj.obj (op V) ↦
      (z ⊗ₜ[chartRing B S hS X.1 X.2 V] e V (𝟙 V) :
        (meromorphicSectionModule B S hS X.1 X.2 L).obj (op V)))
      (by rw [h, mul_zero])
  have hone : (1 : (Stacks.SheafOfModules.Tensor.ringSheaf
      (meromorphicRingedSite B S hS X.1 X.2).O).obj.obj (op V)) = 0 :=
    hreg V ((hconst 1).trans (hconst 0).symm)
  have hequiv := chartMeromorphicFunctionFieldEquiv B S hS X hwa hfin V hV
  exact one_ne_zero (α := ↥(chartScheme V).functionField)
    (((map_one hequiv).symm.trans (congrArg hequiv hone)).trans (map_zero hequiv))

end AlgebraicGeometry.Space

end
