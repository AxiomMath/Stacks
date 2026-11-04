module

public import Mathlib.AlgebraicGeometry.FunctionField
public import StacksFrontier.AlgebraicGeometry.Curves.InseparableGenusChangeCurveDimension
public import StacksFrontier.RingTheory.AdjoinRoot.FractionRing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The function field of the curve of [Stacks, Tag 0CD1] is `k(x)[y] ⧸ (y³ - x² - a)`

`StacksFrontier/AlgebraicGeometry/Curves/InseparableGenusChangeCurve.lean` and
`StacksFrontier/AlgebraicGeometry/Curves/InseparableGenusChangeCurveDimension.lean` construct the
nonsingular plane cubic `Z = Proj (k[T₀, T₁, T₂] ⧸ (F))`, `F = T₁²T₀ - T₂³ + aT₀³`, of
[Stacks, Tag 0CD1], and
`StacksFrontier/AlgebraicGeometry/Curves/InseparableGenusChange.lean` states the purely inseparable
degree-three extension of the example as the abstract field
`Stacks.Curves.InseparableGenus.curveFunctionField k a = k(x)[y] ⧸ (y³ - x² - a)`. This file
**identifies the two**: the function field of the constructed curve *is* that field, and the
identification is the one the chart `Z ∩ D₊(T₀)` prescribes.

## Main results

* `AlgebraicGeometry.isReduced_of_isRegular` and
  `AlgebraicGeometry.isIntegral_of_isRegular`: a regular scheme is reduced, hence integral when
  irreducible. The argument — regular implies normal implies local rings are domains — was
  written out only inside a proof, in
  `StacksFrontier/AlgebraicGeometry/Variety/Curve/RegularCompactification.lean`.
* `AlgebraicGeometry.IsAffineOpen.nonempty_of_nontrivial`: an affine open whose ring of functions
  is nonzero is nonempty.
* `Stacks.Curves.InseparableGenus.isFractionRing_sections_functionField_planeCubicCurve`: **the
  function field of the curve is the fraction field of the chart ring `Γ(Z, Z ∩ D₊(T₀))`.**
* `Stacks.Curves.InseparableGenus.isFractionRing_planeCubicChart_curveFunctionField`:
  **`k(x)[y] ⧸ (y³ - x² - a)` is the fraction field of `k[Y₀, Y₁] ⧸ (Y₀² - Y₁³ + a)`**, for the
  embedding `Y₀ ↦ x`, `Y₁ ↦ y`.
* `Stacks.Curves.InseparableGenus.functionFieldEquivCurveFunctionField`: the resulting
  identification `Z.functionField ≅ k(x)[y] ⧸ (y³ - x² - a)`, pinned down on the chart by
  `functionFieldEquivCurveFunctionField_algebraMap`.
* `Stacks.Curves.InseparableGenus.isPurelyInseparable_and_finrank_functionField_planeCubicCurve`:
  **the function field of the curve is purely inseparable of degree three over `k(x)`**, for the
  embedding of `k(x)` which the chart coordinate `x = T₁/T₀` gives.

## Implementation notes

**The function field on an affine open.** No new general statement is needed for this: Mathlib's
`AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen` already says that the function
field of an integral scheme is a fraction field of the sections on *any* nonempty affine open.
What the curve needs supplied is that it is integral — it is regular, hence normal, hence has
domains for local rings — and that the chart `Z ∩ D₊(T₀)` is nonempty, which holds because its
ring of functions `k[Y₀, Y₁] ⧸ (Y₀² - Y₁³ + a)` is nonzero, the equation not being a unit.

**The algebra.** `Stacks.AdjoinRootFraction.isFractionRing_adjoinRoot` is the general statement
that adjoining a root of a monic polynomial commutes with passing to the fraction field of the
coefficient ring. The chart ring is `k[Y₀][Y₁] ⧸ (Y₁³ - (Y₀² + a))`, so over `k(Y₀) = k(x)` it
becomes `k(x)[y] ⧸ (y³ - (x² + a))`, which is a field because `x² + a` is not a cube in `k(x)` —
an `x`-degree count, and the same input that made the extension of the example degree three.
Reading `k[Y₀, Y₁]` as `k[Y₀][Y₁]` is `Stacks.Curves.InseparableGenus.bivariateEquiv` composed
with the swap of the two variables, since that equivalence puts the *first* variable outside.

## Not done here

The coordinate projection `f : Z ⟶ 𝐏¹_k` of the example is **not** used: the embedding of `k(x)`
above comes from the chart coordinate `T₁/T₀`, not from
`AlgebraicGeometry.dominantFunctionFieldMap f`. That the two agree is
`Stacks.Curves.InseparableGenus.projectionRatFuncAlgebra_eq_chartRatFuncAlgebra`, in
`StacksFrontier/AlgebraicGeometry/Curves/InseparableGenusChangeProjectionEmbedding.lean`, which
needs `f` read on the sections of this chart and so the whole of
`StacksFrontier/AlgebraicGeometry/ProjTwistChain/Sections.lean`.

## References

* [Stacks Project, Tag 0CD1](https://stacks.math.columbia.edu/tag/0CD1)
* [Stacks Project, Tag 02IS](https://stacks.math.columbia.edu/tag/02IS)
* [Stacks Project, Tag 0569](https://stacks.math.columbia.edu/tag/0569)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProjectiveSpectrum.Proj (idealOfClosedSubscheme)
open Stacks.ProjectiveChart (dehomCoeff subschemeChart chartQuotientEquiv
  isAffineOpen_subschemeChart)

universe u

/-! ### A regular scheme is reduced, and integral when irreducible -/

/-- **A regular scheme is reduced.** A regular scheme is normal, so its local rings are domains.
-/
theorem AlgebraicGeometry.isReduced_of_isRegular {X : Scheme.{u}} (hX : IsRegular X) :
    IsReduced X := by
  have hnormal : IsNormal X := isNormal_of_isRegular X hX
  let hstalk : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    let : IsDomain (X.presheaf.stalk x) := hnormal.stalk_isDomain x
    infer_instance
  exact isReduced_of_isReduced_stalk X

/-- **An irreducible regular scheme is integral.** -/
theorem AlgebraicGeometry.isIntegral_of_isRegular {X : Scheme.{u}} [IrreducibleSpace X]
    (hX : IsRegular X) : IsIntegral X :=
  let := isReduced_of_isRegular hX
  isIntegral_of_irreducibleSpace_of_isReduced X

/-- **An affine open with a nonzero ring of functions is nonempty.** -/
theorem AlgebraicGeometry.IsAffineOpen.nonempty_of_nontrivial {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) [Nontrivial Γ(X, U)] : Nonempty U := by
  obtain ⟨p⟩ : Nonempty (Spec Γ(X, U)) := inferInstance
  exact ⟨⟨hU.fromSpec.base p, hU.range_fromSpec.subset ⟨p, rfl⟩⟩⟩

namespace Stacks.Curves.InseparableGenus

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### The chart of the curve on `D₊(T₀)` -/

/-- **The affine coordinate ring of the curve of [Stacks, Tag 0CD1] on `D₊(T₀)`**:
`k[Y₀, Y₁] ⧸ (Y₀² - Y₁³ + a)`, the dehomogenization of `F = T₁²T₀ - T₂³ + aT₀³` at `T₀ = 1`. -/
@[ega "IV 6.7.5"]
abbrev planeCubicChart (k : Type u) [Field k] (a : k) : Type u :=
  MvPolynomial (Fin 2) k ⧸
    Ideal.span {MvPolynomial.X 0 ^ 2 - MvPolynomial.X 1 ^ 3 + MvPolynomial.C a}

/-- **The chart `Z ∩ D₊(T₀)` of the curve has `k[Y₀, Y₁] ⧸ (Y₀² - Y₁³ + a)` as its ring of
functions**, by `Stacks.ProjectiveChart.chartQuotientEquiv` at the explicit curve. -/
def planeCubicChartEquiv (k : Type u) [Field k] (a : k) :
    planeCubicChart k a ≃+*
      Γ(planeCubicCurve k a, subschemeChart (planeCubicEmbedding k a) 0) :=
  (Ideal.quotEquivOfEq (by rw [dehomCoeff_planeCubic_zero])).trans
    (chartQuotientEquiv (planeCubicEmbedding k a) 0 (planeCubic k a)
      (planeCubic_mem_homogeneousSubmodule_smul k a)
      (idealOfClosedSubscheme_planeCubicEmbedding k a))

/-- The affine equation of the curve on `D₊(T₀)` is not a unit, so the chart ring is nonzero. -/
instance nontrivial_planeCubicChart (k : Type u) [Field k] (a : k) :
    Nontrivial (planeCubicChart k a) := by
  refine Ideal.Quotient.nontrivial_iff.mpr fun h => ?_
  rw [← dehomCoeff_planeCubic_zero, Ideal.span_singleton_eq_top] at h
  exact (dehomCoeff_planeCubic_ne_zero_and_not_isUnit k a (Or.inl rfl)).2 h

/-- The ring of functions on the chart `Z ∩ D₊(T₀)` of the curve is nonzero. -/
instance nontrivial_sections_subschemeChart_zero (k : Type u) [Field k] (a : k) :
    Nontrivial Γ(planeCubicCurve k a, subschemeChart (planeCubicEmbedding k a) 0) :=
  (planeCubicChartEquiv k a).symm.toEquiv.nontrivial

/-- **The chart `Z ∩ D₊(T₀)` of the curve is nonempty.** -/
instance nonempty_subschemeChart_zero (k : Type u) [Field k] (a : k) :
    Nonempty (subschemeChart (planeCubicEmbedding k a) 0) :=
  (isAffineOpen_subschemeChart (planeCubicEmbedding k a) 0).nonempty_of_nontrivial

/-! ### The curve is integral -/

/-- **The curve of [Stacks, Tag 0CD1] is integral**: it is irreducible, and reduced because it is
regular. -/
theorem isIntegral_planeCubicCurve (k : Type u) [Field k] [ExpChar k 3] (a : k)
    (ha : ∀ b : k, b ^ 3 ≠ a) : AlgebraicGeometry.IsIntegral (planeCubicCurve k a) :=
  AlgebraicGeometry.isIntegral_of_isRegular (isRegular_planeCubicCurve k a ha)

/-! ### The function field of the curve -/

/-- **The function field of the curve of [Stacks, Tag 0CD1] is the fraction field of its chart
ring on `D₊(T₀)`.** -/
theorem isFractionRing_sections_functionField_planeCubicCurve (k : Type u) [Field k] [ExpChar k 3]
    (a : k) (ha : ∀ b : k, b ^ 3 ≠ a) :
    letI := isIntegral_planeCubicCurve k a ha
    IsFractionRing Γ(planeCubicCurve k a, subschemeChart (planeCubicEmbedding k a) 0)
      (planeCubicCurve k a).functionField :=
  let := isIntegral_planeCubicCurve k a ha
  AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen _ _
    (isAffineOpen_subschemeChart (planeCubicEmbedding k a) 0)

/-! ### The chart ring is `k[Y₀]` with a cube root of `Y₀² + a` adjoined -/

/-- `k[Y₀, Y₁]` read as `k[Y₀][Y₁]`, with `Y₁` as the polynomial variable: this is
`Stacks.Curves.InseparableGenus.bivariateEquiv` after the swap of the two variables, which puts
`Y₀` into the coefficient ring. -/
def bivariateEquivSwap (k : Type u) [CommRing k] :
    MvPolynomial (Fin 2) k ≃+* Polynomial (Polynomial k) :=
  (MvPolynomial.renameEquiv k (Equiv.swap (0 : Fin 2) 1)).toRingEquiv.trans (bivariateEquiv k)

/-- `bivariateEquivSwap` is `bivariateEquiv` applied after swapping the two variables. -/
theorem bivariateEquivSwap_apply (k : Type u) [CommRing k] (x : MvPolynomial (Fin 2) k) :
    bivariateEquivSwap k x =
      bivariateEquiv k (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) x) := rfl

/-- `bivariateEquivSwap` sends the constant `r` to the constant `C (C r)`. -/
@[simp] theorem bivariateEquivSwap_C (k : Type u) [CommRing k] (r : k) :
    bivariateEquivSwap k (MvPolynomial.C r) = Polynomial.C (Polynomial.C r) := by
  rw [bivariateEquivSwap_apply, MvPolynomial.rename_C, bivariateEquiv_C]

/-- `bivariateEquivSwap` sends `Y₀` to the coefficient `C X`. -/
@[simp] theorem bivariateEquivSwap_X_zero (k : Type u) [CommRing k] :
    bivariateEquivSwap k (MvPolynomial.X 0) = Polynomial.C Polynomial.X := by
  rw [bivariateEquivSwap_apply, MvPolynomial.rename_X, Equiv.swap_apply_left,
    bivariateEquiv_X_one]

/-- `bivariateEquivSwap` sends `Y₁` to the polynomial variable `X`. -/
@[simp] theorem bivariateEquivSwap_X_one (k : Type u) [CommRing k] :
    bivariateEquivSwap k (MvPolynomial.X 1) = Polynomial.X := by
  rw [bivariateEquivSwap_apply, MvPolynomial.rename_X, Equiv.swap_apply_right,
    bivariateEquiv_X_zero]

/-- **The affine equation of the curve on `D₊(T₀)` as a monic cubic in `Y₁` over `k[Y₀]`**:
`Y₁³ - (Y₀² + a)`. -/
def chartCubic (k : Type u) [CommRing k] (a : k) : Polynomial (Polynomial k) :=
  Polynomial.X ^ 3 - Polynomial.C (Polynomial.X ^ 2 + Polynomial.C a)

/-- The chart cubic `Y₁³ - (Y₀² + a)` is monic in `Y₁`. -/
theorem monic_chartCubic (k : Type u) [CommRing k] (a : k) : (chartCubic k a).Monic :=
  Polynomial.monic_X_pow_sub_C _ (by decide)

/-- Over `k(x)` the chart cubic is the polynomial `Y³ - (x² + a)` whose root generates
`Stacks.Curves.InseparableGenus.curveFunctionField`. -/
theorem map_chartCubic (k : Type u) [Field k] (a : k) :
    (Polynomial.X ^ 3 - Polynomial.C (RatFunc.X ^ 2 + RatFunc.C a) : Polynomial (RatFunc k)) =
      (chartCubic k a).map (algebraMap (Polynomial k) (RatFunc k)) := by
  have h : algebraMap (Polynomial k) (RatFunc k) (Polynomial.X ^ 2 + Polynomial.C a) =
      RatFunc.X ^ 2 + RatFunc.C a := by
    rw [map_add, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  rw [chartCubic, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, h]

/-- **The chart ring of the curve on `D₊(T₀)` is `k[Y₀]` with a cube root of `Y₀² + a`
adjoined.** -/
def planeCubicChartEquivAdjoinRoot (k : Type u) [Field k] (a : k) :
    planeCubicChart k a ≃+* AdjoinRoot (chartCubic k a) := by
  have hneg : bivariateEquivSwap k
      (MvPolynomial.X 0 ^ 2 - MvPolynomial.X 1 ^ 3 + MvPolynomial.C a) = -chartCubic k a := by
    simp only [map_add, map_sub, map_pow, bivariateEquivSwap_C, bivariateEquivSwap_X_zero,
      bivariateEquivSwap_X_one, chartCubic]
    ring
  refine Ideal.quotientEquiv _ (Ideal.span {chartCubic k a}) (bivariateEquivSwap k) ?_
  rw [Ideal.map_span, Set.image_singleton, RingEquiv.coe_toRingHom, hneg]
  exact le_antisymm (Ideal.span_singleton_le_span_singleton.mpr (neg_dvd.mpr dvd_rfl))
    (Ideal.span_singleton_le_span_singleton.mpr (dvd_neg.mpr dvd_rfl))

/-- On the chart the presentation is the substitution `Y₀ ↦ Y₀`, `Y₁ ↦ y` read modulo the
cubic. -/
theorem planeCubicChartEquivAdjoinRoot_mk (k : Type u) [Field k] (a : k)
    (x : MvPolynomial (Fin 2) k) :
    planeCubicChartEquivAdjoinRoot k a (Ideal.Quotient.mk _ x) =
      AdjoinRoot.mk (chartCubic k a) (bivariateEquivSwap k x) := rfl

/-- The cubic `Y³ - (x² + a)` is irreducible over `k(x)`: `x² + a` is not a cube there, by a
degree count. -/
instance fact_irreducible_curvePolynomial (k : Type u) [Field k] (a : k) :
    Fact (Irreducible (Polynomial.X ^ 3 - Polynomial.C (RatFunc.X ^ 2 + RatFunc.C a) :
      Polynomial (RatFunc k))) :=
  ⟨X_pow_sub_C_irreducible_of_prime Nat.prime_three (ratFuncX_sq_add_C_not_cube a)⟩

/-- **The chart ring of the curve maps into `k(x)[y] ⧸ (y³ - x² - a)`**, by `Y₀ ↦ x` and
`Y₁ ↦ y`. -/
def planeCubicChartToCurveFunctionField (k : Type u) [Field k] (a : k) :
    planeCubicChart k a →+* curveFunctionField k a :=
  (Stacks.AdjoinRootFraction.toMapAdjoinRoot (RatFunc k) (map_chartCubic k a)).comp
    ((planeCubicChartEquivAdjoinRoot k a : planeCubicChart k a →+* AdjoinRoot (chartCubic k a)))

/-- `k(x)[y] ⧸ (y³ - x² - a)` is an algebra over the chart ring of the curve, via
`planeCubicChartToCurveFunctionField`. -/
instance algebra_planeCubicChart_curveFunctionField (k : Type u) [Field k] (a : k) :
    Algebra (planeCubicChart k a) (curveFunctionField k a) :=
  (planeCubicChartToCurveFunctionField k a).toAlgebra

/-- The chart coordinate `Y₀ = T₁/T₀` becomes the coordinate `x` of `k(x)`. -/
@[simp] theorem planeCubicChartToCurveFunctionField_X_zero (k : Type u) [Field k] (a : k) :
    planeCubicChartToCurveFunctionField k a (Ideal.Quotient.mk _ (MvPolynomial.X 0)) =
      algebraMap (RatFunc k) (curveFunctionField k a) RatFunc.X := by
  rw [planeCubicChartToCurveFunctionField, RingHom.comp_apply, RingEquiv.coe_toRingHom,
    planeCubicChartEquivAdjoinRoot_mk, bivariateEquivSwap_X_zero,
    show (AdjoinRoot.mk (chartCubic k a)) (Polynomial.C Polynomial.X) =
      AdjoinRoot.of (chartCubic k a) Polynomial.X from rfl,
    Stacks.AdjoinRootFraction.toMapAdjoinRoot_of, RatFunc.algebraMap_X,
    AdjoinRoot.algebraMap_eq]

/-- The chart coordinate `Y₁ = T₂/T₀` becomes the adjoined cube root `y` of `x² + a`. -/
@[simp] theorem planeCubicChartToCurveFunctionField_X_one (k : Type u) [Field k] (a : k) :
    planeCubicChartToCurveFunctionField k a (Ideal.Quotient.mk _ (MvPolynomial.X 1)) =
      AdjoinRoot.root _ := by
  rw [planeCubicChartToCurveFunctionField, RingHom.comp_apply, RingEquiv.coe_toRingHom,
    planeCubicChartEquivAdjoinRoot_mk, bivariateEquivSwap_X_one,
    show (AdjoinRoot.mk (chartCubic k a)) Polynomial.X = AdjoinRoot.root (chartCubic k a) from rfl,
    Stacks.AdjoinRootFraction.toMapAdjoinRoot_root]

/-- **`k(x)[y] ⧸ (y³ - x² - a)` is the fraction field of the chart ring of the curve.** This is
`Stacks.AdjoinRootFraction.isFractionRing_adjoinRoot` at the chart cubic. -/
theorem isFractionRing_planeCubicChart_curveFunctionField (k : Type u) [Field k] (a : k) :
    IsFractionRing (planeCubicChart k a) (curveFunctionField k a) :=
  Stacks.AdjoinRootFraction.isFractionRing_adjoinRoot (RatFunc k) (map_chartCubic k a)
    (planeCubicChartEquivAdjoinRoot k a) (monic_chartCubic k a)
    (RingHom.algebraMap_toAlgebra _)

/-! ### The function field of the curve -/

/-- **The function field of the curve of [Stacks, Tag 0CD1] is `k(x)[y] ⧸ (y³ - x² - a)`.** Both
sides are fraction fields of the chart ring `k[Y₀, Y₁] ⧸ (Y₀² - Y₁³ + a)`: the function field by
`isFractionRing_sections_functionField_planeCubicCurve`, and `k(x)[y] ⧸ (y³ - x² - a)` by
`isFractionRing_planeCubicChart_curveFunctionField`. -/
def functionFieldEquivCurveFunctionField (k : Type u) [Field k] [ExpChar k 3] (a : k)
    (ha : ∀ b : k, b ^ 3 ≠ a) :
    (planeCubicCurve k a).functionField ≃+* curveFunctionField k a :=
  letI := isIntegral_planeCubicCurve k a ha
  letI := isFractionRing_sections_functionField_planeCubicCurve k a ha
  letI := isFractionRing_planeCubicChart_curveFunctionField k a
  IsFractionRing.ringEquivOfRingEquiv (planeCubicChartEquiv k a).symm

/-- **The identification of the function field is the one the chart prescribes**: a function on
`Z ∩ D₊(T₀)` goes to its own image in `k(x)[y] ⧸ (y³ - x² - a)`. With
`planeCubicChartToCurveFunctionField_X_zero` and
`planeCubicChartToCurveFunctionField_X_one` this says that the germ of the coordinate
`Y₀ = T₁/T₀` is `x` and the germ of `Y₁ = T₂/T₀` is `y`. -/
theorem functionFieldEquivCurveFunctionField_algebraMap (k : Type u) [Field k] [ExpChar k 3]
    (a : k) (ha : ∀ b : k, b ^ 3 ≠ a) (x : planeCubicChart k a) :
    functionFieldEquivCurveFunctionField k a ha
        (algebraMap Γ(planeCubicCurve k a, subschemeChart (planeCubicEmbedding k a) 0)
          (planeCubicCurve k a).functionField (planeCubicChartEquiv k a x)) =
      planeCubicChartToCurveFunctionField k a x := by
  let := isIntegral_planeCubicCurve k a ha
  let := isFractionRing_sections_functionField_planeCubicCurve k a ha
  let := isFractionRing_planeCubicChart_curveFunctionField k a
  have h := IsFractionRing.ringEquivOfRingEquiv_algebraMap
    (K := (planeCubicCurve k a).functionField) (L := curveFunctionField k a)
    (planeCubicChartEquiv k a).symm (planeCubicChartEquiv k a x)
  rw [RingEquiv.symm_apply_apply] at h
  exact h

/-- **The embedding of `k(x)` into the function field of the curve given by the chart**: `x` is
the coordinate `Y₀ = T₁/T₀` of `Z ∩ D₊(T₀)`, read in the function field.

This embedding is also the one the coordinate projection `f : Z ⟶ 𝐏¹_k` induces on function
fields, by `Stacks.Curves.InseparableGenus.projectionRatFuncAlgebra_eq_chartRatFuncAlgebra`. -/
@[instance_reducible] def chartRatFuncAlgebra (k : Type u) [Field k] [ExpChar k 3] (a : k)
    (ha : ∀ b : k, b ^ 3 ≠ a) :
    Algebra (RatFunc k) (planeCubicCurve k a).functionField :=
  (((functionFieldEquivCurveFunctionField k a ha).symm :
      curveFunctionField k a →+* (planeCubicCurve k a).functionField).comp
    (algebraMap (RatFunc k) (curveFunctionField k a))).toAlgebra

/-- **The function field of the curve of [Stacks, Tag 0CD1] is a purely inseparable extension of
`k(x)` of degree three**, for the embedding of `k(x)` given by the chart coordinate `x = T₁/T₀`.

This is `Stacks.Curves.InseparableGenus.isPurelyInseparable_and_finrank_curveFunctionField`
transported along `functionFieldEquivCurveFunctionField`, which is where the geometry enters: the
function field of the explicitly constructed curve really is `k(x)[y] ⧸ (y³ - x² - a)`.

**Which embedding.** The embedding of `k(x)` is the one the chart `Z ∩ D₊(T₀)` gives. It is also
the one the coordinate projection `f : Z ⟶ 𝐏¹_k` induces on function fields, by
`Stacks.Curves.InseparableGenus.projectionRatFuncAlgebra_eq_chartRatFuncAlgebra`, but that is a
separate statement and lives in
`StacksFrontier/AlgebraicGeometry/Curves/InseparableGenusChangeProjectionEmbedding.lean`. -/
theorem isPurelyInseparable_and_finrank_functionField_planeCubicCurve (k : Type u) [Field k]
    [ExpChar k 3] (a : k) (ha : ∀ b : k, b ^ 3 ≠ a) :
    letI := isIntegral_planeCubicCurve k a ha
    letI := chartRatFuncAlgebra k a ha
    IsPurelyInseparable (RatFunc k) (planeCubicCurve k a).functionField ∧
      Module.finrank (RatFunc k) (planeCubicCurve k a).functionField = 3 := by
  let := isIntegral_planeCubicCurve k a ha
  let := chartRatFuncAlgebra k a ha
  obtain ⟨hins, hrank⟩ := isPurelyInseparable_and_finrank_curveFunctionField k a
  let := hins
  let e : curveFunctionField k a ≃ₐ[RatFunc k] (planeCubicCurve k a).functionField :=
    AlgEquiv.ofRingEquiv (f := (functionFieldEquivCurveFunctionField k a ha).symm)
      fun _ => rfl
  exact ⟨e.isPurelyInseparable, by rw [← e.toLinearEquiv.finrank_eq]; exact hrank⟩

end Stacks.Curves.InseparableGenus

end
