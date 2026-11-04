module

public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import StacksFrontier.Algebra.Polynomial.Laurent
public import StacksFrontier.AlgebraicGeometry.Scheme.Affine.PuncturedPlane

/-!
# Pinching the punctured plane: the chart ring and the two coordinate axes

Over a field `k` the punctured plane `A²_k ∖ {0}` contains the two punctured coordinate axes
`C₁ : x = 0` and `C₂ : y = 0`, which are disjoint, and both are isomorphic to
`Spec k[t, 1/t]`: on `C₁` through `(0, t)` and on `C₂` through `(t⁻¹, 0)`. Identifying them
along these two parametrizations is the pinching whose result is a variety that is not
quasi-affine. This file provides the ring theory of the identification.

Both axes are contained in the standard open where `d = (x + y)(x + y³)` is invertible, and on
that chart the function `(x + y³)/(x + y)²` restricts to the coordinate `t` of *both*
parametrizations. That single function is what makes the pair of restriction maps
`k[x, y, 1/d] → k[t, 1/t] × k[t, 1/t]` surjective, hence the two axes a closed subscheme of the
chart: a prescribed pair of Laurent polynomials is interpolated by combining their lifts with
the idempotent-like separator `y/(x + y)`, which is `1` on `C₁` and `0` on `C₂`.

Finally, a polynomial whose restrictions to the two axes agree must be constant: the first
restriction only involves non-negative powers of `t` and the second only non-positive ones.
That is the computation of the ring of global functions on the pinched plane.

## Main definitions

* `Stacks.Examples.PinchedPlane.pinchingDenominator`: the function `(x + y)(x + y³)`, and
  `Stacks.Examples.PinchedPlane.pinchingRing` the coordinate ring `k[x, y, 1/d]` of the chart.
* `Stacks.Examples.PinchedPlane.restrictToFirstAxis` and
  `Stacks.Examples.PinchedPlane.restrictToSecondAxis`: the restrictions of a function on the
  chart to the two parametrized axes, and `Stacks.Examples.PinchedPlane.pinchingRestrictions`
  the pair of them.
* `Stacks.Examples.PinchedPlane.pinchingParameter`: the function `(x + y³)/(x + y)²`, which
  restricts to the coordinate on both axes.

## Main results

* `Stacks.Examples.PinchedPlane.pinchingRestrictions_surjective`: the pair of restrictions is
  surjective.
* `Stacks.Examples.PinchedPlane.exists_algebraMap_eq_of_restrictions_eq`: a polynomial whose
  two restrictions agree restricts to a constant.

## References

* [Stacks Project, Tag 0272](https://stacks.math.columbia.edu/tag/0272)
* [Stacks Project, Section 110.17 (Tag 0271)](https://stacks.math.columbia.edu/tag/0271)
-/

@[expose] public noncomputable section

open AlgebraicGeometry

universe u

namespace Stacks.Examples.PinchedPlane

variable (k : Type u) [Field k]

/-- The function `(x + y)(x + y³)` on the affine plane. Both punctured coordinate axes lie in
the standard open where it is invertible. -/
def pinchingDenominator : affinePlaneRing k :=
  (MvPolynomial.X 0 + MvPolynomial.X 1) * (MvPolynomial.X 0 + MvPolynomial.X 1 ^ 3)

/-- The coordinate ring `k[x, y, 1/((x + y)(x + y³))]` of the affine chart of the punctured
plane that contains both coordinate axes. -/
abbrev pinchingRing := Localization.Away (pinchingDenominator k)

section Units

/-- The factor `x + y` of the denominator is invertible on the chart. -/
theorem isUnit_algebraMap_sum :
    IsUnit (algebraMap (affinePlaneRing k) (pinchingRing k)
      (MvPolynomial.X 0 + MvPolynomial.X 1)) := by
  have h : IsUnit (algebraMap (affinePlaneRing k) (pinchingRing k)
      ((MvPolynomial.X 0 + MvPolynomial.X 1) * (MvPolynomial.X 0 + MvPolynomial.X 1 ^ 3))) :=
    IsLocalization.Away.algebraMap_isUnit (pinchingDenominator k)
  rw [map_mul] at h
  exact (IsUnit.mul_iff.mp h).1

/-- The factor `x + y³` of the denominator is invertible on the chart. -/
theorem isUnit_algebraMap_cubic :
    IsUnit (algebraMap (affinePlaneRing k) (pinchingRing k)
      (MvPolynomial.X 0 + MvPolynomial.X 1 ^ 3)) := by
  have h : IsUnit (algebraMap (affinePlaneRing k) (pinchingRing k)
      ((MvPolynomial.X 0 + MvPolynomial.X 1) * (MvPolynomial.X 0 + MvPolynomial.X 1 ^ 3))) :=
    IsLocalization.Away.algebraMap_isUnit (pinchingDenominator k)
  rw [map_mul] at h
  exact (IsUnit.mul_iff.mp h).2

/-- The function `(x + y³)/(x + y)²` on the chart, as a unit. -/
def pinchingParameterUnit : (pinchingRing k)ˣ :=
  (isUnit_algebraMap_cubic k).unit * ((isUnit_algebraMap_sum k).unit)⁻¹ ^ 2

/-- The function `(x + y³)/(x + y)²` on the chart. It restricts to the coordinate `t` on both
parametrized axes, which is what identifies them. -/
abbrev pinchingParameter : pinchingRing k := pinchingParameterUnit k

/-- The parameter is invertible on the chart. -/
theorem isUnit_pinchingParameter : IsUnit (pinchingParameter k) :=
  (pinchingParameterUnit k).isUnit

/-- The defining equation of the parameter: `(x + y³)/(x + y)²` times `(x + y)²` is
`x + y³`. -/
theorem pinchingParameter_mul_sum_sq :
    pinchingParameter k *
        algebraMap (affinePlaneRing k) (pinchingRing k)
          (MvPolynomial.X 0 + MvPolynomial.X 1) ^ 2 =
      algebraMap (affinePlaneRing k) (pinchingRing k)
        (MvPolynomial.X 0 + MvPolynomial.X 1 ^ 3) := by
  rw [pinchingParameter, pinchingParameterUnit, Units.val_mul, Units.val_pow_eq_pow_val,
    mul_assoc, ← mul_pow, IsUnit.val_inv_mul, one_pow, mul_one, IsUnit.unit_spec]

end Units

section Axes

/-- Restriction of a polynomial to the first punctured axis `x = 0`, parametrized by
`(0, t)`. -/
def restrictToFirstAxisBase : affinePlaneRing k →ₐ[k] LaurentPolynomial k :=
  MvPolynomial.aeval fun i : Fin 2 => if i = 0 then 0 else LaurentPolynomial.T 1

/-- Restriction of a polynomial to the second punctured axis `y = 0`, parametrized by
`(t⁻¹, 0)`. -/
def restrictToSecondAxisBase : affinePlaneRing k →ₐ[k] LaurentPolynomial k :=
  MvPolynomial.aeval fun i : Fin 2 => if i = 0 then LaurentPolynomial.T (-1) else 0

/-- The first coordinate vanishes on the first axis. -/
@[simp]
theorem restrictToFirstAxisBase_X_zero :
    restrictToFirstAxisBase k (MvPolynomial.X 0) = 0 := by
  simp [restrictToFirstAxisBase]

/-- The second coordinate is the parameter of the first axis. -/
@[simp]
theorem restrictToFirstAxisBase_X_one :
    restrictToFirstAxisBase k (MvPolynomial.X 1) = LaurentPolynomial.T 1 := by
  simp [restrictToFirstAxisBase]

/-- The first coordinate is the inverse parameter of the second axis. -/
@[simp]
theorem restrictToSecondAxisBase_X_zero :
    restrictToSecondAxisBase k (MvPolynomial.X 0) = LaurentPolynomial.T (-1) := by
  simp [restrictToSecondAxisBase]

/-- The second coordinate vanishes on the second axis. -/
@[simp]
theorem restrictToSecondAxisBase_X_one :
    restrictToSecondAxisBase k (MvPolynomial.X 1) = 0 := by
  simp [restrictToSecondAxisBase]

/-- On the first axis, `x + y` restricts to `t`. -/
theorem restrictToFirstAxisBase_sum :
    restrictToFirstAxisBase k (MvPolynomial.X 0 + MvPolynomial.X 1) =
      LaurentPolynomial.T 1 := by
  simp

/-- On the second axis, `x + y` restricts to `t⁻¹`. -/
theorem restrictToSecondAxisBase_sum :
    restrictToSecondAxisBase k (MvPolynomial.X 0 + MvPolynomial.X 1) =
      LaurentPolynomial.T (-1) := by
  simp

/-- On the first axis, `x + y³` restricts to `t³`. -/
theorem restrictToFirstAxisBase_cubic :
    restrictToFirstAxisBase k (MvPolynomial.X 0 + MvPolynomial.X 1 ^ 3) =
      LaurentPolynomial.T 3 := by
  simp [LaurentPolynomial.T_pow]

/-- On the second axis, `x + y³` restricts to `t⁻¹`. -/
theorem restrictToSecondAxisBase_cubic :
    restrictToSecondAxisBase k (MvPolynomial.X 0 + MvPolynomial.X 1 ^ 3) =
      LaurentPolynomial.T (-1) := by
  simp

/-- The denominator restricts to `t⁴` on the first axis, hence to a unit. -/
theorem restrictToFirstAxisBase_pinchingDenominator :
    restrictToFirstAxisBase k (pinchingDenominator k) = LaurentPolynomial.T 4 := by
  rw [pinchingDenominator, map_mul, restrictToFirstAxisBase_sum,
    restrictToFirstAxisBase_cubic, ← LaurentPolynomial.T_add]
  norm_num

/-- The denominator restricts to `t⁻²` on the second axis, hence to a unit. -/
theorem restrictToSecondAxisBase_pinchingDenominator :
    restrictToSecondAxisBase k (pinchingDenominator k) = LaurentPolynomial.T (-2) := by
  rw [pinchingDenominator, map_mul, restrictToSecondAxisBase_sum,
    restrictToSecondAxisBase_cubic, ← LaurentPolynomial.T_add]
  norm_num

/-- The first axis lies in the chart. -/
theorem isUnit_restrictToFirstAxisBase_pinchingDenominator :
    IsUnit (restrictToFirstAxisBase k (pinchingDenominator k)) := by
  rw [restrictToFirstAxisBase_pinchingDenominator]
  exact LaurentPolynomial.isUnit_T 4

/-- The second axis lies in the chart. -/
theorem isUnit_restrictToSecondAxisBase_pinchingDenominator :
    IsUnit (restrictToSecondAxisBase k (pinchingDenominator k)) := by
  rw [restrictToSecondAxisBase_pinchingDenominator]
  exact LaurentPolynomial.isUnit_T (-2)

/-- Restriction of a function on the chart to the first punctured axis. -/
def restrictToFirstAxis : pinchingRing k →ₐ[k] LaurentPolynomial k :=
  IsLocalization.Away.liftAlgHom (pinchingDenominator k)
    (isUnit_restrictToFirstAxisBase_pinchingDenominator k)

/-- Restriction of a function on the chart to the second punctured axis. -/
def restrictToSecondAxis : pinchingRing k →ₐ[k] LaurentPolynomial k :=
  IsLocalization.Away.liftAlgHom (pinchingDenominator k)
    (isUnit_restrictToSecondAxisBase_pinchingDenominator k)

/-- Restricting a polynomial to the first axis agrees with
restricting the function it defines on the chart. -/
@[simp]
theorem restrictToFirstAxis_algebraMap (f : affinePlaneRing k) :
    restrictToFirstAxis k (algebraMap (affinePlaneRing k) (pinchingRing k) f) =
      restrictToFirstAxisBase k f := by
  simp [restrictToFirstAxis, IsLocalization.Away.liftAlgHom]

/-- Restricting a polynomial to the second axis agrees with
restricting the function it defines on the chart. -/
@[simp]
theorem restrictToSecondAxis_algebraMap (f : affinePlaneRing k) :
    restrictToSecondAxis k (algebraMap (affinePlaneRing k) (pinchingRing k) f) =
      restrictToSecondAxisBase k f := by
  simp [restrictToSecondAxis, IsLocalization.Away.liftAlgHom]

/-- The pair of restrictions of a function on the chart to the two punctured axes. -/
def pinchingRestrictions :
    pinchingRing k →ₐ[k] LaurentPolynomial k × LaurentPolynomial k :=
  AlgHom.prod (restrictToFirstAxis k) (restrictToSecondAxis k)

/-- The components of the pair of restrictions on the chart. -/
@[simp]
theorem pinchingRestrictions_apply (f : pinchingRing k) :
    pinchingRestrictions k f = (restrictToFirstAxis k f, restrictToSecondAxis k f) := rfl

/-- The pair of restrictions of a polynomial on the plane to the two punctured axes. -/
def axisRestrictions :
    affinePlaneRing k →ₐ[k] LaurentPolynomial k × LaurentPolynomial k :=
  AlgHom.prod (restrictToFirstAxisBase k) (restrictToSecondAxisBase k)

/-- The components of the pair of restrictions of a polynomial. -/
@[simp]
theorem axisRestrictions_apply (f : affinePlaneRing k) :
    axisRestrictions k f = (restrictToFirstAxisBase k f, restrictToSecondAxisBase k f) := rfl

/-- Restricting a polynomial to the two axes is the same as viewing it as a function on the
chart and restricting that. -/
theorem pinchingRestrictions_toRingHom_comp_algebraMap :
    (pinchingRestrictions k).toRingHom.comp (algebraMap (affinePlaneRing k) (pinchingRing k)) =
      (axisRestrictions k).toRingHom := by
  refine RingHom.ext fun f => ?_
  simp

/-- The product of the two coordinates vanishes on both axes. -/
@[simp]
theorem axisRestrictions_X_mul_X :
    axisRestrictions k (MvPolynomial.X 0 * MvPolynomial.X 1) = 0 := by
  refine Prod.ext ?_ ?_ <;> simp

/-- The denominator restricts to a unit on both axes, so both axes lie in the chart. -/
theorem isUnit_axisRestrictions_pinchingDenominator :
    IsUnit (axisRestrictions k (pinchingDenominator k)) := by
  rw [axisRestrictions_apply]
  exact Prod.isUnit_iff.mpr ⟨isUnit_restrictToFirstAxisBase_pinchingDenominator k,
    isUnit_restrictToSecondAxisBase_pinchingDenominator k⟩

/-- Restricting to the first axis is the first component of the pair of restrictions. -/
theorem fst_comp_axisRestrictions :
    (RingHom.fst (LaurentPolynomial k) (LaurentPolynomial k)).comp
        (axisRestrictions k).toRingHom = (restrictToFirstAxisBase k).toRingHom :=
  RingHom.ext fun _ => rfl

/-- Restricting to the second axis is the second component of the pair of restrictions. -/
theorem snd_comp_axisRestrictions :
    (RingHom.snd (LaurentPolynomial k) (LaurentPolynomial k)).comp
        (axisRestrictions k).toRingHom = (restrictToSecondAxisBase k).toRingHom :=
  RingHom.ext fun _ => rfl

end Axes

section Parameter

/-- An equation `z * tⁿ = w` in `k[t, 1/t]` determines `z`. -/
private theorem eq_mul_T_neg_of_mul_T_eq {z w : LaurentPolynomial k} {n : ℤ}
    (h : z * LaurentPolynomial.T n = w) : z = w * LaurentPolynomial.T (-n) := by
  rw [← h, mul_assoc, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero,
    mul_one]

/-- A restriction of the chart sending `x + y` to `tᵃ` and `x + y³` to `tᵇ` sends the parameter
to `tᵇ⁻²ᵃ`. -/
private theorem apply_pinchingParameter_eq_T (φ : pinchingRing k →ₐ[k] LaurentPolynomial k)
    {a b : ℤ}
    (hs : φ (algebraMap (affinePlaneRing k) (pinchingRing k)
      (MvPolynomial.X 0 + MvPolynomial.X 1)) = LaurentPolynomial.T a)
    (hc : φ (algebraMap (affinePlaneRing k) (pinchingRing k)
      (MvPolynomial.X 0 + MvPolynomial.X 1 ^ 3)) = LaurentPolynomial.T b) :
    φ (pinchingParameter k) = LaurentPolynomial.T (b - 2 * a) := by
  have h := congrArg φ (pinchingParameter_mul_sum_sq k)
  rw [map_mul, map_pow, hs, hc, LaurentPolynomial.T_pow] at h
  rw [eq_mul_T_neg_of_mul_T_eq k h, ← LaurentPolynomial.T_add]
  congr 1

/-- The parameter restricts to the coordinate `t` on the first axis: `t³/t² = t`. -/
theorem restrictToFirstAxis_pinchingParameter :
    restrictToFirstAxis k (pinchingParameter k) = LaurentPolynomial.T 1 := by
  rw [apply_pinchingParameter_eq_T k _ (a := 1) (b := 3)
    (by simp) (by simp)]
  norm_num

/-- The parameter restricts to the coordinate `t` on the second axis as well:
`t⁻¹/t⁻² = t`. -/
theorem restrictToSecondAxis_pinchingParameter :
    restrictToSecondAxis k (pinchingParameter k) = LaurentPolynomial.T 1 := by
  rw [apply_pinchingParameter_eq_T k _ (a := -1) (b := -1)
    (by simp) (by simp)]
  norm_num

/-- The lift of the coordinate of either axis to the chart, sending `t` to the parameter. -/
def liftAxisCoordinate : LaurentPolynomial k →ₐ[k] pinchingRing k :=
  IsLocalization.Away.liftAlgHom (Polynomial.X : Polynomial k)
    (f := Polynomial.aeval (pinchingParameter k))
    (by simp [isUnit_pinchingParameter k])

/-- The coordinate of the axis, as the image of the polynomial variable. -/
theorem algebraMap_polynomial_X :
    algebraMap (Polynomial k) (LaurentPolynomial k) Polynomial.X = LaurentPolynomial.T 1 := by
  rw [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_X]

/-- The lift sends the coordinate of the axis to the parameter. -/
@[simp]
theorem liftAxisCoordinate_T_one :
    liftAxisCoordinate k (LaurentPolynomial.T 1) = pinchingParameter k := by
  rw [← algebraMap_polynomial_X, liftAxisCoordinate, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  simp

/-- A restriction of the chart sending the parameter to `t` is a retraction of the lift. -/
private theorem comp_liftAxisCoordinate_eq_id (φ : pinchingRing k →ₐ[k] LaurentPolynomial k)
    (h : φ (pinchingParameter k) = LaurentPolynomial.T 1) :
    φ.comp (liftAxisCoordinate k) = AlgHom.id k (LaurentPolynomial k) := by
  refine IsLocalization.algHom_ext (Submonoid.powers (Polynomial.X : Polynomial k))
    (Polynomial.algHom_ext ?_)
  have hX : (Algebra.algHom k (Polynomial k) (LaurentPolynomial k)) Polynomial.X =
      LaurentPolynomial.T 1 := algebraMap_polynomial_X k
  simp only [AlgHom.comp_apply, AlgHom.id_apply, hX]
  rw [liftAxisCoordinate_T_one, h]

/-- The lift of the coordinate is a section of the restriction to the first axis. -/
theorem restrictToFirstAxis_comp_liftAxisCoordinate :
    (restrictToFirstAxis k).comp (liftAxisCoordinate k) = AlgHom.id k (LaurentPolynomial k) :=
  comp_liftAxisCoordinate_eq_id k _ (restrictToFirstAxis_pinchingParameter k)

/-- The lift of the coordinate is a section of the restriction to the second axis. -/
theorem restrictToSecondAxis_comp_liftAxisCoordinate :
    (restrictToSecondAxis k).comp (liftAxisCoordinate k) = AlgHom.id k (LaurentPolynomial k) :=
  comp_liftAxisCoordinate_eq_id k _ (restrictToSecondAxis_pinchingParameter k)

/-- Restricting the lift of a Laurent polynomial to the first
axis recovers it. -/
theorem restrictToFirstAxis_liftAxisCoordinate (a : LaurentPolynomial k) :
    restrictToFirstAxis k (liftAxisCoordinate k a) = a :=
  DFunLike.congr_fun (restrictToFirstAxis_comp_liftAxisCoordinate k) a

/-- Restricting the lift of a Laurent polynomial to the second
axis recovers it. -/
theorem restrictToSecondAxis_liftAxisCoordinate (a : LaurentPolynomial k) :
    restrictToSecondAxis k (liftAxisCoordinate k a) = a :=
  DFunLike.congr_fun (restrictToSecondAxis_comp_liftAxisCoordinate k) a

end Parameter

section Surjective

/-- The function `y/(x + y)` on the chart: it is `1` on the first axis and `0` on the second,
so it separates them. -/
def axisSeparator : pinchingRing k :=
  algebraMap (affinePlaneRing k) (pinchingRing k) (MvPolynomial.X 1) *
    ↑((isUnit_algebraMap_sum k).unit⁻¹)

/-- The defining equation of the separator: `y/(x + y)` times `x + y` is `y`. -/
theorem axisSeparator_mul_sum :
    axisSeparator k *
        algebraMap (affinePlaneRing k) (pinchingRing k)
          (MvPolynomial.X 0 + MvPolynomial.X 1) =
      algebraMap (affinePlaneRing k) (pinchingRing k) (MvPolynomial.X 1) := by
  rw [axisSeparator, mul_assoc, IsUnit.val_inv_mul, mul_one]

/-- The separator restricts to `1` on the first axis. -/
@[simp]
theorem restrictToFirstAxis_axisSeparator : restrictToFirstAxis k (axisSeparator k) = 1 := by
  have h := congrArg (restrictToFirstAxis k) (axisSeparator_mul_sum k)
  rw [map_mul, restrictToFirstAxis_algebraMap, restrictToFirstAxisBase_sum,
    restrictToFirstAxis_algebraMap, restrictToFirstAxisBase_X_one] at h
  rw [eq_mul_T_neg_of_mul_T_eq k h, ← LaurentPolynomial.T_add]
  norm_num

/-- The separator restricts to `0` on the second axis. -/
@[simp]
theorem restrictToSecondAxis_axisSeparator : restrictToSecondAxis k (axisSeparator k) = 0 := by
  rw [axisSeparator, map_mul, restrictToSecondAxis_algebraMap,
    restrictToSecondAxisBase_X_one, zero_mul]

/-- **The two punctured axes are a closed subscheme of the chart.** The pair of restrictions
to the two axes is surjective: a prescribed pair `(a, b)` is the value of
`e·â + (1 - e)·b̂`, where `e` is the separator and `â`, `b̂` are the lifts of `a` and `b`
along the parameter. -/
theorem pinchingRestrictions_surjective :
    Function.Surjective (pinchingRestrictions k) := by
  rintro ⟨a, b⟩
  refine ⟨axisSeparator k * liftAxisCoordinate k a +
    (1 - axisSeparator k) * liftAxisCoordinate k b, Prod.ext ?_ ?_⟩
  · simp [restrictToFirstAxis_liftAxisCoordinate]
  · simp [restrictToSecondAxis_liftAxisCoordinate]

end Surjective

section Constants

/-- Restriction of a polynomial to the first axis, before inverting the coordinate. -/
def firstAxisPolynomial : affinePlaneRing k →ₐ[k] Polynomial k :=
  MvPolynomial.aeval fun i : Fin 2 => if i = 0 then 0 else Polynomial.X

/-- Restriction of a polynomial to the second axis, before inverting the coordinate. -/
def secondAxisPolynomial : affinePlaneRing k →ₐ[k] Polynomial k :=
  MvPolynomial.aeval fun i : Fin 2 => if i = 0 then Polynomial.X else 0

/-- The restriction to the first axis only involves non-negative powers of the coordinate. -/
theorem restrictToFirstAxisBase_eq_toLaurent (p : affinePlaneRing k) :
    restrictToFirstAxisBase k p = Polynomial.toLaurent (firstAxisPolynomial k p) := by
  have h : Polynomial.toLaurentAlg.comp (firstAxisPolynomial k) = restrictToFirstAxisBase k := by
    refine MvPolynomial.algHom_ext fun i => ?_
    fin_cases i <;> simp [firstAxisPolynomial, restrictToFirstAxisBase]
  exact (DFunLike.congr_fun h p).symm

/-- The restriction to the second axis only involves non-positive powers of the coordinate. -/
theorem restrictToSecondAxisBase_eq_invert_toLaurent (p : affinePlaneRing k) :
    restrictToSecondAxisBase k p =
      LaurentPolynomial.invert (Polynomial.toLaurent (secondAxisPolynomial k p)) := by
  have h : (LaurentPolynomial.invert.toAlgHom.comp Polynomial.toLaurentAlg).comp
      (secondAxisPolynomial k) = restrictToSecondAxisBase k := by
    refine MvPolynomial.algHom_ext fun i => ?_
    fin_cases i <;> simp [secondAxisPolynomial, restrictToSecondAxisBase]
  exact (DFunLike.congr_fun h p).symm

/-- **The functions on the pinched plane are the constants.** A polynomial whose restrictions
to the two axes agree restricts to a constant: one restriction has only non-negative powers of
the coordinate and the other only non-positive ones. -/
theorem exists_algebraMap_eq_of_restrictions_eq (p : affinePlaneRing k)
    (h : restrictToFirstAxisBase k p = restrictToSecondAxisBase k p) :
    ∃ c : k, restrictToFirstAxisBase k p = algebraMap k (LaurentPolynomial k) c := by
  rw [restrictToFirstAxisBase_eq_toLaurent, restrictToSecondAxisBase_eq_invert_toLaurent] at h
  obtain ⟨c, hc, -⟩ := Polynomial.toLaurent_eq_invert_toLaurent_iff.mp h
  refine ⟨c, ?_⟩
  rw [restrictToFirstAxisBase_eq_toLaurent, hc, Polynomial.toLaurent_C,
    LaurentPolynomial.C_eq_algebraMap]

end Constants

end Stacks.Examples.PinchedPlane

end
