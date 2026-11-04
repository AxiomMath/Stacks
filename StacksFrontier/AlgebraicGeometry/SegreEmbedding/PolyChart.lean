module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The standard affine chart of projective space

`AlgebraicGeometry.Proj` of a polynomial ring graded by total degree is covered by the loci
`D₊(x_i)`, and `AlgebraicGeometry.Proj.basicOpenIsoSpec` identifies each with `Spec` of the
degree-zero homogeneous localisation `HomogeneousLocalization.Away` at `x_i`.  That localisation
is not computed anywhere in Mathlib.  This file computes it: it is the polynomial ring on the
remaining indices, the chart variables being the ratios `x_k / x_i`.

The use is Stacks Tag 01WD, the Segre embedding.  Identifying `Proj` of the Segre product with a
product of two projective spaces is a chart-by-chart argument, and the charts of the two
projective spaces are exactly the rings computed here; see
`StacksFrontier/AlgebraicGeometry/SegreEmbedding/SegreChartRing.lean`, which runs the same
argument for the Segre product itself.

## What is proved, and the route

* `Stacks.AlgebraicGeometry.PolyChart.eval₂_mul_pow_weight_of_isWeightedHomogeneous` is Euler's
  scaling identity in weighted form: evaluating a `w`-weighted homogeneous polynomial of weight
  `n` at the variables scaled by `c ^ w v` multiplies the value by `c ^ n`.  It is proved by
  expanding the polynomial as the sum of its monomials, where the scaling factor of a monomial is
  `c` raised to the weight of its exponent vector.
  `Stacks.AlgebraicGeometry.PolyChart.eval₂_mul_left_of_isHomogeneous` is the total-degree case,
  the weight being constantly one.

* `Stacks.AlgebraicGeometry.PolyChart.dehom` is dehomogenisation at `i`: the ring homomorphism
  substituting `1` for `x_i` and the chart variable for every other variable.  Since it sends
  `x_i` to a unit it extends to the localization of the polynomial ring at `x_i`, and composing
  with the inclusion of the chart ring into that localization gives
  `Stacks.AlgebraicGeometry.PolyChart.fromAway`.

* `Stacks.AlgebraicGeometry.PolyChart.toAway` goes the other way, sending the chart variable
  indexed by `k` to the fraction `x_k / x_i`, which is
  `Stacks.AlgebraicGeometry.PolyChart.chartVar`.

* `Stacks.AlgebraicGeometry.PolyChart.val_toAway_dehom` is the computational heart: for `p`
  homogeneous of degree `n`, the image of its dehomogenisation is the fraction `p / x_i ^ n`.
  The proof identifies the composite of `toAway` with `dehom`, read in the localization, as the
  evaluation sending each variable to `x_k / x_i` — this is
  `Stacks.AlgebraicGeometry.PolyChart.comp_toAway_dehom_eq_evalInv`, two ring homomorphisms
  compared on the constants and the variables — and then applies the scaling identity with
  `c = 1 / x_i`.

* `Stacks.AlgebraicGeometry.PolyChart.chartIso` is the resulting ring isomorphism.  One composite
  is `fromAway_comp_toAway`, checked on the constants and the chart variables; the other is
  `toAway_fromAway`, where `HomogeneousLocalization.Away.mk_surjective` writes an arbitrary
  element as `a / x_i ^ n` with `a` homogeneous of degree `n` and the previous item applies.

## Implementation notes

The grading of a polynomial ring is `MvPolynomial.gradedAlgebra`, a definition rather than an
instance, so it is taken here as an ordinary instance **binder**: a local instance introduced in a
*statement* does not survive into the proof of that statement.  Consumers supply the canonical
grading in the body of a definition.

`IsLocalization.Away.invSelf` is used for `1 / x_i` rather than a bare `Localization.mk`, because
the subtype proof inside a `Localization.mk` is a term and two spellings of it do not meet; the
`IsLocalization` API avoids that entirely.

## What is not done

Nothing here is geometric: no statement about `AlgebraicGeometry.Proj`, `Spec` or schemes is made,
and in particular the chart isomorphism is not transported to an isomorphism of the standard open
`D₊(x_i)` of projective space with affine space.

No `Algebra R` structure is put on the chart ring — `HomogeneousLocalization` carries only an
algebra structure over the degree-zero part — so no statement here involves a tensor product.
The companion file states its tensor-product comparison between two polynomial rings instead, for
that reason.
-/
@[expose] public section

open MvPolynomial

namespace Stacks.AlgebraicGeometry.PolyChart

/-! ### A homogeneous polynomial evaluated at scaled variables -/

variable {R S σ : Type*} [CommSemiring R] [CommSemiring S]

/-- **Euler's scaling identity, weighted.**  Evaluating a `w`-weighted homogeneous polynomial of
weight `n` at the variables scaled by `c ^ w v` multiplies the value by `c ^ n`. -/
public theorem eval₂_mul_pow_weight_of_isWeightedHomogeneous (f : R →+* S) (g : σ → S) (c : S)
    (w : σ → ℕ) {n : ℕ} {p : MvPolynomial σ R} (hp : p.IsWeightedHomogeneous w n) :
    MvPolynomial.eval₂ f (fun v => c ^ w v * g v) p = c ^ n * MvPolynomial.eval₂ f g p := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [← MvPolynomial.coe_eval₂Hom, ← MvPolynomial.coe_eval₂Hom, map_sum, map_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hdeg : Finsupp.weight w α = n := hp (MvPolynomial.mem_support_iff.mp hα)
  have hprod : (α.prod fun v e => (c ^ w v * g v) ^ e) =
      c ^ Finsupp.weight w α * α.prod fun v e => g v ^ e := by
    rw [Finsupp.prod, Finsupp.prod, Finsupp.weight_apply, Finsupp.sum]
    simp_rw [mul_pow, ← pow_mul]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    congr 2
    exact Finset.sum_congr rfl fun v _ => by rw [smul_eq_mul, mul_comm]
  simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial, hprod, hdeg]
  ring

/-- Euler's scaling identity for the total degree. -/
public theorem eval₂_mul_left_of_isHomogeneous (f : R →+* S) (g : σ → S) (c : S) {n : ℕ}
    {p : MvPolynomial σ R} (hp : p.IsHomogeneous n) :
    MvPolynomial.eval₂ f (fun k => c * g k) p = c ^ n * MvPolynomial.eval₂ f g p := by
  simpa using eval₂_mul_pow_weight_of_isWeightedHomogeneous f g c 1 hp

/-! ### The chart ring -/

section Chart

variable (R : Type*) [CommRing R] {ι : Type*} [DecidableEq ι]
  [GradedAlgebra (MvPolynomial.homogeneousSubmodule ι R)] (i : ι)

omit [DecidableEq ι] [GradedAlgebra (MvPolynomial.homogeneousSubmodule ι R)] in
/-- The variable `X i` is homogeneous of degree one. -/
public theorem X_mem_one : (MvPolynomial.X i : MvPolynomial ι R) ∈ homogeneousSubmodule ι R 1 :=
  MvPolynomial.isHomogeneous_X R i

/-- Dehomogenisation at `i`: substitute `1` for `X i` and the corresponding chart variable for
every other variable. -/
public noncomputable def dehom :
    MvPolynomial ι R →+* MvPolynomial {k : ι // k ≠ i} R :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun k => if h : k = i then 1 else MvPolynomial.X ⟨k, h⟩)

omit [GradedAlgebra (MvPolynomial.homogeneousSubmodule ι R)] in
/-- Dehomogenisation fixes the constants. -/
public theorem dehom_C (r : R) :
    dehom R i (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [dehom]

omit [GradedAlgebra (MvPolynomial.homogeneousSubmodule ι R)] in
/-- Dehomogenisation at `i` sends `X i` to `1`. -/
public theorem dehom_X_self : dehom R i (MvPolynomial.X i) = 1 := by
  simp [dehom]

omit [GradedAlgebra (MvPolynomial.homogeneousSubmodule ι R)] in
/-- Dehomogenisation at `i` sends `X k`, for `k ≠ i`, to the chart variable indexed by `k`. -/
public theorem dehom_X_of_ne {k : ι} (h : k ≠ i) :
    dehom R i (MvPolynomial.X k) = MvPolynomial.X ⟨k, h⟩ := by
  simp [dehom, h]

/-- The constants, as a ring homomorphism into the degree-zero part. -/
public noncomputable def constHom : R →+* (homogeneousSubmodule ι R 0) where
  toFun r := ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C ι r⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

/-- The chart variable `x_k / x_i`. -/
public noncomputable def chartVar (k : ι) :
    HomogeneousLocalization.Away (homogeneousSubmodule ι R) (MvPolynomial.X i) :=
  HomogeneousLocalization.Away.mk _ (X_mem_one R i) 1 (MvPolynomial.X k)
    (by simpa using MvPolynomial.isHomogeneous_X R k)

/-- The comparison homomorphism from the polynomial ring on the chart variables to the chart
ring. -/
public noncomputable def toAway :
    MvPolynomial {k : ι // k ≠ i} R →+*
      HomogeneousLocalization.Away (homogeneousSubmodule ι R) (MvPolynomial.X i) :=
  MvPolynomial.eval₂Hom
    ((HomogeneousLocalization.fromZeroRingHom _ _).comp (constHom R (ι := ι)))
    (fun k => chartVar R i k.1)

omit [GradedAlgebra (MvPolynomial.homogeneousSubmodule ι R)] in
/-- Dehomogenisation at `i` sends `X i` to a unit. -/
public theorem isUnit_dehom_X : IsUnit (dehom R i (MvPolynomial.X i)) := by
  rw [dehom_X_self]
  exact isUnit_one

/-- The comparison homomorphism back: the chart ring is a subring of the localization of the
polynomial ring at `X i`, and dehomogenisation inverts `X i`. -/
public noncomputable def fromAway :
    HomogeneousLocalization.Away (homogeneousSubmodule ι R) (MvPolynomial.X i) →+*
      MvPolynomial {k : ι // k ≠ i} R :=
  (Localization.awayLift (dehom R i) (MvPolynomial.X i) (isUnit_dehom_X R i)).comp
    (algebraMap (HomogeneousLocalization.Away (homogeneousSubmodule ι R) (MvPolynomial.X i))
      (Localization.Away (MvPolynomial.X i : MvPolynomial ι R)))

/-! ### The two composites -/

/-- `1 / x_i`, in the localization of the polynomial ring at `x_i`. -/
public noncomputable def invX :
    Localization.Away (MvPolynomial.X i : MvPolynomial ι R) :=
  IsLocalization.Away.invSelf (MvPolynomial.X i : MvPolynomial ι R)

omit [DecidableEq ι] [GradedAlgebra (MvPolynomial.homogeneousSubmodule ι R)] in
/-- `x_i * (1 / x_i) = 1` in the localization at `x_i`. -/
public theorem algebraMap_X_mul_invX :
    algebraMap (MvPolynomial ι R) (Localization.Away (MvPolynomial.X i : MvPolynomial ι R))
        (MvPolynomial.X i) * invX R i = 1 :=
  IsLocalization.Away.mul_invSelf _

omit [DecidableEq ι] [GradedAlgebra (MvPolynomial.homogeneousSubmodule ι R)] in
/-- `1 / x_i` is the fraction with numerator `1` and denominator `x_i`. -/
public theorem invX_eq_mk' :
    invX R i = IsLocalization.mk' _ 1
      (⟨MvPolynomial.X i, Submonoid.mem_powers _⟩ :
        Submonoid.powers (MvPolynomial.X i : MvPolynomial ι R)) := rfl

/-- Evaluation of the polynomial ring in the localization at `x_i`, each variable going to
`x_k / x_i`. -/
public noncomputable def evalInv :
    MvPolynomial ι R →+* Localization.Away (MvPolynomial.X i : MvPolynomial ι R) :=
  MvPolynomial.eval₂Hom
    ((algebraMap (MvPolynomial ι R)
      (Localization.Away (MvPolynomial.X i : MvPolynomial ι R))).comp MvPolynomial.C)
    (fun k => invX R i *
      algebraMap (MvPolynomial ι R)
        (Localization.Away (MvPolynomial.X i : MvPolynomial ι R)) (MvPolynomial.X k))

omit [DecidableEq ι] in
/-- In the localization at `x_i`, the chart variable indexed by `k` is `x_k / x_i`. -/
public theorem val_chartVar (k : ι) :
    (chartVar R i k).val = invX R i *
      algebraMap (MvPolynomial ι R)
        (Localization.Away (MvPolynomial.X i : MvPolynomial ι R)) (MvPolynomial.X k) := by
  rw [chartVar, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk'_apply, invX_eq_mk',
    mul_comm, ← IsLocalization.mk'_eq_mul_mk'_one]
  congr 1
  exact Subtype.ext (pow_one _)

omit [DecidableEq ι] in
/-- The comparison homomorphism sends a constant to the constant fraction. -/
public theorem val_toAway_C (r : R) :
    (toAway R i (MvPolynomial.C r)).val =
      algebraMap (MvPolynomial ι R)
        (Localization.Away (MvPolynomial.X i : MvPolynomial ι R)) (MvPolynomial.C r) := by
  rw [toAway, MvPolynomial.eval₂Hom_C]
  exact Localization.mk_one_eq_algebraMap _

/-- Dehomogenising and then mapping into the chart ring agrees, in the localization, with
dividing each variable by `x_i`. -/
public theorem comp_toAway_dehom_eq_evalInv :
    (algebraMap (HomogeneousLocalization.Away (homogeneousSubmodule ι R) (MvPolynomial.X i))
      (Localization.Away (MvPolynomial.X i : MvPolynomial ι R))).comp
        ((toAway R i).comp (dehom R i)) = evalInv R i := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_)
  · simp only [RingHom.comp_apply, dehom_C, evalInv, MvPolynomial.eval₂Hom_C,
      HomogeneousLocalization.algebraMap_apply]
    exact val_toAway_C R i r
  · simp only [RingHom.comp_apply, evalInv, MvPolynomial.eval₂Hom_X',
      HomogeneousLocalization.algebraMap_apply]
    by_cases h : k = i
    · subst h
      rw [dehom_X_self, map_one, HomogeneousLocalization.val_one, mul_comm]
      exact (algebraMap_X_mul_invX R k).symm
    · rw [dehom_X_of_ne R i h, toAway, MvPolynomial.eval₂Hom_X']
      exact val_chartVar R i k

/-- **The chart ring receives every homogeneous fraction.**  For `p` homogeneous of degree `n`,
the image of its dehomogenisation is the fraction `p / x_i ^ n`. -/
public theorem val_toAway_dehom {n : ℕ} {p : MvPolynomial ι R} (hp : p.IsHomogeneous n) :
    (toAway R i (dehom R i p)).val =
      Localization.mk p (⟨MvPolynomial.X i ^ n, n, rfl⟩ :
        Submonoid.powers (MvPolynomial.X i : MvPolynomial ι R)) := by
  have h := DFunLike.congr_fun (comp_toAway_dehom_eq_evalInv R i) p
  rw [RingHom.comp_apply, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply] at h
  have hbase : MvPolynomial.eval₂
      ((algebraMap (MvPolynomial ι R)
        (Localization.Away (MvPolynomial.X i : MvPolynomial ι R))).comp MvPolynomial.C)
      (fun k => algebraMap (MvPolynomial ι R)
        (Localization.Away (MvPolynomial.X i : MvPolynomial ι R)) (MvPolynomial.X k)) p =
      algebraMap (MvPolynomial ι R)
        (Localization.Away (MvPolynomial.X i : MvPolynomial ι R)) p := by
    rw [← MvPolynomial.coe_eval₂Hom]
    exact DFunLike.congr_fun
      (MvPolynomial.ringHom_ext (fun r => by simp) (fun k => by simp)) p
  rw [h, evalInv, MvPolynomial.coe_eval₂Hom,
    eval₂_mul_left_of_isHomogeneous _ _ _ hp, hbase, Localization.mk_eq_mk'_apply,
    IsLocalization.eq_mk'_iff_mul_eq]
  have hunit : invX R i ^ n *
      algebraMap (MvPolynomial ι R)
        (Localization.Away (MvPolynomial.X i : MvPolynomial ι R)) (MvPolynomial.X i ^ n) = 1 := by
    rw [map_pow, ← mul_pow, mul_comm, algebraMap_X_mul_invX, one_pow]
  rw [mul_right_comm, hunit, one_mul]

/-! ### The chart ring is a polynomial ring -/

omit [GradedAlgebra (MvPolynomial.homogeneousSubmodule ι R)] in
/-- Dehomogenisation, extended to the localization at `x_i`, sends `a / x_i ^ n` to the
dehomogenisation of `a`. -/
public theorem awayLift_dehom_mk (a : MvPolynomial ι R) (n : ℕ) :
    Localization.awayLift (dehom R i) (MvPolynomial.X i) (isUnit_dehom_X R i)
        (Localization.mk a (⟨MvPolynomial.X i ^ n, n, rfl⟩ :
          Submonoid.powers (MvPolynomial.X i : MvPolynomial ι R))) = dehom R i a := by
  rw [Localization.awayLift_mk (dehom R i) (MvPolynomial.X i) a 1
    (by rw [dehom_X_self, mul_one]) n, one_pow, mul_one]

/-- `fromAway` sends the fraction `a / x_i ^ n` to the dehomogenisation of `a`. -/
private theorem fromAway_mk (n : ℕ) (a : MvPolynomial ι R)
    (ha : a ∈ homogeneousSubmodule ι R (n • 1)) :
    fromAway R i (HomogeneousLocalization.Away.mk _ (X_mem_one R i) n a ha) = dehom R i a := by
  simp only [fromAway, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  exact awayLift_dehom_mk R i a n

/-- The chart ring maps onto the polynomial ring on the chart variables, with the comparison
homomorphism as a section. -/
public theorem fromAway_comp_toAway :
    (fromAway R i).comp (toAway R i) = RingHom.id (MvPolynomial {k : ι // k ≠ i} R) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_)
  · simp only [RingHom.comp_apply, RingHom.id_apply, fromAway,
      HomogeneousLocalization.algebraMap_apply, val_toAway_C]
    rw [IsLocalization.Away.lift_eq, dehom_C]
  · simp only [RingHom.comp_apply, RingHom.id_apply, toAway, MvPolynomial.eval₂Hom_X', chartVar]
    rw [fromAway_mk, dehom_X_of_ne R i k.2]

/-- Every element of the chart ring is the image of its own dehomogenisation. -/
public theorem toAway_fromAway
    (z : HomogeneousLocalization.Away (homogeneousSubmodule ι R) (MvPolynomial.X i)) :
    toAway R i (fromAway R i z) = z := by
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ (X_mem_one R i) z
  have hahom : a.IsHomogeneous n := by
    simpa [MvPolynomial.mem_homogeneousSubmodule] using ha
  rw [fromAway_mk]
  apply HomogeneousLocalization.val_injective
  rw [val_toAway_dehom R i hahom, HomogeneousLocalization.Away.val_mk]

/-- **The standard affine chart of projective space.**  The degree-zero homogeneous localisation
of the polynomial ring on `ι`, graded by total degree, at the variable `x_i`, is the polynomial
ring on the remaining indices: the chart variables are the ratios `x_k / x_i`. -/
public noncomputable def chartIso :
    HomogeneousLocalization.Away (homogeneousSubmodule ι R) (MvPolynomial.X i) ≃+*
      MvPolynomial {k : ι // k ≠ i} R where
  toFun := fromAway R i
  invFun := toAway R i
  left_inv := toAway_fromAway R i
  right_inv := DFunLike.congr_fun (fromAway_comp_toAway R i)
  map_mul' x y := map_mul _ x y
  map_add' x y := map_add _ x y

/-- The chart isomorphism is `fromAway`. -/
@[simp] public theorem chartIso_apply
    (z : HomogeneousLocalization.Away (homogeneousSubmodule ι R) (MvPolynomial.X i)) :
    chartIso R i z = fromAway R i z := rfl

/-- The inverse of the chart isomorphism is `toAway`. -/
@[simp] public theorem chartIso_symm_apply (p : MvPolynomial {k : ι // k ≠ i} R) :
    (chartIso R i).symm p = toAway R i p := rfl

end Chart

end Stacks.AlgebraicGeometry.PolyChart

end
