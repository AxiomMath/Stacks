module

public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassCubicPoints

/-!
# The two standard charts of a plane Weierstrass cubic

Let `W : y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` be a Weierstrass equation over a commutative
ring `R`, with no condition on its discriminant, and let `E ⊂ P²_R` be its plane cubic
`zy² + a₁xyz + a₃yz² = x³ + a₂x²z + a₄xz² + a₆z³`. This file identifies the two standard charts
of `E` that cover it:

* `D₊(z) ≅ Spec R[x, y]/(y² + a₁xy + a₃y - x³ - a₂x² - a₄x - a₆)`, the affine curve, whose
  coordinate ring is Mathlib's `WeierstrassCurve.Affine.CoordinateRing`;
* `D₊(y) ≅ Spec R[X, Z]/(Z + a₁XZ + a₃Z² - X³ - a₂X²Z - a₄XZ² - a₆Z³)`, the chart at infinity,
  with `X = x / y` and `Z = z / y`.

It proves that they cover `E`, that the zero section `(0 : 1 : 0)` is the origin `X = Z = 0` of
the second chart, that the complement of the zero section is exactly `D₊(z)`, and that on the
overlap the two charts are related by `x = X / Z`, `y = 1 / Z`.

## Main definitions

* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.chartZEquiv`: the ring isomorphism
  `R[x, y, z]/(F)_{(z)} ≃ R[x, y]/(f)`, and
  `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.chartZ` the open immersion
  `Spec R[x, y]/(f) ⟶ E`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.ChartYRing`: the coordinate ring of the
  chart at infinity, presented as `R[Z][X]` modulo the monic cubic
  `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.chartYPolynomial`, with coordinates
  `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.chartYX` and
  `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.chartYZ`;
  `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.chartYEquiv` the ring isomorphism
  `R[x, y, z]/(F)_{(y)} ≃ ChartYRing W`, and
  `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.chartY` the open immersion
  `Spec (ChartYRing W) ⟶ E`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.chartYEvalZero`: evaluation of
  `ChartYRing W` at the origin.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.chartZOfChartY`: the change of charts
  `x ↦ X / Z`, `y ↦ 1 / Z`.

## Main results

* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.opensRange_chartZ` and
  `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.opensRange_chartY`: the images of the
  charts are `D₊(z)` and `D₊(y)`, and
  `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.chartZ_projectionOf`,
  `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.chartY_projectionOf`: they lie over
  `Spec R`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.basicOpenOf_two_sup_basicOpenOf_one`:
  `D₊(z) ∪ D₊(y)` is all of `E`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.zeroOf_eq_chartY`: the zero section is the
  origin of the chart at infinity.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.range_zeroOf`: the image of the zero
  section is the complement of `D₊(z)`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.SpecMap_chartZOfChartY_chartZ`: the two
  charts agree on the overlap.
* `Module.Free (Polynomial R) (ChartYRing W)`: the chart at infinity is free over `R[Z]`, with
  basis `1, X, X²` (`AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.chartYPowerBasis`).

## Implementation notes

Both charts are written as points with values in their coordinate rings, in the sense of
`AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.specPoint`: `D₊(z)` is the point
`(x : y : 1)` and `D₊(y)` the point `(X : 1 : Z)`. The identification with Mathlib's
`AlgebraicGeometry.Proj.awayι` is
`AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.specPoint_eq_awayι`, and the comparison on
the overlap is a rescaling of homogeneous coordinates by the unit `Z`. The chart at infinity is
presented as an `AdjoinRoot` over `R[Z]` because its equation is monic of degree three in `X`,
which makes it free over `R[Z]`.

## References

* [Stacks Project, Tag 072S](https://stacks.math.columbia.edu/tag/072S)
* [Stacks Project, Tag 072T](https://stacks.math.columbia.edu/tag/072T)
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial HomogeneousLocalization

universe u

namespace AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-! ### The affine chart `D₊(z)` -/

/-- The constants of `R[x, y]/(f)` are the classes of the constant polynomials. -/
theorem algebraMap_coordinateRing (a : R) :
    algebraMap R W.toAffine.CoordinateRing a =
      AdjoinRoot.mk W.toAffine.polynomial (Polynomial.C (Polynomial.C a)) := by
  rw [IsScalarTower.algebraMap_apply R (Polynomial R) W.toAffine.CoordinateRing,
    AdjoinRoot.algebraMap_eq, Polynomial.algebraMap_apply, Algebra.algebraMap_self_apply,
    AdjoinRoot.of, RingHom.comp_apply]

/-- The dehomogenization `R[x, y, z]/(F) → R[x, y]/(f)` at `z`: `x ↦ x`, `y ↦ y`, `z ↦ 1`. -/
def affineChartHom : coordRingOf W →+* W.toAffine.CoordinateRing :=
  coordLift W (algebraMap R _) ![AdjoinRoot.mk _ (Polynomial.C Polynomial.X),
    AdjoinRoot.mk _ Polynomial.X, 1] <| by
    have h : (Polynomial.X ^ 2 + Polynomial.C (Polynomial.C W.a₁ * Polynomial.X +
        Polynomial.C W.a₃) * Polynomial.X - Polynomial.C (Polynomial.X ^ 3 + Polynomial.C W.a₂ *
        Polynomial.X ^ 2 + Polynomial.C W.a₄ * Polynomial.X + Polynomial.C W.a₆)).eval₂
        (AdjoinRoot.of W.toAffine.polynomial) (AdjoinRoot.root W.toAffine.polynomial) = 0 :=
      AdjoinRoot.eval₂_root _
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, map_add, map_mul,
      map_pow] at h
    simp only [Matrix.cons_val, algebraMap_coordinateRing, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
    linear_combination h

/-- The dehomogenization at `z` sends `z` to `1`. -/
theorem affineChartHom_coordOf_two : affineChartHom W (coordOf W 2) = 1 := by
  simp [affineChartHom, coordLift_mk]

/-- The rehomogenization `R[x, y]/(f) → R[x, y, z]/(F)_{(z)}`: `x ↦ x / z`, `y ↦ y / z`. -/
def affineChartInv : W.toAffine.CoordinateRing →+* Away (gradingOf W) (coordOf W 2) :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (awayConst W 2) (awayCoord W 2 0)) (awayCoord W 2 1) <|
    by
    have h := awayCoord_equation W 2
    rw [awayCoord_self] at h
    simp only [WeierstrassCurve.Affine.polynomial, Polynomial.eval₂_add, Polynomial.eval₂_sub,
      Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
      Polynomial.coe_eval₂RingHom]
    linear_combination h

/-- The rehomogenization sends the coordinates to the affine coordinates of `D₊(z)`. -/
theorem affineChartInv_affineChartHom_coordOf (j : Fin 3) :
    affineChartInv W (affineChartHom W (coordOf W j)) = awayCoord W 2 j := by
  fin_cases j
  · simp [affineChartHom, coordLift_mk, affineChartInv]
  · simp [affineChartHom, coordLift_mk, affineChartInv]
  · simp [affineChartHom, coordLift_mk, awayCoord_self]

/-- The rehomogenization sends constants to constants. -/
theorem affineChartInv_algebraMap (a : R) :
    affineChartInv W (algebraMap R _ a) = awayConst W 2 a := by
  simp [algebraMap_coordinateRing, affineChartInv]

/-- **The chart `D₊(z)`.** The degree-zero localization `R[x, y, z]/(F)_{(z)}` is the affine
coordinate ring `R[x, y]/(f)` of `W`, by `p / zᵏ ↦ p(x, y, 1)`. -/
def chartZEquiv : Away (gradingOf W) (coordOf W 2) ≃+* W.toAffine.CoordinateRing :=
  RingEquiv.ofBijective (awayLiftOf W (affineChartHom W) 2 (affineChartHom_coordOf_two W)) <|
    awayLiftOf_bijective W _ 2 _ (affineChartInv W) (affineChartInv_affineChartHom_coordOf W)
      (fun a => by simpa [affineChartHom, coordLift_mk] using affineChartInv_algebraMap W a)
      fun s => by
      have : (awayLiftOf W (affineChartHom W) 2 (affineChartHom_coordOf_two W)).comp
          (affineChartInv W) = RingHom.id _ := by
        refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun a => ?_) ?_) ?_
        · simp only [RingHom.comp_apply, AdjoinRoot.of, affineChartInv, AdjoinRoot.lift_mk,
            Polynomial.eval₂_C, Polynomial.coe_eval₂RingHom, awayLiftOf_awayConst]
          simp [affineChartHom, coordLift_mk, algebraMap_coordinateRing]
        · simp only [RingHom.comp_apply, AdjoinRoot.of, affineChartInv, AdjoinRoot.lift_mk,
            Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.coe_eval₂RingHom,
            awayLiftOf_awayCoord]
          simp [affineChartHom, coordLift_mk]
        · simp only [RingHom.comp_apply, affineChartInv, AdjoinRoot.lift_root,
            awayLiftOf_awayCoord]
          simp [affineChartHom, coordLift_mk]
      exact congr($this s)

/-! ### The chart `D₊(y)` -/

/-- The equation `X³ + a₂ZX² + (a₄Z² - a₁Z)X - (Z + a₃Z² - a₆Z³)` of the chart `D₊(y)`, monic in
`X`, as a polynomial in `X` over `R[Z]`. It is minus the dehomogenization `F(X, 1, Z)` of the
Weierstrass cubic, with `X = x / y` and `Z = z / y`. -/
def chartYPolynomial : Polynomial (Polynomial R) :=
  Polynomial.X ^ 3 + Polynomial.C (Polynomial.C W.a₂ * Polynomial.X) * Polynomial.X ^ 2 +
    Polynomial.C (Polynomial.C W.a₄ * Polynomial.X ^ 2 - Polynomial.C W.a₁ * Polynomial.X) *
      Polynomial.X -
    Polynomial.C (Polynomial.X + Polynomial.C W.a₃ * Polynomial.X ^ 2 -
      Polynomial.C W.a₆ * Polynomial.X ^ 3)

/-- The equation of the chart `D₊(y)` is monic of degree three in `X`. -/
theorem monic_chartYPolynomial : (chartYPolynomial W).Monic := by
  have : chartYPolynomial W = Polynomial.X ^ 3 +
      (Polynomial.C (Polynomial.C W.a₂ * Polynomial.X) * Polynomial.X ^ 2 +
        Polynomial.C (Polynomial.C W.a₄ * Polynomial.X ^ 2 - Polynomial.C W.a₁ * Polynomial.X) *
          Polynomial.X -
        Polynomial.C (Polynomial.X + Polynomial.C W.a₃ * Polynomial.X ^ 2 -
          Polynomial.C W.a₆ * Polynomial.X ^ 3)) := by
    rw [chartYPolynomial]; ring
  rw [this]
  refine Polynomial.monic_X_pow_add
    ((Polynomial.degree_le_of_natDegree_le (n := 2) (by compute_degree)).trans_lt ?_)
  exact_mod_cast Nat.lt_succ_self 2

/-- The coordinate ring `R[X, Z]/(Z + a₁XZ + a₃Z² - X³ - a₂X²Z - a₄XZ² - a₆Z³)` of the chart
`D₊(y)`, presented as `R[Z][X]` modulo the monic cubic `chartYPolynomial`. -/
abbrev ChartYRing : Type u := AdjoinRoot (chartYPolynomial W)

/-- The affine coordinate `X = x / y` of the chart `D₊(y)`. -/
def chartYX : ChartYRing W := AdjoinRoot.root _

/-- The affine coordinate `Z = z / y` of the chart `D₊(y)`. -/
def chartYZ : ChartYRing W := AdjoinRoot.of _ Polynomial.X

/-- The constants of the chart `D₊(y)` are the classes of the constant polynomials. -/
theorem algebraMap_chartYRing (a : R) :
    algebraMap R (ChartYRing W) a = AdjoinRoot.of _ (Polynomial.C a) := by
  rw [IsScalarTower.algebraMap_apply R (Polynomial R) (ChartYRing W), AdjoinRoot.algebraMap_eq,
    Polynomial.algebraMap_apply, Algebra.algebraMap_self_apply]

/-- The equation of the chart `D₊(y)`: `Z + a₁XZ + a₃Z² - X³ - a₂X²Z - a₄XZ² - a₆Z³ = 0`. -/
theorem chartY_equation :
    chartYZ W + algebraMap R _ W.a₁ * chartYX W * chartYZ W +
        algebraMap R _ W.a₃ * chartYZ W ^ 2 -
      (chartYX W ^ 3 + algebraMap R _ W.a₂ * chartYX W ^ 2 * chartYZ W +
        algebraMap R _ W.a₄ * chartYX W * chartYZ W ^ 2 +
        algebraMap R _ W.a₆ * chartYZ W ^ 3) = 0 := by
  have h : (Polynomial.X ^ 3 + Polynomial.C (Polynomial.C W.a₂ * Polynomial.X) * Polynomial.X ^ 2 +
      Polynomial.C (Polynomial.C W.a₄ * Polynomial.X ^ 2 - Polynomial.C W.a₁ * Polynomial.X) *
        Polynomial.X -
      Polynomial.C (Polynomial.X + Polynomial.C W.a₃ * Polynomial.X ^ 2 -
        Polynomial.C W.a₆ * Polynomial.X ^ 3)).eval₂ (AdjoinRoot.of (chartYPolynomial W))
        (AdjoinRoot.root (chartYPolynomial W)) = 0 :=
    AdjoinRoot.eval₂_root _
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, map_add, map_sub, map_mul,
    map_pow] at h
  simp only [algebraMap_chartYRing, chartYX, chartYZ]
  linear_combination -h

/-- The dehomogenization `R[x, y, z]/(F) → R[X, Z]/(F(X, 1, Z))` at `y`: `x ↦ X`, `y ↦ 1`,
`z ↦ Z`. -/
def chartYHom : coordRingOf W →+* ChartYRing W :=
  coordLift W (algebraMap R _) ![chartYX W, 1, chartYZ W] <| by
    simp only [Matrix.cons_val]
    linear_combination chartY_equation W

/-- The dehomogenization at `y` sends `y` to `1`. -/
theorem chartYHom_coordOf_one : chartYHom W (coordOf W 1) = 1 := by
  simp [chartYHom, coordLift_mk]

/-- The rehomogenization `R[X, Z]/(F(X, 1, Z)) → R[x, y, z]/(F)_{(y)}`: `X ↦ x / y`,
`Z ↦ z / y`. -/
def chartYInv : ChartYRing W →+* Away (gradingOf W) (coordOf W 1) :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (awayConst W 1) (awayCoord W 1 2)) (awayCoord W 1 0) <|
    by
    have h := awayCoord_equation W 1
    rw [awayCoord_self] at h
    simp only [chartYPolynomial, Polynomial.eval₂_add, Polynomial.eval₂_sub,
      Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
      Polynomial.coe_eval₂RingHom]
    linear_combination -h

/-- The rehomogenization sends the coordinates to the affine coordinates of `D₊(y)`. -/
theorem chartYInv_chartYHom_coordOf (j : Fin 3) :
    chartYInv W (chartYHom W (coordOf W j)) = awayCoord W 1 j := by
  fin_cases j
  · simp [chartYHom, coordLift_mk, chartYInv, chartYX]
  · simp [chartYHom, coordLift_mk, awayCoord_self]
  · simp [chartYHom, coordLift_mk, chartYInv, chartYZ]

/-- The rehomogenization at `y` sends constants to constants. -/
theorem chartYInv_algebraMap (a : R) :
    chartYInv W (algebraMap R _ a) = awayConst W 1 a := by
  simp [algebraMap_chartYRing, chartYInv]

/-- **The chart `D₊(y)`.** The degree-zero localization `R[x, y, z]/(F)_{(y)}` is the coordinate
ring `R[X, Z]/(F(X, 1, Z))` of the chart at infinity, by `p / yᵏ ↦ p(X, 1, Z)`. -/
def chartYEquiv : Away (gradingOf W) (coordOf W 1) ≃+* ChartYRing W :=
  RingEquiv.ofBijective (awayLiftOf W (chartYHom W) 1 (chartYHom_coordOf_one W)) <|
    awayLiftOf_bijective W _ 1 _ (chartYInv W) (chartYInv_chartYHom_coordOf W)
      (fun a => by simpa [chartYHom, coordLift_mk] using chartYInv_algebraMap W a)
      fun s => by
      have : (awayLiftOf W (chartYHom W) 1 (chartYHom_coordOf_one W)).comp
          (chartYInv W) = RingHom.id _ := by
        refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun a => ?_) ?_) ?_
        · simp only [RingHom.comp_apply, chartYInv, AdjoinRoot.lift_of,
            Polynomial.eval₂_C, Polynomial.coe_eval₂RingHom, awayLiftOf_awayConst]
          simp [chartYHom, coordLift_mk, algebraMap_chartYRing]
        · simp only [RingHom.comp_apply, chartYInv, AdjoinRoot.lift_of,
            Polynomial.eval₂_X, Polynomial.coe_eval₂RingHom, awayLiftOf_awayCoord]
          simp [chartYHom, coordLift_mk, chartYZ]
        · simp only [RingHom.comp_apply, chartYInv, AdjoinRoot.lift_root,
            awayLiftOf_awayCoord]
          simp [chartYHom, coordLift_mk, chartYX]
      exact congr($this s)

/-- The power basis `{1, X, X²}` of the coordinate ring of the chart `D₊(y)` over `R[Z]`. -/
def chartYPowerBasis : PowerBasis (Polynomial R) (ChartYRing W) :=
  AdjoinRoot.powerBasis' (monic_chartYPolynomial W)

/-- The coordinate ring of the chart `D₊(y)` is a free `R[Z]`-module. -/
instance : Module.Free (Polynomial R) (ChartYRing W) :=
  .of_basis (chartYPowerBasis W).basis

/-- The coordinate ring of the chart `D₊(y)` is a free `R`-module. -/
instance : Module.Free R (ChartYRing W) := .trans (S := Polynomial R)

/-! ### The charts as open immersions -/

/-- The constants of `R[x, y, z]/(F)` are the classes of the constant polynomials. -/
theorem algebraMap_coordRingOf (a : R) :
    algebraMap R (coordRingOf W) a = Ideal.Quotient.mk _ (MvPolynomial.C a) := rfl

/-- The open immersion `Spec R[x, y]/(f) ⟶ E` of the affine chart `D₊(z)`. -/
def chartZ : Spec (CommRingCat.of W.toAffine.CoordinateRing) ⟶ projOf W :=
  specPoint W (affineChartHom W) (map_irrelevant_eq_top_of_isUnit W _ 2
    (by rw [affineChartHom_coordOf_two]; exact isUnit_one))

/-- The open immersion `Spec R[X, Z]/(F(X, 1, Z)) ⟶ E` of the chart `D₊(y)` at infinity. -/
def chartY : Spec (CommRingCat.of (ChartYRing W)) ⟶ projOf W :=
  specPoint W (chartYHom W) (map_irrelevant_eq_top_of_isUnit W _ 1
    (by rw [chartYHom_coordOf_one]; exact isUnit_one))

/-- The chart `D₊(z)` is Mathlib's chart `AlgebraicGeometry.Proj.awayι`, read through
`chartZEquiv`. -/
theorem chartZ_eq_awayι :
    chartZ W = Spec.map (chartZEquiv W).toCommRingCatIso.hom ≫ awayιOf W 2 :=
  specPoint_eq_awayι W _ 2 (affineChartHom_coordOf_two W) _

/-- The chart `D₊(y)` is Mathlib's chart `AlgebraicGeometry.Proj.awayι`, read through
`chartYEquiv`. -/
theorem chartY_eq_awayι :
    chartY W = Spec.map (chartYEquiv W).toCommRingCatIso.hom ≫ awayιOf W 1 :=
  specPoint_eq_awayι W _ 1 (chartYHom_coordOf_one W) _

/-- The chart `chartZ W` is an open immersion. -/
instance : IsOpenImmersion (chartZ W) := by
  rw [chartZ_eq_awayι]; infer_instance

/-- The chart `chartY W` is an open immersion. -/
instance : IsOpenImmersion (chartY W) := by
  rw [chartY_eq_awayι]; infer_instance

/-- The image of the chart `chartZ W` is `D₊(z)`. -/
theorem opensRange_chartZ : (chartZ W).opensRange = basicOpenOf W (coordOf W 2) := by
  simp only [chartZ_eq_awayι, Scheme.Hom.opensRange_comp_of_isIso, opensRange_awayιOf]

/-- The image of the chart `chartY W` is `D₊(y)`. -/
theorem opensRange_chartY : (chartY W).opensRange = basicOpenOf W (coordOf W 1) := by
  simp only [chartY_eq_awayι, Scheme.Hom.opensRange_comp_of_isIso, opensRange_awayιOf]

/-- A point of `E` with values in `S` whose coordinates restrict to the structure map on `R` lies
over `Spec S ⟶ Spec R`. -/
private theorem specPoint_projectionOf_of_algebraMap {S : Type u} [CommRing S] [Algebra R S]
    (κ : coordRingOf W →+* S) (hκ) (h : ∀ a : R, κ (algebraMap R _ a) = algebraMap R S a) :
    specPoint W κ hκ ≫ projectionOf W = Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [specPoint_projectionOf]
  congr 2
  exact RingHom.ext h

/-- The chart `D₊(z)` lies over `Spec R`. -/
theorem chartZ_projectionOf :
    chartZ W ≫ projectionOf W = Spec.map (CommRingCat.ofHom (algebraMap R _)) :=
  specPoint_projectionOf_of_algebraMap W _ _ fun a => by
    simp [algebraMap_coordRingOf, affineChartHom, coordLift_mk]

/-- The chart `D₊(y)` lies over `Spec R`. -/
theorem chartY_projectionOf :
    chartY W ≫ projectionOf W = Spec.map (CommRingCat.ofHom (algebraMap R _)) :=
  specPoint_projectionOf_of_algebraMap W _ _ fun a => by
    simp [algebraMap_coordRingOf, chartYHom, coordLift_mk]

/-! ### The two charts cover the plane cubic -/

/-- The homogeneous Weierstrass equation in `R[x, y, z]/(F)`. -/
theorem coordOf_equation :
    coordOf W 2 * coordOf W 1 ^ 2 + algebraMap R _ W.a₁ * coordOf W 0 * coordOf W 1 * coordOf W 2 +
        algebraMap R _ W.a₃ * coordOf W 1 * coordOf W 2 ^ 2 -
      (coordOf W 0 ^ 3 + algebraMap R _ W.a₂ * coordOf W 0 ^ 2 * coordOf W 2 +
        algebraMap R _ W.a₄ * coordOf W 0 * coordOf W 2 ^ 2 +
        algebraMap R _ W.a₆ * coordOf W 2 ^ 3) = 0 := by
  have h0 : Ideal.Quotient.mk (cubicIdealOf W).toIdeal (cubicOf W) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  rw [← h0]
  simp only [cubicOf, WeierstrassCurve.Projective.polynomial, map_sub, map_add, map_mul, map_pow,
    algebraMap_coordRingOf]
  ring

/-- The homogeneous coordinate ring is generated over its degree-zero part by `x`, `y`, `z`. -/
theorem adjoin_coordOf : Algebra.adjoin (gradingOf W 0) (Set.range (coordOf W)) = ⊤ := by
  rw [eq_top_iff]
  rintro a -
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
  induction P using MvPolynomial.induction_on with
  | C r => exact Subalgebra.algebraMap_mem _ (toGradingZeroOf W r)
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p i hp => rw [map_mul]; exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)

/-- A prime ideal containing `z` contains `x`, when `z y² + a₁xyz + a₃yz² = x³ + a₂x²z + a₄xz² +
a₆z³`. -/
private theorem mem_of_weierstrass_equation {A : Type*} [CommRing A] (I : Ideal A) [I.IsPrime]
    (x y z a₁ a₂ a₃ a₄ a₆ : A)
    (h : z * y ^ 2 + a₁ * x * y * z + a₃ * y * z ^ 2 -
      (x ^ 3 + a₂ * x ^ 2 * z + a₄ * x * z ^ 2 + a₆ * z ^ 3) = 0) (hz : z ∈ I) : x ∈ I := by
  refine Ideal.IsPrime.mem_of_pow_mem ‹_› 3 ?_
  have : x ^ 3 = z * (y ^ 2 + a₁ * x * y + a₃ * y * z - a₂ * x ^ 2 - a₄ * x * z - a₆ * z ^ 2) := by
    linear_combination -h
  rw [this]
  exact Ideal.mul_mem_right _ _ hz

/-- At a point of the plane cubic where `z` vanishes, `x` vanishes too. -/
theorem coordOf_zero_mem_of_two_mem (p : ProjectiveSpectrum (gradingOf W))
    (hz : coordOf W 2 ∈ p.asHomogeneousIdeal) : coordOf W 0 ∈ p.asHomogeneousIdeal :=
  have := p.isPrime
  mem_of_weierstrass_equation p.asHomogeneousIdeal.toIdeal _ _ _ _ _ _ _ _
    (coordOf_equation W) hz

/-- **The charts `D₊(z)` and `D₊(y)` cover the plane cubic.** -/
theorem basicOpenOf_two_sup_basicOpenOf_one :
    basicOpenOf W (coordOf W 2) ⊔ basicOpenOf W (coordOf W 1) = ⊤ := by
  refine eq_top_iff.mpr fun p _ => ?_
  by_contra hp
  simp only [TopologicalSpace.Opens.mem_sup, mem_basicOpenOf, not_or, not_not] at hp
  have htop : (⨆ i, basicOpenOf W (coordOf W i)) = ⊤ :=
    Proj.iSup_basicOpen_eq_top' (gradingOf W) (coordOf W) (fun i => ⟨1, coordOf_mem W i⟩)
      (adjoin_coordOf W)
  have hcov : p ∈ ⨆ i, basicOpenOf W (coordOf W i) := by
    rw [htop]; trivial
  rw [TopologicalSpace.Opens.mem_iSup] at hcov
  obtain ⟨i, hi⟩ := hcov
  have hx := coordOf_zero_mem_of_two_mem W p hp.1
  fin_cases i
  · exact hi hx
  · exact hi hp.2
  · exact hi hp.1

/-- The images of the two charts cover the plane cubic. -/
theorem range_chartZ_union_range_chartY :
    Set.range (chartZ W) ∪ Set.range (chartY W) = Set.univ := by
  rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange, opensRange_chartZ,
    opensRange_chartY, ← TopologicalSpace.Opens.coe_sup, basicOpenOf_two_sup_basicOpenOf_one]
  rfl

/-! ### The zero section in the chart `D₊(y)` -/

/-- Evaluation of the coordinate ring of the chart `D₊(y)` at its origin `X = Z = 0`. -/
def chartYEvalZero : ChartYRing W →+* R :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (RingHom.id R) 0) 0
    (by
      simp only [chartYPolynomial, Polynomial.eval₂_add, Polynomial.eval₂_sub,
        Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
        Polynomial.coe_eval₂RingHom]
      simp)

/-- Evaluation at the origin of the chart `D₊(y)` sends `X` to `0`. -/
@[simp] theorem chartYEvalZero_chartYX : chartYEvalZero W (chartYX W) = 0 := by
  simp [chartYEvalZero, chartYX]

/-- Evaluation at the origin of the chart `D₊(y)` sends `Z` to `0`. -/
@[simp] theorem chartYEvalZero_chartYZ : chartYEvalZero W (chartYZ W) = 0 := by
  simp [chartYEvalZero, chartYZ]

/-- Evaluation at the origin of the chart `D₊(y)` is the identity on constants. -/
@[simp] theorem chartYEvalZero_algebraMap (a : R) : chartYEvalZero W (algebraMap R _ a) = a := by
  simp [chartYEvalZero, algebraMap_chartYRing]

/-- Dehomogenizing at `y` and evaluating at the origin is evaluating at `(0 : 1 : 0)`. -/
theorem chartYEvalZero_comp_chartYHom : (chartYEvalZero W).comp (chartYHom W) = evalZeroOf W := by
  refine coordRingOf_ringHom_ext W (fun a => ?_) fun i => ?_
  · simp [chartYHom, coordLift_mk, algebraMap_coordRingOf, evalZeroOf]
  · fin_cases i <;> simp [chartYHom, coordLift_mk, evalZeroOf]

/-- **The zero section lies in the chart `D₊(y)`, at its origin.** -/
theorem zeroOf_eq_chartY :
    zeroOf W = Spec.map (CommRingCat.ofHom (chartYEvalZero W)) ≫ chartY W := by
  rw [chartY, SpecMap_specPoint, zeroOf_eq_specPoint]
  · exact specPoint_congr W (chartYEvalZero_comp_chartYHom W).symm _ _
  · rw [chartYEvalZero_comp_chartYHom]
    exact map_irrelevant_eq_top_of_isUnit W _ 1 (by simp [evalZeroOf])

/-- Every element of the coordinate ring of the chart `D₊(y)` is its value at the origin plus an
element of the ideal `(X, Z)`. -/
theorem sub_algebraMap_chartYEvalZero_mem (b : ChartYRing W) :
    b - algebraMap R _ (chartYEvalZero W b) ∈ Ideal.span {chartYX W, chartYZ W} := by
  let I : Ideal (ChartYRing W) := Ideal.span {chartYX W, chartYZ W}
  have hX : chartYX W ∈ I := Ideal.subset_span (by simp)
  have hZ : chartYZ W ∈ I := Ideal.subset_span (by simp)
  have key : (Ideal.Quotient.mk I).comp ((algebraMap R _).comp (chartYEvalZero W)) =
      Ideal.Quotient.mk I := by
    refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun a => ?_) ?_) ?_
    · simp [← algebraMap_chartYRing]
    · simp only [RingHom.comp_apply]
      rw [show AdjoinRoot.of (chartYPolynomial W) Polynomial.X = chartYZ W from rfl,
        chartYEvalZero_chartYZ, map_zero, map_zero,
        (Ideal.Quotient.eq_zero_iff_mem).mpr hZ]
    · simp only [RingHom.comp_apply]
      rw [show AdjoinRoot.root (chartYPolynomial W) = chartYX W from rfl,
        chartYEvalZero_chartYX, map_zero, map_zero,
        (Ideal.Quotient.eq_zero_iff_mem).mpr hX]
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  exact (congr($key b)).symm

/-- The inverse image of `D₊(f)` under a point with values in `S` is the basic open of `κ f`. -/
theorem specPoint_preimage_basicOpenOf {S : Type u} [CommRing S] (κ : coordRingOf W →+* S) (hκ)
    {f : coordRingOf W} {n : ℕ} (hn : 0 < n) (hf : f ∈ gradingOf W n) :
    specPoint W κ hκ ⁻¹ᵁ basicOpenOf W f = PrimeSpectrum.basicOpen (κ f) :=
  (Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ hn hf).trans
    (basicOpen_eq_of_affine (R := CommRingCat.of S) (κ f))

/-- The zero section misses the chart `D₊(z)`. -/
theorem zeroOf_preimage_basicOpenOf_two : zeroOf W ⁻¹ᵁ basicOpenOf W (coordOf W 2) = ⊥ := by
  rw [zeroOf_eq_specPoint, specPoint_preimage_basicOpenOf W _ _ one_pos (coordOf_mem W 2)]
  simp [evalZeroOf]
  rfl

/-- In the chart `D₊(y)`, the plane cubic meets `z = 0` only at the origin `X = Z = 0`: a prime
of the coordinate ring containing `Z` contains `X`. -/
theorem chartYX_mem_of_chartYZ_mem (q : Ideal (ChartYRing W)) [q.IsPrime] (hZ : chartYZ W ∈ q) :
    chartYX W ∈ q :=
  mem_of_weierstrass_equation q _ 1 _ _ _ _ _ _ (by simpa using chartY_equation W) hZ

/-- The dehomogenization at `y` sends `z` to `Z`. -/
theorem chartYHom_coordOf_two : chartYHom W (coordOf W 2) = chartYZ W := by
  simp [chartYHom, coordLift_mk]

/-- **The complement of the zero section is the chart `D₊(z)`.** The image of `(0 : 1 : 0)` is the
locus where `z` vanishes. -/
theorem range_zeroOf : Set.range (zeroOf W) = (basicOpenOf W (coordOf W 2) : Set (projOf W))ᶜ := by
  apply Set.Subset.antisymm
  · rintro _ ⟨r, rfl⟩ hr
    have : r ∈ zeroOf W ⁻¹ᵁ basicOpenOf W (coordOf W 2) := hr
    rw [zeroOf_preimage_basicOpenOf_two] at this
    exact this
  · intro p hp
    have hcov : p ∈ basicOpenOf W (coordOf W 2) ⊔ basicOpenOf W (coordOf W 1) := by
      rw [basicOpenOf_two_sup_basicOpenOf_one]; trivial
    have hy : p ∈ basicOpenOf W (coordOf W 1) := by
      rcases hcov with h | h
      · exact absurd h hp
      · exact h
    rw [← opensRange_chartY] at hy
    obtain ⟨q, rfl⟩ := hy
    have hq : q ∉ chartY W ⁻¹ᵁ basicOpenOf W (coordOf W 2) := hp
    rw [chartY, specPoint_preimage_basicOpenOf W _ _ one_pos (coordOf_mem W 2),
      chartYHom_coordOf_two] at hq
    have hZ : chartYZ W ∈ q.asIdeal := not_not.mp fun h => hq h
    have := q.isPrime
    have hX := chartYX_mem_of_chartYZ_mem W q.asIdeal hZ
    have hker : RingHom.ker (chartYEvalZero W) ≤ q.asIdeal := by
      intro b hb
      have h := sub_algebraMap_chartYEvalZero_mem W b
      rw [RingHom.mem_ker.mp hb, map_zero, sub_zero] at h
      exact (Ideal.span_le.mpr (by
        rintro _ (rfl | rfl)
        exacts [hX, hZ])) h
    have hsurj : Function.Surjective (chartYEvalZero W) :=
      fun a => ⟨algebraMap R _ a, chartYEvalZero_algebraMap W a⟩
    obtain ⟨r, hr⟩ : q ∈ Set.range (PrimeSpectrum.comap (chartYEvalZero W)) := by
      rw [range_comap_of_surjective _ _ hsurj]
      exact hker
    refine ⟨r, ?_⟩
    rw [zeroOf_eq_chartY]
    exact congrArg (chartY W) hr

/-! ### The overlap of the two charts -/

/-- On the overlap `D₊(yz)`, a homomorphism `β` out of the coordinate ring of the chart `D₊(y)`
under which `Z` is invertible, with inverse `v`, induces the homomorphism out of the affine
coordinate ring `R[x, y]/(f)` with `x ↦ β(X) · v` and `y ↦ v`: that is, `x = X / Z`,
`y = 1 / Z`. -/
def chartZOfChartY {S : Type*} [CommRing S] (β : ChartYRing W →+* S) (v : S)
    (hv : β (chartYZ W) * v = 1) : W.toAffine.CoordinateRing →+* S :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (β.comp (algebraMap R _)) (β (chartYX W) * v)) v <| by
    have h := congrArg β (chartY_equation W)
    simp only [map_add, map_sub, map_mul, map_pow, map_zero] at h
    simp only [WeierstrassCurve.Affine.polynomial, Polynomial.eval₂_add, Polynomial.eval₂_sub,
      Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
      Polynomial.coe_eval₂RingHom, RingHom.comp_apply]
    linear_combination v ^ 3 * h - (v ^ 2 + β (algebraMap R _ W.a₁) * β (chartYX W) * v ^ 2 +
      β (algebraMap R _ W.a₃) * v * (1 + β (chartYZ W) * v) -
      β (algebraMap R _ W.a₂) * β (chartYX W) ^ 2 * v ^ 2 -
      β (algebraMap R _ W.a₄) * β (chartYX W) * v * (1 + β (chartYZ W) * v) -
      β (algebraMap R _ W.a₆) * (1 + β (chartYZ W) * v + (β (chartYZ W) * v) ^ 2)) * hv

/-- The change of charts sends `x` to `β(X) · v`. -/
@[simp] theorem chartZOfChartY_x {S : Type*} [CommRing S] (β : ChartYRing W →+* S) (v : S) (hv) :
    chartZOfChartY W β v hv (AdjoinRoot.of _ Polynomial.X) = β (chartYX W) * v := by
  simp [chartZOfChartY]

/-- The change of charts sends `y` to `v`. -/
@[simp] theorem chartZOfChartY_y {S : Type*} [CommRing S] (β : ChartYRing W →+* S) (v : S) (hv) :
    chartZOfChartY W β v hv (AdjoinRoot.root _) = v := by
  simp [chartZOfChartY]

/-- The change of charts is the identity on constants. -/
theorem chartZOfChartY_algebraMap {S : Type*} [CommRing S] (β : ChartYRing W →+* S) (v : S) (hv)
    (a : R) : chartZOfChartY W β v hv (algebraMap R _ a) = β (algebraMap R _ a) := by
  simp [chartZOfChartY, algebraMap_coordinateRing]

/-- **The two charts agree on the overlap.** If `Z` becomes invertible under
`β : R[X, Z]/(F(X, 1, Z)) → S`, the `S`-point of the chart `D₊(y)` given by `β` is the `S`-point
of the chart `D₊(z)` given by `x ↦ X / Z`, `y ↦ 1 / Z`. -/
theorem SpecMap_chartZOfChartY_chartZ {S : Type u} [CommRing S] (β : ChartYRing W →+* S) (v : S)
    (hv : β (chartYZ W) * v = 1) :
    Spec.map (CommRingCat.ofHom (chartZOfChartY W β v hv)) ≫ chartZ W =
      Spec.map (CommRingCat.ofHom β) ≫ chartY W := by
  rw [chartZ, chartY, SpecMap_specPoint, SpecMap_specPoint]
  · refine specPoint_congr_unit W _ _ (Units.mkOfMulEqOne _ _ hv) (fun a => ?_) (fun i => ?_) _ _
    · simp only [RingHom.comp_apply, ← algebraMap_coordRingOf]
      simp only [chartYHom, affineChartHom, coordLift_mk, algebraMap_coordRingOf, eval₂_C,
        chartZOfChartY_algebraMap]
    · fin_cases i
      · simp [chartYHom, affineChartHom, coordLift_mk]
        linear_combination (β (chartYX W)) * hv.symm
      · simpa [chartYHom, affineChartHom, coordLift_mk] using hv.symm
      · simp [chartYHom, affineChartHom, coordLift_mk]
  · exact map_irrelevant_eq_top_of_isUnit W _ 1 (by simp [chartYHom_coordOf_one])
  · exact map_irrelevant_eq_top_of_isUnit W _ 2 (by simp [affineChartHom_coordOf_two])

end AlgebraicGeometry.ModuliEllipticCurves.Weierstrass
