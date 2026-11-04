module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.EllipticCurve.DiscriminantSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassCubicCharts

/-!
# A Weierstrass cubic smooth over a field has invertible discriminant

Let `C` be a Weierstrass curve over a field `k` and `E ⊆ ℙ²_k` its plane cubic, with projection
`E ⟶ Spec k`.  This file proves that if this projection is smooth, then the discriminant `Δ` of
`C` is invertible, that is, `C` is an elliptic curve.  The affine chart `D₊(z)` of `E` is the open
immersion `Spec k[x, y]/(f) ⟶ E`, so `k[x, y]/(f)` is smooth over `k`; this is the plane curve
whose smoothness forces `Δ ≠ 0` by `Stacks.WeierstrassDiscriminant.Δ_ne_zero_of_smooth`.

## Main definitions

* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.coordinateRingEquiv`: Mathlib's affine
  coordinate ring `k[X][Y]/(f)` of `C` is `k[x, y]/(f)`, with `x ↦ X 0` and `y ↦ X 1`.

## Main results

* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.algebraSmooth_coordinateRing_of_smooth`:
  if `E ⟶ Spec k` is smooth, then so is the affine coordinate ring of `C` over `k`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.isUnit_Δ_of_smooth`: if `E ⟶ Spec k` is
  smooth, then `Δ` is a unit.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.isElliptic_of_smooth`: the same, as
  `C.IsElliptic`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

variable {k : Type u} [Field k] (C : WeierstrassCurve k)

/-- Mathlib's affine polynomial of a Weierstrass curve, read in `k[x, y]` with the inner variable
as `x = X 0` and the outer variable as `y = X 1`, is the affine equation of the curve. -/
theorem equivMvPolynomial_polynomial :
    Polynomial.Bivariate.equivMvPolynomial k C.toAffine.polynomial =
      Stacks.WeierstrassDiscriminant.affineEquation C := by
  rw [Stacks.WeierstrassDiscriminant.affineEquation_eq]
  simp [WeierstrassCurve.Affine.polynomial]
  ring

/-- The affine coordinate ring `k[X][Y]/(f)` of a Weierstrass curve is the quotient
`k[x, y]/(f)` of `MvPolynomial (Fin 2) k` by its affine equation, with `x ↦ X 0` and
`y ↦ X 1`. -/
def coordinateRingEquiv :
    C.toAffine.CoordinateRing ≃ₐ[k]
      MvPolynomial (Fin 2) k ⧸ Ideal.span {Stacks.WeierstrassDiscriminant.affineEquation C} :=
  Ideal.quotientEquivAlg (Ideal.span {C.toAffine.polynomial}) _
    (Polynomial.Bivariate.equivMvPolynomial k) <| by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun p => Ideal.span {p}) (equivMvPolynomial_polynomial C).symm

/-- **The affine chart of a smooth cubic is smooth.**  If the plane cubic `E ⟶ Spec k` of a
Weierstrass curve is smooth, then its affine coordinate ring is smooth over `k`: the open
immersion `Spec k[x, y]/(f) ⟶ E` of the chart `D₊(z)` composed with the projection is `Spec` of
the structure map. -/
theorem algebraSmooth_coordinateRing_of_smooth (h : Smooth (projectionOf C)) :
    Algebra.Smooth k C.toAffine.CoordinateRing := by
  have : Smooth (chartZ C ≫ projectionOf C) := inferInstance
  rw [chartZ_projectionOf, HasRingHomProperty.Spec_iff (P := @Smooth)] at this
  exact RingHom.smooth_algebraMap.mp this

/-- **A Weierstrass cubic smooth over a field has invertible discriminant.**  The plane curve
`k[x, y]/(f)` is the affine coordinate ring, smooth over `k` by
`algebraSmooth_coordinateRing_of_smooth`, so `Δ ≠ 0` by
`Stacks.WeierstrassDiscriminant.Δ_ne_zero_of_smooth`. -/
theorem isUnit_Δ_of_smooth (h : Smooth (projectionOf C)) : IsUnit C.Δ := by
  have := algebraSmooth_coordinateRing_of_smooth C h
  have := Algebra.Smooth.of_equiv (coordinateRingEquiv C)
  exact isUnit_iff_ne_zero.mpr Stacks.WeierstrassDiscriminant.Δ_ne_zero_of_smooth

/-- A Weierstrass curve over a field whose plane cubic is smooth is an elliptic curve. -/
theorem isElliptic_of_smooth [h : Smooth (projectionOf C)] : C.IsElliptic :=
  ⟨isUnit_Δ_of_smooth C h⟩

end AlgebraicGeometry.ModuliEllipticCurves.Weierstrass
