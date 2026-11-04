module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.RingHom.Locally
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassCubicCharts

/-!
# A Weierstrass cubic with invertible discriminant is smooth of relative dimension one

Let `R` be a ring and `E ⊂ P²_R` the plane cubic of a Weierstrass equation over `R` whose
discriminant `Δ` is a unit. This file proves that the projection `E → Spec R` is smooth of
relative dimension one, the second of the conditions of [Stacks, Tag 072J] that
[Stacks, Tag 072S] asserts for the Weierstrass family.

## Main definitions

* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.planePresentation`: the presentation of
  `R[x₀, x₁] ⧸ (f)` by two variables and one relation, with the relation matched to `xᵢ`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.planeAwayPresentation`: the submersive
  presentation of `(R[x₀, x₁] ⧸ (f))[1/(∂f/∂xᵢ)]` over `R`.

## Main results

* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass`
  `.locally_isStandardSmoothOfRelativeDimension_plane`: if `∂f/∂x₀` and `∂f/∂x₁` generate the
  unit ideal of `R[x₀, x₁] ⧸ (f)`, then `R → R[x₀, x₁] ⧸ (f)` is locally standard smooth of
  relative dimension one.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.Δ_eq_jacobian_zChart`: an explicit
  expression of `Δ` as a combination of the two partial derivatives of the affine Weierstrass
  equation at any of its solutions.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.span_jacobian_zChart_eq_top` and
  `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.span_jacobian_yChart_eq_top`: when `Δ` is a
  unit, the partial derivatives of the equations of the charts `z = 1` and `y = 1` generate the
  unit ideal at every solution.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.smoothOfRelativeDimension_projectionOf`:
  the projection `E → Spec R` is smooth of relative dimension one when `Δ` is a unit.

## References

* [Stacks Project, Tag 072S](https://stacks.math.columbia.edu/tag/072S)
* [Stacks Project, Tag 072J](https://stacks.math.columbia.edu/tag/072J)
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial

universe u

namespace AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

section Algebra

variable {R : Type u} [CommRing R] (f : MvPolynomial (Fin 2) R) (i : Fin 2)

/-- The presentation of `R[x₀, x₁] ⧸ (f)` by its two variables and the single relation `f`,
with the relation matched to the variable `xᵢ`. -/
def planePresentation :
    Algebra.PreSubmersivePresentation R (MvPolynomial (Fin 2) R ⧸ Ideal.span {f}) (Fin 2) (Fin 1) :=
  (Algebra.PreSubmersivePresentation.naive (v := fun _ : Fin 1 => f) (fun _ => i)
    (Function.injective_of_subsingleton _)).ofAlgEquiv
    (Ideal.quotientEquivAlgOfEq R (by rw [Set.range_const]))

/-- The Jacobian of `planePresentation f i` is the class of `∂f/∂xᵢ`. -/
theorem planePresentation_jacobian :
    (planePresentation f i).jacobian = Ideal.Quotient.mk _ (pderiv i f) := by
  rw [planePresentation, Algebra.PreSubmersivePresentation.jacobian_ofAlgEquiv,
    Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Matrix.det_unique,
    Algebra.PreSubmersivePresentation.jacobiMatrix_naive]
  rfl

variable (T : Type*) [CommRing T] [Algebra (MvPolynomial (Fin 2) R ⧸ Ideal.span {f}) T]
  [Algebra R T] [IsScalarTower R (MvPolynomial (Fin 2) R ⧸ Ideal.span {f}) T]
  [IsLocalization.Away (Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f)) T]

/-- The submersive presentation of `(R[x₀, x₁] ⧸ (f))[1/(∂f/∂xᵢ)]` over `R`: the presentation of
`R[x₀, x₁] ⧸ (f)` by `planePresentation` followed by that of the localization. -/
def planeAwayPresentation :
    Algebra.SubmersivePresentation R T (Unit ⊕ Fin 2) (Unit ⊕ Fin 1) where
  __ := (Algebra.PreSubmersivePresentation.localizationAway T
    (Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f))).comp (planePresentation f i)
  jacobian_isUnit := by
    rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.PreSubmersivePresentation.localizationAway_jacobian, planePresentation_jacobian,
      Algebra.smul_def]
    exact (IsLocalization.Away.algebraMap_isUnit _).mul (IsLocalization.Away.algebraMap_isUnit _)

/-- The presentation `planeAwayPresentation f i T` has dimension one. -/
theorem planeAwayPresentation_dimension : (planeAwayPresentation f i T).dimension = 1 := by
  simp [Algebra.Presentation.dimension]

include f i in
/-- **The basic open `D(∂f/∂xᵢ)` of a plane curve is standard smooth of relative dimension
one.** -/
theorem isStandardSmoothOfRelativeDimension_planeAway :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R T :=
  (planeAwayPresentation f i T).isStandardSmoothOfRelativeDimension
    (planeAwayPresentation_dimension f i T)

/-- **A plane curve whose partial derivatives generate the unit ideal is locally standard smooth
of relative dimension one.** If the classes of `∂f/∂x₀` and `∂f/∂x₁` generate the unit ideal of
`R[x₀, x₁] ⧸ (f)`, then `R → R[x₀, x₁] ⧸ (f)` is, locally on the target, standard smooth of
relative dimension one. -/
theorem locally_isStandardSmoothOfRelativeDimension_plane {R : Type u} [CommRing R]
    (f : MvPolynomial (Fin 2) R)
    (h : Ideal.span {Ideal.Quotient.mk (Ideal.span {f}) (pderiv 0 f),
      Ideal.Quotient.mk (Ideal.span {f}) (pderiv 1 f)} = ⊤) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap R (MvPolynomial (Fin 2) R ⧸ Ideal.span {f})) := by
  refine ⟨_, h, fun t ht => ?_⟩
  rw [← IsScalarTower.algebraMap_eq]
  refine (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := 1)).mpr ?_
  rcases ht with rfl | rfl
  · exact isStandardSmoothOfRelativeDimension_planeAway f 0 _
  · exact isStandardSmoothOfRelativeDimension_planeAway f 1 _

end Algebra

section Certificates

/-- **The discriminant lies in the Jacobian ideal of the affine Weierstrass equation.** If
`(u, v)` satisfies `v² + a₁uv + a₃v = u³ + a₂u² + a₄u + a₆`, then `Δ` is a combination of the two
partial derivatives `a₁v - 3u² - 2a₂u - a₄` and `2v + a₁u + a₃` of the equation at `(u, v)`. -/
theorem Δ_eq_jacobian_zChart {T : Type*} [CommRing T] (W : WeierstrassCurve T) (u v : T)
    (h : v ^ 2 + W.a₁ * u * v + W.a₃ * v - (u ^ 3 + W.a₂ * u ^ 2 + W.a₄ * u + W.a₆) = 0) :
    W.Δ =
      (-W.a₁ ^ 6 * u - W.a₁ ^ 5 * W.a₃ - W.a₁ ^ 5 * v - 10 * W.a₁ ^ 4 * W.a₂ * u - W.a₁ ^ 4 * W.a₄ +
      3 * W.a₁ ^ 4 * u ^ 2 - 8 * W.a₁ ^ 3 * W.a₂ * W.a₃ - 8 * W.a₁ ^ 3 * W.a₂ * v +
      36 * W.a₁ ^ 3 * W.a₃ * u - 32 * W.a₁ ^ 2 * W.a₂ ^ 2 * u - 8 * W.a₁ ^ 2 * W.a₂ * W.a₄ -
      48 * W.a₁ ^ 2 * W.a₂ * u ^ 2 + 30 * W.a₁ ^ 2 * W.a₃ ^ 2 + 24 * W.a₁ ^ 2 * W.a₃ * v +
      72 * W.a₁ ^ 2 * W.a₄ * u - 144 * W.a₁ ^ 2 * u ^ 3 - 8 * W.a₁ ^ 2 * v ^ 2 -
      16 * W.a₁ * W.a₂ ^ 2 * W.a₃ - 16 * W.a₁ * W.a₂ ^ 2 * v - 48 * W.a₁ * W.a₂ * W.a₃ * u -
      256 * W.a₁ * W.a₂ * u * v + 96 * W.a₁ * W.a₃ * W.a₄ - 288 * W.a₁ * W.a₃ * u ^ 2 +
      64 * W.a₁ * W.a₄ * v - 816 * W.a₁ * u ^ 2 * v - 32 * W.a₂ ^ 3 * u - 16 * W.a₂ ^ 2 * W.a₄ +
      16 * W.a₂ ^ 2 * u ^ 2 - 72 * W.a₂ * W.a₃ ^ 2 - 288 * W.a₂ * W.a₃ * v + 160 * W.a₂ * W.a₄ * u +
      192 * W.a₂ * u ^ 3 - 288 * W.a₂ * v ^ 2 - 216 * W.a₃ ^ 2 * u - 864 * W.a₃ * u * v +
      64 * W.a₄ ^ 2 + 240 * W.a₄ * u ^ 2 + 144 * u ^ 4 - 864 * u * v ^ 2) *
        (W.a₁ * v - (3 * u ^ 2 + 2 * W.a₂ * u + W.a₄)) +
      (-W.a₁ ^ 5 * W.a₂ * u - 2 * W.a₁ ^ 5 * u ^ 2 - W.a₁ ^ 4 * W.a₂ * W.a₃ -
      2 * W.a₁ ^ 4 * W.a₂ * v - W.a₁ ^ 4 * W.a₃ * u - 2 * W.a₁ ^ 4 * u * v -
      8 * W.a₁ ^ 3 * W.a₂ ^ 2 * u - 12 * W.a₁ ^ 3 * W.a₂ * u ^ 2 + W.a₁ ^ 3 * W.a₃ ^ 2 +
      4 * W.a₁ ^ 3 * W.a₃ * v + 9 * W.a₁ ^ 3 * u ^ 3 + 4 * W.a₁ ^ 3 * v ^ 2 -
      8 * W.a₁ ^ 2 * W.a₂ ^ 2 * W.a₃ - 16 * W.a₁ ^ 2 * W.a₂ ^ 2 * v +
      24 * W.a₁ ^ 2 * W.a₂ * W.a₃ * u + 48 * W.a₁ ^ 2 * W.a₂ * u * v +
      63 * W.a₁ ^ 2 * W.a₃ * u ^ 2 + 126 * W.a₁ ^ 2 * u ^ 2 * v - 16 * W.a₁ * W.a₂ ^ 3 * u -
      144 * W.a₁ * W.a₂ ^ 2 * u ^ 2 + 36 * W.a₁ * W.a₂ * W.a₃ ^ 2 + 144 * W.a₁ * W.a₂ * W.a₃ * v -
      432 * W.a₁ * W.a₂ * u ^ 3 + 144 * W.a₁ * W.a₂ * v ^ 2 + 27 * W.a₁ * W.a₃ ^ 2 * u +
      108 * W.a₁ * W.a₃ * u * v - 432 * W.a₁ * u ^ 4 + 108 * W.a₁ * u * v ^ 2 -
      16 * W.a₂ ^ 3 * W.a₃ - 32 * W.a₂ ^ 3 * v - 144 * W.a₂ ^ 2 * W.a₃ * u -
      288 * W.a₂ ^ 2 * u * v - 432 * W.a₂ * W.a₃ * u ^ 2 - 864 * W.a₂ * u ^ 2 * v - 27 * W.a₃ ^ 3 -
      162 * W.a₃ ^ 2 * v - 432 * W.a₃ * u ^ 3 - 324 * W.a₃ * v ^ 2 - 864 * u ^ 3 * v -
      216 * v ^ 3) *
        (2 * v + W.a₁ * u + W.a₃) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  linear_combination
    (W.a₁ ^ 6 + 12 * W.a₁ ^ 4 * W.a₂ - 36 * W.a₁ ^ 3 * W.a₃ + 48 * W.a₁ ^ 2 * W.a₂ ^ 2 -
    72 * W.a₁ ^ 2 * W.a₄ - 144 * W.a₁ * W.a₂ * W.a₃ + 432 * W.a₁ * u * v + 64 * W.a₂ ^ 3 -
    288 * W.a₂ * W.a₄ - 432 * W.a₂ * u ^ 2 + 216 * W.a₃ ^ 2 + 432 * W.a₃ * v - 432 * W.a₄ * u +
    432 * W.a₆ - 432 * u ^ 3 + 432 * v ^ 2) * h

/-- **At the point at infinity the partial derivative in `z` is a unit.** If `(u, v)`
satisfies the Weierstrass equation of the chart `y = 1`, then `1` is a combination of its partial
derivative in `v` and of `v`. -/
theorem one_eq_yChart {T : Type*} [CommRing T] (W : WeierstrassCurve T) (u v : T)
    (h : v + W.a₁ * u * v + W.a₃ * v ^ 2 -
      (u ^ 3 + W.a₂ * u ^ 2 * v + W.a₄ * u * v ^ 2 + W.a₆ * v ^ 3) = 0) :
    1 = (1 - (W.a₁ * u - W.a₂ * u ^ 2) + (W.a₁ * u - W.a₂ * u ^ 2) ^ 2) *
        (1 + W.a₁ * u + 2 * W.a₃ * v - (W.a₂ * u ^ 2 + 2 * W.a₄ * u * v + 3 * W.a₆ * v ^ 2)) +
      v *
        (-u ^ 5 * W.a₂ ^ 4 + 2 * u ^ 5 * W.a₂ ^ 2 * W.a₄ - u ^ 4 * v * W.a₂ ^ 3 * W.a₄ +
        3 * u ^ 4 * v * W.a₂ ^ 2 * W.a₆ + 4 * u ^ 4 * W.a₁ * W.a₂ ^ 3 -
        4 * u ^ 4 * W.a₁ * W.a₂ * W.a₄ - 2 * u ^ 4 * W.a₂ ^ 2 * W.a₃ -
        u ^ 3 * v ^ 2 * W.a₂ ^ 3 * W.a₆ + 3 * u ^ 3 * v * W.a₁ * W.a₂ ^ 2 * W.a₄ -
        6 * u ^ 3 * v * W.a₁ * W.a₂ * W.a₆ + u ^ 3 * v * W.a₂ ^ 3 * W.a₃ -
        6 * u ^ 3 * W.a₁ ^ 2 * W.a₂ ^ 2 + 2 * u ^ 3 * W.a₁ ^ 2 * W.a₄ +
        4 * u ^ 3 * W.a₁ * W.a₂ * W.a₃ + u ^ 3 * W.a₂ ^ 3 + 2 * u ^ 3 * W.a₂ * W.a₄ +
        3 * u ^ 2 * v ^ 2 * W.a₁ * W.a₂ ^ 2 * W.a₆ - 3 * u ^ 2 * v * W.a₁ ^ 2 * W.a₂ * W.a₄ +
        3 * u ^ 2 * v * W.a₁ ^ 2 * W.a₆ - 3 * u ^ 2 * v * W.a₁ * W.a₂ ^ 2 * W.a₃ +
        3 * u ^ 2 * v * W.a₂ * W.a₆ + 4 * u ^ 2 * W.a₁ ^ 3 * W.a₂ - 2 * u ^ 2 * W.a₁ ^ 2 * W.a₃ -
        3 * u ^ 2 * W.a₁ * W.a₂ ^ 2 - 2 * u ^ 2 * W.a₁ * W.a₄ - 2 * u ^ 2 * W.a₂ * W.a₃ -
        3 * u * v ^ 2 * W.a₁ ^ 2 * W.a₂ * W.a₆ + u * v * W.a₁ ^ 3 * W.a₄ +
        3 * u * v * W.a₁ ^ 2 * W.a₂ * W.a₃ - 3 * u * v * W.a₁ * W.a₆ - u * W.a₁ ^ 4 +
        3 * u * W.a₁ ^ 2 * W.a₂ + 2 * u * W.a₁ * W.a₃ + 2 * u * W.a₄ + v ^ 2 * W.a₁ ^ 3 * W.a₆ -
        v * W.a₁ ^ 3 * W.a₃ + 3 * v * W.a₆ - W.a₁ ^ 3 - 2 * W.a₃) := by
  linear_combination (W.a₁ - W.a₂ * u) ^ 3 * h

/-- An element expressed as a combination of two members of an ideal lies in the ideal. -/
private theorem mem_of_eq_mul_add_mul {T : Type*} [CommRing T] {I : Ideal T} {a b : T}
    (ha : a ∈ I) (hb : b ∈ I) {B C d : T} (h : d = B * a + C * b) : d ∈ I :=
  h ▸ I.add_mem (I.mul_mem_left _ ha) (I.mul_mem_left _ hb)

/-- **The partial derivatives of an affine Weierstrass equation with invertible discriminant
generate the unit ideal at a solution.** -/
theorem span_jacobian_zChart_eq_top {T : Type*} [CommRing T] (W : WeierstrassCurve T)
    (hΔ : IsUnit W.Δ) (u v : T)
    (h : v ^ 2 + W.a₁ * u * v + W.a₃ * v - (u ^ 3 + W.a₂ * u ^ 2 + W.a₄ * u + W.a₆) = 0) :
    Ideal.span {W.a₁ * v - (3 * u ^ 2 + 2 * W.a₂ * u + W.a₄), 2 * v + W.a₁ * u + W.a₃} = ⊤ := by
  exact Ideal.eq_top_of_isUnit_mem _ (mem_of_eq_mul_add_mul (Ideal.subset_span (by simp))
    (Ideal.subset_span (by simp)) (Δ_eq_jacobian_zChart W u v h)) hΔ

/-- **The partial derivatives of the Weierstrass equation of the chart `y = 1` with invertible
discriminant generate the unit ideal at a solution.** -/
theorem span_jacobian_yChart_eq_top {T : Type u} [CommRing T] (W : WeierstrassCurve T)
    (hΔ : IsUnit W.Δ) (u v : T)
    (h : v + W.a₁ * u * v + W.a₃ * v ^ 2 -
      (u ^ 3 + W.a₂ * u ^ 2 * v + W.a₄ * u * v ^ 2 + W.a₆ * v ^ 3) = 0) :
    Ideal.span {W.a₁ * v - (3 * u ^ 2 + 2 * W.a₂ * u * v + W.a₄ * v ^ 2),
      1 + W.a₁ * u + 2 * W.a₃ * v - (W.a₂ * u ^ 2 + 2 * W.a₄ * u * v + 3 * W.a₆ * v ^ 2)} = ⊤ := by
  set gX := W.a₁ * v - (3 * u ^ 2 + 2 * W.a₂ * u * v + W.a₄ * v ^ 2)
  set gZ := 1 + W.a₁ * u + 2 * W.a₃ * v - (W.a₂ * u ^ 2 + 2 * W.a₄ * u * v + 3 * W.a₆ * v ^ 2)
  set J := Ideal.span {gX, gZ}
  have hX : gX ∈ J := Ideal.subset_span (by simp)
  have hZ : gZ ∈ J := Ideal.subset_span (by simp)
  have h1 : J ⊔ Ideal.span {v} = ⊤ := by
    rw [Ideal.eq_top_iff_one, one_eq_yChart W u v h]
    exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ hZ))
      (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self v)))
  obtain ⟨n, hn⟩ : ∃ n : ℕ, v ^ n ∈ J := by
    let L := Localization.Away v
    let φ := algebraMap T L
    let zi := IsLocalization.Away.invSelf (S := L) v
    have hzi : φ v * zi = 1 := IsLocalization.Away.mul_invSelf v
    have hg := congrArg φ h
    simp only [map_add, map_sub, map_mul, map_pow, map_zero] at hg
    have hf : zi ^ 2 + (W.map φ).a₁ * (φ u * zi) * zi + (W.map φ).a₃ * zi -
        ((φ u * zi) ^ 3 + (W.map φ).a₂ * (φ u * zi) ^ 2 + (W.map φ).a₄ * (φ u * zi) +
          (W.map φ).a₆) = 0 := by
      simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
        WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
      linear_combination zi ^ 3 * hg + (φ u ^ 2 * φ W.a₂ * zi ^ 2 + φ u * φ v * φ W.a₄ * zi ^ 2 -
        φ u * φ W.a₁ * zi ^ 2 + φ u * φ W.a₄ * zi + φ v ^ 2 * φ W.a₆ * zi ^ 2 -
        φ v * φ W.a₃ * zi ^ 2 + φ v * φ W.a₆ * zi - φ W.a₃ * zi + φ W.a₆ - zi ^ 2) * hzi
    have hfx : (W.map φ).a₁ * zi - (3 * (φ u * zi) ^ 2 + 2 * (W.map φ).a₂ * (φ u * zi) +
        (W.map φ).a₄) = zi ^ 2 * φ gX := by
      simp only [gX, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄,
        map_add, map_sub, map_mul, map_pow, map_ofNat]
      linear_combination (2 * φ u * φ W.a₂ * zi + φ v * φ W.a₄ * zi - φ W.a₁ * zi + φ W.a₄) * hzi
    have hfy : 2 * zi + (W.map φ).a₁ * (φ u * zi) + (W.map φ).a₃ =
        -(zi ^ 2 * φ u) * φ gX - (zi ^ 2 * φ v) * φ gZ := by
      simp only [gX, gZ, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, map_add, map_sub,
        map_mul, map_pow, map_ofNat, map_one]
      linear_combination 3 * zi ^ 2 * hg +
        (-φ u * φ W.a₁ * zi - φ v * φ W.a₃ * zi - φ W.a₃ - 2 * zi) * hzi
    obtain ⟨B, C, hBC⟩ : ∃ B C : L, (W.map φ).Δ =
        B * ((W.map φ).a₁ * zi - (3 * (φ u * zi) ^ 2 + 2 * (W.map φ).a₂ * (φ u * zi) +
          (W.map φ).a₄)) + C * (2 * zi + (W.map φ).a₁ * (φ u * zi) + (W.map φ).a₃) :=
      ⟨_, _, Δ_eq_jacobian_zChart (W.map φ) (φ u * zi) zi hf⟩
    have hmem : φ W.Δ ∈ J.map φ := by
      rw [← WeierstrassCurve.map_Δ, hBC, hfx, hfy]
      exact mem_of_eq_mul_add_mul (Ideal.mem_map_of_mem φ hX) (Ideal.mem_map_of_mem φ hZ)
        (B := B * zi ^ 2 - C * (zi ^ 2 * φ u)) (C := -(C * (zi ^ 2 * φ v))) (by ring)
    obtain ⟨_, ⟨n, rfl⟩, hm⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers v) L J W.Δ).mp hmem
    obtain ⟨w, hw⟩ := hΔ.exists_left_inv
    refine ⟨n, ?_⟩
    have := J.mul_mem_left w hm
    rwa [mul_left_comm, hw, mul_one] at this
  have h2 := Ideal.sup_pow_eq_top (n := n) h1
  rwa [Ideal.span_singleton_pow, sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem J).mpr hn)]
    at h2

end Certificates

section Charts

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- **The affine chart `z = 1` of a Weierstrass cubic with invertible discriminant is locally
standard smooth of relative dimension one.** Here `R[x, y] ⧸ (f)` is presented with `x = x₀`,
`y = x₁` and `f = y² + a₁xy + a₃y - (x³ + a₂x² + a₄x + a₆)`. -/
theorem locally_isStandardSmoothOfRelativeDimension_zChart (hΔ : IsUnit W.Δ) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap R (MvPolynomial (Fin 2) R ⧸ Ideal.span {X 1 ^ 2 + C W.a₁ * X 0 * X 1 +
        C W.a₃ * X 1 - (X 0 ^ 3 + C W.a₂ * X 0 ^ 2 + C W.a₄ * X 0 + C W.a₆)})) := by
  set f : MvPolynomial (Fin 2) R := X 1 ^ 2 + C W.a₁ * X 0 * X 1 + C W.a₃ * X 1 -
    (X 0 ^ 3 + C W.a₂ * X 0 ^ 2 + C W.a₄ * X 0 + C W.a₆)
  refine locally_isStandardSmoothOfRelativeDimension_plane f ?_
  set φ := algebraMap R (MvPolynomial (Fin 2) R ⧸ Ideal.span {f})
  have hmk : ∀ a, Ideal.Quotient.mk (Ideal.span {f}) (C a) = φ a := fun _ => rfl
  have hf : (Ideal.Quotient.mk (Ideal.span {f}) (X 1)) ^ 2 +
      (W.map φ).a₁ * (Ideal.Quotient.mk _ (X 0)) * (Ideal.Quotient.mk _ (X 1)) +
      (W.map φ).a₃ * (Ideal.Quotient.mk _ (X 1)) - ((Ideal.Quotient.mk _ (X 0)) ^ 3 +
        (W.map φ).a₂ * (Ideal.Quotient.mk _ (X 0)) ^ 2 +
        (W.map φ).a₄ * (Ideal.Quotient.mk _ (X 0)) +
        (W.map φ).a₆) = 0 := by
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, ← hmk, ← map_pow, ← map_mul, ← map_add,
      ← map_sub]
    exact Ideal.Quotient.mk_singleton_self f
  have p0 : pderiv 0 f = C W.a₁ * X 1 - (3 * X 0 ^ 2 + 2 * C W.a₂ * X 0 + C W.a₄) := by
    simp [f, pderiv_X]
    ring
  have p1 : pderiv 1 f = 2 * X 1 + C W.a₁ * X 0 + C W.a₃ := by
    simp [f, pderiv_X]
  have e0 : Ideal.Quotient.mk (Ideal.span {f}) (pderiv 0 f) = (W.map φ).a₁ *
      (Ideal.Quotient.mk _ (X 1)) - (3 * (Ideal.Quotient.mk _ (X 0)) ^ 2 +
        2 * (W.map φ).a₂ * (Ideal.Quotient.mk _ (X 0)) + (W.map φ).a₄) := by
    rw [p0]
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄, ← hmk,
      map_sub, map_add, map_mul, map_pow, map_ofNat]
  have e1 : Ideal.Quotient.mk (Ideal.span {f}) (pderiv 1 f) = 2 * (Ideal.Quotient.mk _ (X 1)) +
      (W.map φ).a₁ * (Ideal.Quotient.mk _ (X 0)) + (W.map φ).a₃ := by
    rw [p1]
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, ← hmk, map_add, map_mul,
      map_ofNat]
  rw [e0, e1]
  exact span_jacobian_zChart_eq_top (W.map φ) (by rw [WeierstrassCurve.map_Δ]; exact hΔ.map φ)
    _ _ hf

/-- **The chart `y = 1` of a Weierstrass cubic with invertible discriminant is locally standard
smooth of relative dimension one.** Here `R[z, x] ⧸ (g)` is presented with `z = x₀`, `x = x₁` and
`g = x³ + a₂zx² + (a₄z² - a₁z)x - (z + a₃z² - a₆z³)`, which is minus the dehomogenization of the
Weierstrass cubic at `y = 1`. -/
theorem locally_isStandardSmoothOfRelativeDimension_yChart (hΔ : IsUnit W.Δ) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap R (MvPolynomial (Fin 2) R ⧸ Ideal.span {X 1 ^ 3 + C W.a₂ * X 0 * X 1 ^ 2 +
        (C W.a₄ * X 0 ^ 2 - C W.a₁ * X 0) * X 1 -
          (X 0 + C W.a₃ * X 0 ^ 2 - C W.a₆ * X 0 ^ 3)})) := by
  set g : MvPolynomial (Fin 2) R := X 1 ^ 3 + C W.a₂ * X 0 * X 1 ^ 2 +
    (C W.a₄ * X 0 ^ 2 - C W.a₁ * X 0) * X 1 - (X 0 + C W.a₃ * X 0 ^ 2 - C W.a₆ * X 0 ^ 3)
  refine locally_isStandardSmoothOfRelativeDimension_plane g ?_
  set φ := algebraMap R (MvPolynomial (Fin 2) R ⧸ Ideal.span {g})
  set u := Ideal.Quotient.mk (Ideal.span {g}) (X 1)
  set v := Ideal.Quotient.mk (Ideal.span {g}) (X 0)
  have hmk : ∀ a, Ideal.Quotient.mk (Ideal.span {g}) (C a) = φ a := fun _ => rfl
  have hg : v + (W.map φ).a₁ * u * v + (W.map φ).a₃ * v ^ 2 - (u ^ 3 + (W.map φ).a₂ * u ^ 2 * v +
      (W.map φ).a₄ * u * v ^ 2 + (W.map φ).a₆ * v ^ 3) = 0 := by
    have h0 := Ideal.Quotient.mk_singleton_self g
    simp only [g, map_add, map_sub, map_mul, map_pow, hmk] at h0
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
    linear_combination -h0
  have p0 : pderiv 0 g = C W.a₂ * X 1 ^ 2 + (2 * C W.a₄ * X 0 - C W.a₁) * X 1 -
      (1 + 2 * C W.a₃ * X 0 - 3 * C W.a₆ * X 0 ^ 2) := by
    simp [g, pderiv_X]
    ring
  have p1 : pderiv 1 g = 3 * X 1 ^ 2 + 2 * C W.a₂ * X 0 * X 1 + (C W.a₄ * X 0 ^ 2 -
      C W.a₁ * X 0) := by
    simp [g, pderiv_X]
    ring
  have e0 : Ideal.Quotient.mk (Ideal.span {g}) (pderiv 0 g) = -(1 + (W.map φ).a₁ * u +
      2 * (W.map φ).a₃ * v - ((W.map φ).a₂ * u ^ 2 + 2 * (W.map φ).a₄ * u * v +
        3 * (W.map φ).a₆ * v ^ 2)) := by
    rw [p0]
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, map_sub, map_add, map_mul, map_pow,
      map_ofNat, map_one, hmk]
    ring
  have e1 : Ideal.Quotient.mk (Ideal.span {g}) (pderiv 1 g) = -((W.map φ).a₁ * v -
      (3 * u ^ 2 + 2 * (W.map φ).a₂ * u * v + (W.map φ).a₄ * v ^ 2)) := by
    rw [p1]
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄,
      map_sub, map_add, map_mul, map_pow, map_ofNat, hmk]
    ring
  have key := span_jacobian_yChart_eq_top (W.map φ)
    (by rw [WeierstrassCurve.map_Δ]; exact hΔ.map φ) u v hg
  rw [e0, e1, Ideal.span_insert_neg, Ideal.span_pair_neg, Ideal.span_pair_comm]
  exact key

/-- If `R → R[x₀, x₁] ⧸ (p)` is locally standard smooth of relative dimension one, for `p` read
in `R[x₀, x₁]` through `Polynomial.Bivariate.equivMvPolynomial`, then so is `R → R[X][Y] ⧸ (p)`. -/
theorem locally_isStandardSmoothOfRelativeDimension_adjoinRoot
    (p : Polynomial (Polynomial R))
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap R (MvPolynomial (Fin 2) R ⧸
        Ideal.span {Polynomial.Bivariate.equivMvPolynomial R p}))) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap R (AdjoinRoot p)) := by
  let e : AdjoinRoot p ≃ₐ[R] MvPolynomial (Fin 2) R ⧸
      Ideal.span {Polynomial.Bivariate.equivMvPolynomial R p} :=
    Ideal.quotientEquivAlg (Ideal.span {p}) _ (Polynomial.Bivariate.equivMvPolynomial R)
      (by rw [Ideal.map_span, Set.image_singleton]; rfl)
  have := (RingHom.locally_respectsIso
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso).1 _ e.symm.toRingEquiv h
  convert this
  exact RingHom.ext fun a => (e.symm.commutes a).symm

/-- **The coordinate ring of the affine chart `D₊(z)` is locally standard smooth of relative
dimension one over `R`** when the discriminant is invertible. -/
theorem locally_isStandardSmoothOfRelativeDimension_coordinateRing (hΔ : IsUnit W.Δ) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap R W.toAffine.CoordinateRing) := by
  refine locally_isStandardSmoothOfRelativeDimension_adjoinRoot _ ?_
  have : Polynomial.Bivariate.equivMvPolynomial R W.toAffine.polynomial = X 1 ^ 2 +
      C W.a₁ * X 0 * X 1 + C W.a₃ * X 1 - (X 0 ^ 3 + C W.a₂ * X 0 ^ 2 + C W.a₄ * X 0 + C W.a₆) := by
    simp [WeierstrassCurve.Affine.polynomial]
    ring
  rw [this]
  exact locally_isStandardSmoothOfRelativeDimension_zChart W hΔ

/-- **The coordinate ring of the chart `D₊(y)` is locally standard smooth of relative dimension
one over `R`** when the discriminant is invertible. -/
theorem locally_isStandardSmoothOfRelativeDimension_chartYRing (hΔ : IsUnit W.Δ) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap R (ChartYRing W)) := by
  refine locally_isStandardSmoothOfRelativeDimension_adjoinRoot _ ?_
  have : Polynomial.Bivariate.equivMvPolynomial R (chartYPolynomial W) = X 1 ^ 3 +
      C W.a₂ * X 0 * X 1 ^ 2 + (C W.a₄ * X 0 ^ 2 - C W.a₁ * X 0) * X 1 -
        (X 0 + C W.a₃ * X 0 ^ 2 - C W.a₆ * X 0 ^ 3) := by
    simp [chartYPolynomial]
  rw [this]
  exact locally_isStandardSmoothOfRelativeDimension_yChart W hΔ

end Charts

section Scheme

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- **A Weierstrass cubic with invertible discriminant is smooth of relative dimension one over
its base.** -/
@[stacks 072S "f_W is smooth of relative dimension one"]
theorem smoothOfRelativeDimension_projectionOf (hΔ : IsUnit W.Δ) :
    SmoothOfRelativeDimension 1 (projectionOf W) := by
  let : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} 1) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1))
  let 𝒰 : (projOf W).OpenCover := Scheme.Cover.mkOfCovers Bool
    (fun b => Bool.rec (Spec (CommRingCat.of (ChartYRing W)))
      (Spec (CommRingCat.of W.toAffine.CoordinateRing)) b)
    (fun b => Bool.rec (motive := fun b => Bool.rec (Spec (CommRingCat.of (ChartYRing W)))
      (Spec (CommRingCat.of W.toAffine.CoordinateRing)) b ⟶ projOf W) (chartY W) (chartZ W) b)
    (fun x => by
      have hx : x ∈ Set.range (chartZ W) ∪ Set.range (chartY W) := by
        rw [range_chartZ_union_range_chartY]; trivial
      rcases hx with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact ⟨true, y, hy⟩
      · exact ⟨false, y, hy⟩)
    (fun b => by cases b <;> infer_instance)
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension.{u} 1) 𝒰 fun b => ?_
  cases b
  · show SmoothOfRelativeDimension 1 (chartY W ≫ projectionOf W)
    rw [chartY_projectionOf]
    exact (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension.{u} 1)).mpr
      (locally_isStandardSmoothOfRelativeDimension_chartYRing W hΔ)
  · show SmoothOfRelativeDimension 1 (chartZ W ≫ projectionOf W)
    rw [chartZ_projectionOf]
    exact (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension.{u} 1)).mpr
      (locally_isStandardSmoothOfRelativeDimension_coordinateRing W hΔ)

end Scheme

end AlgebraicGeometry.ModuliEllipticCurves.Weierstrass
