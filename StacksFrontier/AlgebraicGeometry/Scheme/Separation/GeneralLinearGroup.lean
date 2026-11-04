module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The rank-two general linear scheme

For a commutative ring `k`, the rank-two general linear scheme `GL₂` is the spectrum of the
polynomial ring in the four entries of a generic two-by-two matrix, with the determinant of that
matrix inverted:

`GL₂ = Spec k[a, b, c, d][1 / (ad - bc)]`.

The two entries `a`, `b` of the first row of the generic matrix generate the unit ideal of the
coordinate ring, so their basic opens cover `GL₂`.

## Main definitions

* `AlgebraicGeometry.generalLinearTwoDeterminant`: the determinant of the generic two-by-two
  matrix.
* `AlgebraicGeometry.generalLinearTwoCoordinateRing`: the localized coordinate ring.
* `AlgebraicGeometry.generalLinearTwoCoordinate`: a coordinate function in that ring.
* `AlgebraicGeometry.generalLinearTwoScheme`: the rank-two general linear scheme over `k`.

## Main results

* `AlgebraicGeometry.span_firstRow_eq_top`: the two entries of the first row generate the unit
  ideal.
* `AlgebraicGeometry.iSup_basicOpen_firstRow_eq_top`: their basic opens cover the spectrum.

## References

* [Stacks Project, Tag 01KX](https://stacks.math.columbia.edu/tag/01KX)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry

universe u

/-- The determinant of the generic two-by-two matrix over `k`. -/
public abbrev generalLinearTwoDeterminant (k : Type u) [CommRing k] :
    MvPolynomial (Fin 2 × Fin 2) k :=
  Matrix.det (Matrix.mvPolynomialX (Fin 2) (Fin 2) k)

/-- The coordinate ring `k[a,b,c,d,1/(ad-bc)]` of the rank-two general linear scheme. -/
public abbrev generalLinearTwoCoordinateRing (k : Type u) [CommRing k] :=
  Localization.Away (generalLinearTwoDeterminant k)

/-- The `(i,j)` coordinate of the generic matrix in the coordinate ring of `GL₂`. -/
public abbrev generalLinearTwoCoordinate (k : Type u) [CommRing k] (i j : Fin 2) :
    generalLinearTwoCoordinateRing k :=
  algebraMap (MvPolynomial (Fin 2 × Fin 2) k) (generalLinearTwoCoordinateRing k)
    (MvPolynomial.X (i, j))

/-- The rank-two general linear scheme over `k`. -/
@[stacks 01KX "gl2"]
public abbrev generalLinearTwoScheme (k : Type u) [CommRing k] : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Spec (CommRingCat.of (generalLinearTwoCoordinateRing k))

variable (k : Type u) [CommRing k]

/-- The two entries in the first row of the generic invertible two-by-two matrix generate the
unit ideal in its coordinate ring. -/
public lemma span_firstRow_eq_top :
    Ideal.span (Set.range fun j : Fin 2 ↦ generalLinearTwoCoordinate k 0 j) = ⊤ := by
  refine Ideal.eq_top_of_isUnit_mem _ ?_
    (IsLocalization.Away.algebraMap_isUnit (generalLinearTwoDeterminant k))
  show algebraMap _ _ ((Matrix.mvPolynomialX (Fin 2) (Fin 2) k).det) ∈ _
  rw [Matrix.det_fin_two, map_sub, map_mul, map_mul]
  exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨0, rfl⟩))
    (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨1, rfl⟩))

/-- The basic opens defined by the two entries in the first row cover the spectrum of the
coordinate ring of `GL₂`. -/
public lemma iSup_basicOpen_firstRow_eq_top :
    (⨆ j : Fin 2, PrimeSpectrum.basicOpen (generalLinearTwoCoordinate k 0 j)) = ⊤ :=
  PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr (span_firstRow_eq_top k)

end AlgebraicGeometry
