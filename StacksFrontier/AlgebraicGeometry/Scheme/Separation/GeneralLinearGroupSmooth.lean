module

public import StacksFrontier.AlgebraicGeometry.Scheme.Separation.GeneralLinearGroupProjectiveLine
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.SmoothAffineRationalPoint
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The rank-two general linear scheme is smooth

The coordinate ring of `GL₂` over a commutative ring `k` is the polynomial ring on the four
entries of a generic two-by-two matrix with the determinant inverted, so `GL₂` is the basic open
`D(ad - bc)` of affine four-space over `k`, and the structure morphism `GL₂ → Spec k` is smooth
for an arbitrary base `k`.

Over a field `k`, `GL₂` is an integral scheme, a variety and geometrically integral over `k`, and
when `k` is infinite its `k`-rational points are dense.

## Main definitions

* `AlgebraicGeometry.generalLinearTwoStructureMap`: the structure morphism of `GL₂` over
  `Spec k`.
* `AlgebraicGeometry.generalLinearTwoIdentityPoint`: the `k`-rational point of `GL₂` given by
  the identity matrix.

## Main results

* `AlgebraicGeometry.smooth_generalLinearTwoCoordinateRing`: the coordinate ring of `GL₂` is a
  smooth `k`-algebra.
* `AlgebraicGeometry.smooth_generalLinearTwoStructureMap`: `GL₂` is smooth over `Spec k`, for an
  arbitrary commutative base ring `k`.
* `AlgebraicGeometry.isDomain_generalLinearTwoCoordinateRing`: over a field the coordinate ring
  is a domain.
* `AlgebraicGeometry.irreducibleSpace_generalLinearTwoScheme` and
  `AlgebraicGeometry.isIntegral_generalLinearTwoScheme`: over a field `GL₂` is irreducible and
  integral.
* `AlgebraicGeometry.isVariety_generalLinearTwoStructureMap`: over a field `GL₂` is a variety.
* `AlgebraicGeometry.geometricallyIntegral_generalLinearTwoStructureMap`: over a field `GL₂` is
  geometrically integral.
* `AlgebraicGeometry.dense_rationalPoints_generalLinearTwoScheme`: over an infinite field the
  `k`-rational points of `GL₂` are dense.

## References

* [Stacks Project, Tag 01KX](https://stacks.math.columbia.edu/tag/01KX)
* [Stacks Project, Tag 0CDW](https://stacks.math.columbia.edu/tag/0CDW)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

section Base

variable (k : Type u) [CommRing k]

/-- The structure morphism of the rank-two general linear scheme over `k`: `Spec` of the
structure map of its coordinate ring. -/
abbrev generalLinearTwoStructureMap :
    generalLinearTwoScheme k ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (generalLinearTwoCoordinateRing k)))

/-- The coordinate ring of `GL₂` is a smooth `k`-algebra. -/
theorem smooth_generalLinearTwoCoordinateRing :
    Algebra.Smooth k (generalLinearTwoCoordinateRing k) :=
  smooth_of_isLocalization_away_mvPolynomial k (generalLinearTwoDeterminant k)
    (generalLinearTwoCoordinateRing k)

/-- The structure morphism `GL₂ → Spec k` is smooth, for an arbitrary commutative ring `k`. -/
@[sga "3 XX 5.1" "special case"]
theorem smooth_generalLinearTwoStructureMap :
    Smooth (generalLinearTwoStructureMap k) :=
  smooth_Spec_map_algebraMap_of_isLocalization_away_mvPolynomial k
    (generalLinearTwoDeterminant k) (generalLinearTwoCoordinateRing k)

/-- The `k`-rational point of `GL₂` given by the identity matrix, as a homomorphism of
`k`-algebras from the coordinate ring to `k`. -/
def generalLinearTwoIdentityPoint : generalLinearTwoCoordinateRing k →ₐ[k] k where
  __ := generalLinearTwoHom k (1 : Matrix (Fin 2) (Fin 2) k) (by simp)
  commutes' r := generalLinearTwoHom_algebraMap k _ _ r

end Base

section Field

variable (k : Type u) [Field k]

/-- Over a field the coordinate ring of `GL₂` is a domain. -/
@[sga "3 XX 5.1" "special case"]
theorem isDomain_generalLinearTwoCoordinateRing :
    IsDomain (generalLinearTwoCoordinateRing k) :=
  Localization.Away.isDomain (Matrix.det_mvPolynomialX_ne_zero (Fin 2) k)

/-- Over a field `GL₂` is irreducible. -/
theorem irreducibleSpace_generalLinearTwoScheme :
    IrreducibleSpace (generalLinearTwoScheme k) :=
  let := isDomain_generalLinearTwoCoordinateRing k
  inferInstanceAs (IrreducibleSpace (PrimeSpectrum (generalLinearTwoCoordinateRing k)))

/-- Over a field `GL₂` is an integral scheme. -/
theorem isIntegral_generalLinearTwoScheme : IsIntegral (generalLinearTwoScheme k) :=
  let := isDomain_generalLinearTwoCoordinateRing k
  inferInstance

/-- Over a field `GL₂` is a variety. -/
@[sga "3 XX 5.1" "special case"]
theorem isVariety_generalLinearTwoStructureMap :
    IsVariety k (generalLinearTwoStructureMap k) :=
  let := isDomain_generalLinearTwoCoordinateRing k
  let := smooth_generalLinearTwoCoordinateRing k
  isVariety_Spec_map_algebraMap k (generalLinearTwoCoordinateRing k)

/-- Over a field `GL₂` is geometrically integral over `k`. -/
theorem geometricallyIntegral_generalLinearTwoStructureMap :
    GeometricallyIntegral (generalLinearTwoStructureMap k) :=
  let := isDomain_generalLinearTwoCoordinateRing k
  let := smooth_generalLinearTwoCoordinateRing k
  geometricallyIntegral_Spec_map_algebraMap_of_rationalPoint k
    (generalLinearTwoCoordinateRing k) (generalLinearTwoIdentityPoint k)

/-- Over an infinite field `k` the `k`-rational points of `GL₂`, the points in the image of a
section of the structure morphism, are dense. -/
theorem dense_rationalPoints_generalLinearTwoScheme [Infinite k] :
    Dense {x : generalLinearTwoScheme k |
      ∃ s : Spec (CommRingCat.of k) ⟶ generalLinearTwoScheme k,
        s ≫ generalLinearTwoStructureMap k = 𝟙 _ ∧ x ∈ Set.range s.base} :=
  dense_rationalPoints_Spec_of_isLocalization_away_mvPolynomial k
    (Matrix.det_mvPolynomialX_ne_zero (Fin 2) k) (generalLinearTwoCoordinateRing k)

end Field

end AlgebraicGeometry

end
