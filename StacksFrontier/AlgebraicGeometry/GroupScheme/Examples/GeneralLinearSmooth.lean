module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.GeneralLinear
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.LocalizationAwayPolynomial
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The general linear group scheme is smooth over any base

The coordinate ring of `GL_n` over the integers is the polynomial ring on the `n²` entries of a
generic matrix with the determinant inverted, so `GL_n` is the basic open `D(det)` of affine
`n²`-space over `ℤ`. A basic open of affine space is a smooth algebra over the base, so the
structure morphism `GL_n → Spec ℤ` is smooth; and `GL_n` over an arbitrary base scheme `S` is
obtained from it by base change, under which smoothness is stable. In particular the group
scheme `GL_n` over the spectrum of a field is smooth, with no assumption on the field.

This is the same argument that makes the rank-two general linear scheme of
`StacksFrontier.AlgebraicGeometry.Scheme.Separation.GeneralLinearGroupSmooth` smooth: both
constructions are basic opens of affine space cut out by the invertibility of the generic
determinant, over `ℤ` here and over the base ring there, so both inherit smoothness from
`AlgebraicGeometry.smooth_Spec_map_algebraMap_of_isLocalization_away_mvPolynomial`. The two are
not identified here — that would need the coordinate ring over `k` to be recognized as the base
change of the coordinate ring over `ℤ` — so each carries its own statement.

## Main results

* `AlgebraicGeometry.smooth_generalLinearStructureMorphism`: `GL_n` is smooth over `Spec ℤ`.
* `AlgebraicGeometry.smooth_generalLinearBaseChange`: `GL_n` over an arbitrary base scheme is
  smooth.
* `AlgebraicGeometry.isDomain_generalLinearCoordinateRing`,
  `AlgebraicGeometry.irreducibleSpace_generalLinearScheme` and
  `AlgebraicGeometry.isIntegral_generalLinearScheme`: `GL_n` over the integers is irreducible
  and integral.

## Implementation notes

`AlgebraicGeometry.generalLinearBaseChange` is the pullback of the structure morphism along the
unique morphism to the spectrum of the integers, so its structure morphism is the second
projection of that pullback square, and smoothness of it is the base-change stability instance
for `AlgebraicGeometry.Smooth`.

## References

* [Stacks Project, Tag 022W](https://stacks.math.columbia.edu/tag/022W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **`GL_n` is smooth over the spectrum of the integers.** Its coordinate ring is the
polynomial ring on the `n²` entries of a generic matrix with the determinant inverted, so `GL_n`
is a basic open of affine `n²`-space over `ℤ`, and a basic open of affine space is smooth over
the base. -/
@[sga "3 XX 5.1" "special case"]
theorem smooth_generalLinearStructureMorphism (n : ℕ) :
    Smooth (generalLinearStructureMorphism.{u} n) :=
  smooth_Spec_map_algebraMap_of_isLocalization_away_mvPolynomial (ULift.{u} ℤ)
    (generalLinearDeterminant.{u} n) (generalLinearCoordinateRing.{u} n)

/-- **`GL_n` over an arbitrary base scheme is smooth.** It is the base change of `GL_n` over the
integers, and smoothness of morphisms of schemes is stable under base change. In particular this
covers `GL_n` over the spectrum of a field, for an arbitrary field. -/
@[sga "3 XX 5.1" "special case"]
theorem smooth_generalLinearBaseChange (n : ℕ) (S : Scheme.{u}) :
    Smooth (generalLinearBaseChange.{u} n S).hom := by
  have _ : Smooth (generalLinearStructureMorphism.{u} n) :=
    smooth_generalLinearStructureMorphism n
  change Smooth (pullback.snd (generalLinearStructureMorphism.{u} n) (specULiftZIsTerminal.from S))
  infer_instance

/-- **The coordinate ring of `GL_n` over the integers is a domain.** It is a localization of the
polynomial ring on the `n²` matrix entries away from the generic determinant, which is a nonzero
polynomial. -/
theorem isDomain_generalLinearCoordinateRing (n : ℕ) :
    IsDomain (generalLinearCoordinateRing.{u} n) :=
  let : IsDomain (ULift.{u} ℤ) := MulEquiv.isDomain ℤ (ULift.ringEquiv (R := ℤ)).toMulEquiv
  Localization.Away.isDomain (Matrix.det_mvPolynomialX_ne_zero (Fin n) (ULift.{u} ℤ))

/-- **`GL_n` over the integers is irreducible.** Its coordinate ring is a domain, so the zero
ideal is prime and is contained in every prime. -/
theorem irreducibleSpace_generalLinearScheme (n : ℕ) :
    IrreducibleSpace (generalLinearScheme.{u} n) :=
  let := isDomain_generalLinearCoordinateRing.{u} n
  inferInstanceAs (IrreducibleSpace (PrimeSpectrum (generalLinearCoordinateRing.{u} n)))

/-- **`GL_n` over the integers is an integral scheme.** Its coordinate ring is a domain. -/
theorem isIntegral_generalLinearScheme (n : ℕ) : IsIntegral (generalLinearScheme.{u} n) :=
  let := isDomain_generalLinearCoordinateRing.{u} n
  inferInstance

end AlgebraicGeometry

end
