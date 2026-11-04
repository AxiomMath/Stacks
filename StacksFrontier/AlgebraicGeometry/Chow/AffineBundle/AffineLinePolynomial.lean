module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.AlgebraicGeometry.AffineSpace

/-!
# The affine line as the spectrum of a univariate polynomial ring

Mathlib's affine space `𝔸(n; S)` is indexed by an arbitrary type `n`, so the affine line over a
scheme `S` is `𝔸(ULift (Fin 1); S)`, and over an affine base it is identified by
`AlgebraicGeometry.AffineSpace.SpecIso` with the spectrum of the *multivariate* polynomial ring
`MvPolynomial (ULift (Fin 1)) R`. Every statement about the affine line that mentions a
polynomial — in particular the monic irreducible polynomial cutting out a point of the affine
line over a field — is phrased with `Polynomial`, not with `MvPolynomial`.

This file bridges the two. The ring-level identification is Mathlib's
`MvPolynomial.uniqueAlgEquiv`, available because `ULift (Fin 1)` is a `Unique` type; what is
added here is its scheme-level consequence, the identification of the affine line over `Spec R`
with `Spec R[T]` as a scheme over `Spec R`.

## Main definitions

* `Stacks.Chow.mvPolynomialULiftFinOneAlgEquiv` — `MvPolynomial (ULift (Fin 1)) R ≃ₐ[R] R[T]`,
  Mathlib's equivalence at the index type of the affine line.
* `Stacks.Chow.affineLineSpecIsoSpecPolynomial` — `𝔸(ULift (Fin 1); Spec R) ≅ Spec R[T]`.

## Main results

* `Stacks.Chow.affineLineSpecIsoSpecPolynomial_inv_over` — the identification is one of schemes
  over `Spec R`: it carries the structure morphism of the affine line to the morphism induced by
  `Polynomial.C`.

## References

* [Stacks Project, Tag 01M0](https://stacks.math.columbia.edu/tag/01M0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- Polynomials in the variables `ULift (Fin 1)` — the index type of Mathlib's affine line
`𝔸(ULift (Fin 1); S)` — are univariate polynomials. This is Mathlib's
`MvPolynomial.uniqueAlgEquiv` at that index type. -/
def mvPolynomialULiftFinOneAlgEquiv (R : Type u) [CommRing R] :
    MvPolynomial (ULift.{u} (Fin 1)) R ≃ₐ[R] Polynomial R :=
  MvPolynomial.uniqueAlgEquiv R (ULift.{u} (Fin 1))

/-- The equivalence `mvPolynomialULiftFinOneAlgEquiv R` sends the constant polynomial
`MvPolynomial.C r` to the constant polynomial `Polynomial.C r`. -/
@[simp]
theorem mvPolynomialULiftFinOneAlgEquiv_C (R : Type u) [CommRing R] (r : R) :
    mvPolynomialULiftFinOneAlgEquiv R (MvPolynomial.C r) = Polynomial.C r := by
  have := (mvPolynomialULiftFinOneAlgEquiv R).commutes r
  simpa [MvPolynomial.algebraMap_eq, Polynomial.algebraMap_eq] using this

/-- The one-variable polynomial ring over `R` indexed by `ULift (Fin 1)`, as an isomorphism of
commutative rings onto the univariate polynomial ring `R[T]`. -/
def mvPolynomialULiftFinOneIso (R : CommRingCat.{u}) :
    CommRingCat.of (MvPolynomial (ULift.{u} (Fin 1)) ↑R) ≅ CommRingCat.of (Polynomial ↑R) :=
  (mvPolynomialULiftFinOneAlgEquiv ↑R).toRingEquiv.toCommRingCatIso

/-- The forward map of `mvPolynomialULiftFinOneIso R` evaluates as the equivalence
`mvPolynomialULiftFinOneAlgEquiv R`. -/
@[simp]
theorem mvPolynomialULiftFinOneIso_hom_apply (R : CommRingCat.{u})
    (p : MvPolynomial (ULift.{u} (Fin 1)) ↑R) :
    (mvPolynomialULiftFinOneIso R).hom p = mvPolynomialULiftFinOneAlgEquiv ↑R p :=
  rfl

/-- **The affine line over an affine base is the spectrum of a univariate polynomial ring.**
Mathlib identifies `𝔸(n; Spec R)` with `Spec (MvPolynomial n R)`; composing with the
identification of `MvPolynomial (ULift (Fin 1)) R` with `R[T]` gives the affine line over
`Spec R` as `Spec R[T]`. -/
def affineLineSpecIsoSpecPolynomial (R : CommRingCat.{u}) :
    𝔸(ULift.{u} (Fin 1); Spec R) ≅ Spec (CommRingCat.of (Polynomial ↑R)) :=
  AffineSpace.SpecIso (ULift.{u} (Fin 1)) R ≪≫
    Scheme.Spec.mapIso (mvPolynomialULiftFinOneIso R).symm.op

/-- **The identification of the affine line with `Spec R[T]` is one of schemes over `Spec R`.**
It carries the structure morphism of the affine line to the morphism of spectra induced by the
inclusion `Polynomial.C` of the coefficients. -/
theorem affineLineSpecIsoSpecPolynomial_inv_over (R : CommRingCat.{u}) :
    (affineLineSpecIsoSpecPolynomial R).inv ≫ (𝔸(ULift.{u} (Fin 1); Spec R) ↘ Spec R) =
      Spec.map (CommRingCat.ofHom (Polynomial.C : ↑R →+* Polynomial ↑R)) := by
  rw [affineLineSpecIsoSpecPolynomial, Iso.trans_inv, Category.assoc,
    AffineSpace.SpecIso_inv_over]
  have h : (Scheme.Spec.mapIso (mvPolynomialULiftFinOneIso R).symm.op).inv =
      Spec.map (mvPolynomialULiftFinOneIso R).hom := rfl
  rw [h, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext fun r => mvPolynomialULiftFinOneAlgEquiv_C (↑R) r)

end Stacks.Chow

end
