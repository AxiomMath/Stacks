module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.KrullDimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Affine ingredients for the normalization of a one-dimensional scheme

Let `X` be a scheme and let `U` be an open of `X` presented by a ring `A`, i.e. equipped with
an isomorphism `Spec A ≅ U`. The normalization of `X` restricted over `U` is the spectrum of
the integral closure of `A` in the product of the residue fields at the generic points of the
irreducible components of `U`, and those residue fields are the fraction fields of the
minimal-prime quotients `A ⧸ p`. This file collects the local inputs of that description which
are statements about `A` alone.

## Main results

* `AlgebraicGeometry.IsLocallyNoetherian.isNoetherianRing_of_specIso`: a ring presenting an
  open of a locally Noetherian scheme is Noetherian.
* `AlgebraicGeometry.isNoetherianRing_quotient_minimalPrime_of_affine_open`: each
  minimal-prime quotient of such a ring is Noetherian.
* `AlgebraicGeometry.ringKrullDim_quotient_le_topologicalKrullDim`: every quotient of a ring
  presenting an open of `X` has Krull dimension at most the Krull dimension of `X`.
* `AlgebraicGeometry.ringKrullDim_quotient_minimalPrime_le_one` specializes this to a
  one-dimensional scheme.
* `integralClosure_fractionRing_eq_bot_of_ringKrullDim_eq_zero`: a domain of Krull dimension
  zero is integrally closed in its fraction field.

## Implementation notes

An open presented by a ring is given here by an isomorphism `Spec A ≅ U` rather than by an
`IsAffineOpen` hypothesis together with `Γ(X, U)`. This is the form in which the local
description of a normalization is used, and it is strictly more flexible: it does not commit
to the presentation `Γ(X, U)`, so a ring already in hand can be used directly.

The scheme-level statements fix `A : Type u` for `X : Scheme.{u}`. This is forced, not chosen:
`Spec (.of A)` has to be a `Scheme.{u}` for the presenting isomorphism to typecheck.

The algebraic step that splits an integral closure over a finite product of algebras is not
restated here: it is already `isIntegral_pi_iff_of_finite` in
`StacksFrontier.RingTheory.Branches.MinimalPrimes`.

`AlgebraicGeometry.ringKrullDim_quotient_le_topologicalKrullDim` is stated for an arbitrary
ideal and with no Noetherian hypothesis, since neither is used: the bound is the composite of
three topological facts (a quotient map of rings induces a closed embedding of spectra, `U` is
homeomorphic to `Spec A`, and `U` embeds in `X`), and Krull dimension of a topological space
is monotone along inducing maps. The minimal-prime form keeps the hypotheses in which it is
applied.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/-- A domain of Krull dimension zero is a field, hence is integrally closed in its fraction
field: its integral closure there is the bottom subalgebra. -/
theorem integralClosure_fractionRing_eq_bot_of_ringKrullDim_eq_zero {R : Type*} [CommRing R]
    [IsDomain R] (hR : ringKrullDim R = 0) :
    integralClosure R (FractionRing R) = ⊥ := by
  have : Ring.KrullDimLE 0 R := Ring.krullDimLE_iff.mpr (by simp [hR])
  let _ := (Ring.KrullDimLE.isField_of_isDomain (R := R)).toField
  exact IsIntegrallyClosed.integralClosure_eq_bot (R := R) (FractionRing R)

namespace AlgebraicGeometry

/-- A ring presenting an open of a locally Noetherian scheme is Noetherian: the presenting
isomorphism is an open immersion, along which local Noetherianness descends to `Spec A`. -/
@[ega "I 6.1.3" "more general"]
theorem IsLocallyNoetherian.isNoetherianRing_of_specIso {X : Scheme.{u}} [IsLocallyNoetherian X]
    {A : Type u} [CommRing A] (U : X.Opens) (e : Spec (.of A) ≅ U.toScheme) :
    IsNoetherianRing A :=
  isLocallyNoetherian_Spec.mp (isLocallyNoetherian_of_isOpenImmersion e.hom)

/-- Every minimal-prime quotient of a ring presenting an open of a locally Noetherian scheme is
Noetherian. -/
theorem isNoetherianRing_quotient_minimalPrime_of_affine_open {X : Scheme.{u}}
    [IsLocallyNoetherian X] {A : Type u} [CommRing A] (U : X.Opens)
    (e : Spec (.of A) ≅ U.toScheme) (p : minimalPrimes A) :
    IsNoetherianRing (A ⧸ (p : Ideal A)) :=
  have : IsNoetherianRing A := IsLocallyNoetherian.isNoetherianRing_of_specIso U e
  inferInstance

/-- Every quotient of a ring presenting an open of a scheme `X` has Krull dimension at most the
Krull dimension of `X`. The spectrum of the quotient is a closed subspace of `Spec A`, which is
homeomorphic to `U`, which is a subspace of `X`; Krull dimension of a topological space is
monotone along inducing maps. -/
@[ega "0 14.1.4" "(i), special case", ega "IV 5.1.1" "partial"]
theorem ringKrullDim_quotient_le_topologicalKrullDim {X : Scheme.{u}} {A : Type u} [CommRing A]
    (U : X.Opens) (e : Spec (.of A) ≅ U.toScheme) (I : Ideal A) :
    ringKrullDim (A ⧸ I) ≤ topologicalKrullDim X := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  have hquot : topologicalKrullDim (PrimeSpectrum (A ⧸ I))
      ≤ topologicalKrullDim (PrimeSpectrum A) :=
    (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _
      Ideal.Quotient.mk_surjective).isInducing.topologicalKrullDim_le
  have hspec : topologicalKrullDim (PrimeSpectrum A) = topologicalKrullDim U.toScheme :=
    IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph
  have hopen : topologicalKrullDim U.toScheme ≤ topologicalKrullDim X :=
    Topology.IsEmbedding.subtypeVal.isInducing.topologicalKrullDim_le
  exact ((hspec ▸ hquot).trans hopen)

/-- The minimal-prime quotients of a ring presenting an open of a one-dimensional locally
Noetherian scheme have Krull dimension at most one. -/
theorem ringKrullDim_quotient_minimalPrime_le_one {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hX : topologicalKrullDim X = 1) {A : Type u} [CommRing A] (U : X.Opens)
    (e : Spec (.of A) ≅ U.toScheme) (p : minimalPrimes A) :
    ringKrullDim (A ⧸ (p : Ideal A)) ≤ 1 :=
  (ringKrullDim_quotient_le_topologicalKrullDim U e _).trans hX.le

end AlgebraicGeometry

end
