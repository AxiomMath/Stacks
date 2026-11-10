module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import StacksFrontier.RingTheory.Branches.MinimalPrimes
public import StacksFrontier.RingTheory.MinimalPrimes.Reduced
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The two ambient algebras of the normalization stalk

[Stacks, Tag 0C3B] describes the stalk of the pushforward of the structure sheaf of the
normalization in two ways: as the integral closure of the local ring in the total ring of
fractions of its reduction, and as the integral closure in the product of the residue fields
of its minimal primes.  This module identifies those two ambient algebras, so that either
description follows from the other.

For a ring `A` with finitely many minimal primes, write `R = A ⧸ nilradical A`.  Then `R` is
reduced with the same minimal primes as `A`, and its total ring of fractions is the product of
the localizations at those minimal primes.  Each such localization is a field, hence equal to
its own residue field, which is the residue field of the corresponding minimal prime of `A`.

## Main results

* `minimalPrimeResidueFieldProductAlgEquivFractionRingReduction`: the product of the residue
  fields of the minimal primes is the total ring of fractions of the reduction, as an
  `A`-algebra.
* `integralClosureReductionFractionRingAlgEquivMinimalPrimeResidueFields`: consequently the two
  integral closures appearing in [Stacks, Tag 0C3B] agree.

## Implementation notes

The `A`-algebra structures are the ones given by `reductionFractionRingHom` and
`minimalPrimeResidueFieldProductHom`, rather than by whatever instances typeclass synthesis
finds; the equivalences are therefore assembled as ring equivalences and packaged with an
explicit `commutes` proof.  Minimal primes of the reduction are indexed by the minimal primes
of `A` itself, through `minimalPrimeMapNilradical`, so no reindexing of the products is needed.

## References

* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
-/

@[expose] public noncomputable section

universe u

namespace Stacks.NormalizationStalkAmbient

/-- The canonical map from a ring to the total ring of fractions of its reduction. -/
public noncomputable def reductionFractionRingHom (A : Type*) [CommRing A] :
    A →+* FractionRing (A ⧸ nilradical A) :=
  (algebraMap (A ⧸ nilradical A) (FractionRing (A ⧸ nilradical A))).comp
    (Ideal.Quotient.mk (nilradical A))

/-- The product of the residue fields of the minimal primes of a commutative ring. -/
public abbrev minimalPrimeResidueFieldProduct (A : Type*) [CommRing A] :=
  ∀ p : minimalPrimes A, @Ideal.ResidueField A _ p.1 p.2.1.1

/-- The canonical map from a ring to the product of the residue fields of its minimal
primes. -/
public noncomputable def minimalPrimeResidueFieldProductHom (A : Type*) [CommRing A] :
    A →+* minimalPrimeResidueFieldProduct A :=
  RingHom.pi fun p : minimalPrimes A ↦
    letI : p.1.IsPrime := p.2.1.1
    algebraMap A p.1.ResidueField

section Reduction

variable (A : Type u) [CommRing A]

/-- The reduction of a commutative ring is reduced. -/
@[ega "0 1.1.1"]
public theorem isReduced_quotient_nilradical : IsReduced (A ⧸ nilradical A) :=
  (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)

/-- The image of a minimal prime in the reduction. -/
public def minimalPrimeMapNilradical (p : minimalPrimes A) : Ideal (A ⧸ nilradical A) :=
  (p : Ideal A).map (Ideal.Quotient.mk (nilradical A))

/-- A minimal prime is recovered from its image in the reduction. -/
public theorem comap_minimalPrimeMapNilradical (p : minimalPrimes A) :
    (minimalPrimeMapNilradical A p).comap (Ideal.Quotient.mk (nilradical A)) =
      (p : Ideal A) := by
  rw [minimalPrimeMapNilradical,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  exact sup_eq_left.mpr (nilradical_le_prime (H := p.2.1.1) (p : Ideal A))

/-- The minimal primes of a ring are the contractions of the minimal primes of its
reduction. -/
public theorem minimalPrimes_eq_comap_quotient_nilradical :
    minimalPrimes A =
      Ideal.comap (Ideal.Quotient.mk (nilradical A)) '' minimalPrimes (A ⧸ nilradical A) := by
  rw [← Ideal.minimalPrimes_eq_comap]
  simp [nilradical, Ideal.radical_minimalPrimes, minimalPrimes]

/-- The image in the reduction of a minimal prime is a minimal prime. -/
public theorem minimalPrimeMapNilradical_mem (p : minimalPrimes A) :
    minimalPrimeMapNilradical A p ∈ minimalPrimes (A ⧸ nilradical A) := by
  obtain ⟨q, hq, hqp⟩ :=
    (minimalPrimes_eq_comap_quotient_nilradical A).le p.2
  have : minimalPrimeMapNilradical A p = q := by
    rw [minimalPrimeMapNilradical, ← hqp,
      Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  rwa [this]

/-- Passing to the reduction is injective on minimal primes. -/
public theorem minimalPrimeMapNilradical_injective :
    Function.Injective (minimalPrimeMapNilradical A) := fun p p' h ↦ by
  apply Subtype.ext
  rw [← comap_minimalPrimeMapNilradical A p, ← comap_minimalPrimeMapNilradical A p', h]

/-- Every minimal prime of the reduction comes from a minimal prime. -/
public theorem minimalPrimeMapNilradical_surjective
    (q : Ideal (A ⧸ nilradical A)) (hq : q ∈ minimalPrimes (A ⧸ nilradical A)) :
    ∃ p : minimalPrimes A, minimalPrimeMapNilradical A p = q := by
  refine ⟨⟨q.comap (Ideal.Quotient.mk (nilradical A)),
    (minimalPrimes_eq_comap_quotient_nilradical A).ge ⟨q, hq, rfl⟩⟩, ?_⟩
  exact Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective q

end Reduction

section Ambient

variable (A : Type u) [CommRing A]

/-- The localization of the reduction at the image of a minimal prime is a field, so its
residue map is bijective. -/
public theorem bijective_residue_localizationNilradical (p : minimalPrimes A) :
    letI : (minimalPrimeMapNilradical A p).IsPrime := (minimalPrimeMapNilradical_mem A p).1.1
    Function.Bijective
      (IsLocalRing.residue (Localization.AtPrime (minimalPrimeMapNilradical A p))) := by
  let : (minimalPrimeMapNilradical A p).IsPrime := (minimalPrimeMapNilradical_mem A p).1.1
  let : IsReduced (A ⧸ nilradical A) := isReduced_quotient_nilradical A
  let : Field (Localization.AtPrime (minimalPrimeMapNilradical A p)) :=
    (isField_localizationAtPrime_of_minimal (A ⧸ nilradical A) _
      (minimalPrimeMapNilradical_mem A p)).toField
  refine ⟨?_, IsLocalRing.residue_surjective⟩
  rw [RingHom.injective_iff_ker_eq_bot]
  change RingHom.ker (Ideal.Quotient.mk _) = ⊥
  rw [Ideal.mk_ker]
  exact IsLocalRing.maximalIdeal_eq_bot

/-- The residue map of the localization of the reduction at the image of a minimal prime, as a
ring equivalence. -/
public noncomputable def residueRingEquivNilradical (p : minimalPrimes A) :
    letI : (minimalPrimeMapNilradical A p).IsPrime := (minimalPrimeMapNilradical_mem A p).1.1
    Localization.AtPrime (minimalPrimeMapNilradical A p) ≃+*
      (minimalPrimeMapNilradical A p).ResidueField :=
  letI : (minimalPrimeMapNilradical A p).IsPrime := (minimalPrimeMapNilradical_mem A p).1.1
  RingEquiv.ofBijective (IsLocalRing.residue _) (bijective_residue_localizationNilradical A p)

/-- The residue field of a minimal prime agrees with the residue field of its image in the
reduction. -/
public noncomputable def residueFieldRingEquivNilradical (p : minimalPrimes A) :
    letI : (minimalPrimeMapNilradical A p).IsPrime := (minimalPrimeMapNilradical_mem A p).1.1
    (@Ideal.ResidueField A _ p.1 p.2.1.1) ≃+*
      (minimalPrimeMapNilradical A p).ResidueField :=
  letI : (p : Ideal A).IsPrime := p.2.1.1
  letI : (minimalPrimeMapNilradical A p).IsPrime := (minimalPrimeMapNilradical_mem A p).1.1
  RingEquiv.ofBijective
    (Ideal.ResidueField.map (p : Ideal A) (minimalPrimeMapNilradical A p)
      (Ideal.Quotient.mk (nilradical A)) (comap_minimalPrimeMapNilradical A p).symm)
    ((RingHom.surjectiveOnStalks_of_surjective
      Ideal.Quotient.mk_surjective).residueFieldMap_bijective _ _ _)

/-- The localization of the reduction at the image of a minimal prime is the residue field of
that minimal prime. -/
public noncomputable def localizationNilradicalRingEquivResidueField (p : minimalPrimes A) :
    letI : (minimalPrimeMapNilradical A p).IsPrime := (minimalPrimeMapNilradical_mem A p).1.1
    Localization.AtPrime (minimalPrimeMapNilradical A p) ≃+*
      @Ideal.ResidueField A _ p.1 p.2.1.1 :=
  letI : (minimalPrimeMapNilradical A p).IsPrime := (minimalPrimeMapNilradical_mem A p).1.1
  (residueRingEquivNilradical A p).trans (residueFieldRingEquivNilradical A p).symm

/-- That identification carries the image of an element of the ring to its image in the
residue field. -/
public theorem localizationNilradicalRingEquivResidueField_algebraMap (p : minimalPrimes A)
    (a : A) :
    letI : (minimalPrimeMapNilradical A p).IsPrime := (minimalPrimeMapNilradical_mem A p).1.1
    localizationNilradicalRingEquivResidueField A p
        (algebraMap (A ⧸ nilradical A) (Localization.AtPrime (minimalPrimeMapNilradical A p))
          (Ideal.Quotient.mk (nilradical A) a)) =
      @algebraMap A (@Ideal.ResidueField A _ p.1 p.2.1.1) _ _ _ a := by
  let : (p : Ideal A).IsPrime := p.2.1.1
  let : (minimalPrimeMapNilradical A p).IsPrime := (minimalPrimeMapNilradical_mem A p).1.1
  change (residueFieldRingEquivNilradical A p).symm (residueRingEquivNilradical A p _) = _
  rw [RingEquiv.symm_apply_eq]
  change IsLocalRing.residue (Localization.AtPrime (minimalPrimeMapNilradical A p))
        (algebraMap (A ⧸ nilradical A) (Localization.AtPrime (minimalPrimeMapNilradical A p))
          (Ideal.Quotient.mk (nilradical A) a)) =
      Ideal.ResidueField.map (p : Ideal A) (minimalPrimeMapNilradical A p)
        (Ideal.Quotient.mk (nilradical A)) (comap_minimalPrimeMapNilradical A p).symm
        (algebraMap A (p : Ideal A).ResidueField a)
  rw [Ideal.ResidueField.map_algebraMap,
    ← IsLocalRing.ResidueField.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply (A ⧸ nilradical A)
      (Localization.AtPrime (minimalPrimeMapNilradical A p))
      (minimalPrimeMapNilradical A p).ResidueField]

/-- For a ring with finitely many minimal primes, the total ring of fractions of its reduction
is the product of the localizations of the reduction at the images of those minimal primes. -/
public theorem isLocalization_pi_localizationNilradical (hA : (minimalPrimes A).Finite) :
    @IsLocalization (A ⧸ nilradical A) _ (nonZeroDivisors (A ⧸ nilradical A))
      (∀ p : minimalPrimes A,
        @Localization.AtPrime (A ⧸ nilradical A) _ (minimalPrimeMapNilradical A p)
          (minimalPrimeMapNilradical_mem A p).1.1) _ _ :=
  let : Finite (minimalPrimes A) := hA
  @isLocalization_pi_localization_atPrime (A ⧸ nilradical A) _
    (isReduced_quotient_nilradical A) (minimalPrimes A) hA (minimalPrimeMapNilradical A)
    (fun p ↦ (minimalPrimeMapNilradical_mem A p).1.1)
    (fun p ↦ minimalPrimeMapNilradical_mem A p)
    (minimalPrimeMapNilradical_injective A)
    (fun q hq ↦ by
      obtain ⟨p, hp⟩ := minimalPrimeMapNilradical_surjective A q hq
      exact ⟨p, hp⟩)

/-- For a ring with finitely many minimal primes, the total ring of fractions of its reduction
is the product of the residue fields of those minimal primes. -/
public noncomputable def fractionRingReductionRingEquivMinimalPrimeResidueFields
    (hA : (minimalPrimes A).Finite) :
    FractionRing (A ⧸ nilradical A) ≃+* minimalPrimeResidueFieldProduct A :=
  letI : Finite (minimalPrimes A) := hA
  letI := isLocalization_pi_localizationNilradical A hA
  (IsLocalization.algEquiv (nonZeroDivisors (A ⧸ nilradical A))
      (FractionRing (A ⧸ nilradical A))
      (∀ p : minimalPrimes A,
        @Localization.AtPrime (A ⧸ nilradical A) _ (minimalPrimeMapNilradical A p)
          (minimalPrimeMapNilradical_mem A p).1.1)).toRingEquiv.trans
    (RingEquiv.piCongrRight (localizationNilradicalRingEquivResidueField A))

/-- **For a reduced ring, the total ring of fractions of its reduction is, as an algebra over the
ring, its own total ring of fractions.**  The nilradical is trivial, so the reduction is the ring
itself, and a ring isomorphism carries one total ring of fractions to the other. -/
public noncomputable def fractionRingReductionAlgEquiv (hred : IsReduced A) :
    letI : Algebra A (FractionRing (A ⧸ nilradical A)) :=
      (reductionFractionRingHom A).toAlgebra
    FractionRing (A ⧸ nilradical A) ≃ₐ[A] FractionRing A := by
  letI : Algebra A (FractionRing (A ⧸ nilradical A)) :=
    (reductionFractionRingHom A).toAlgebra
  have h0 : nilradical A = ⊥ := nilradical_eq_bot_iff.mpr hred
  let b : (A ⧸ nilradical A) ≃+* A :=
    (Ideal.quotEquivOfEq h0).trans (RingEquiv.quotientBot A)
  let e : FractionRing (A ⧸ nilradical A) ≃+* FractionRing A :=
    IsFractionRing.ringEquivOfRingEquiv b
  refine AlgEquiv.ofRingEquiv (f := e) ?_
  intro a
  change e (algebraMap (A ⧸ nilradical A) (FractionRing (A ⧸ nilradical A))
    (Ideal.Quotient.mk (nilradical A) a)) = algebraMap A (FractionRing A) a
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  simp [b]

/-- **Stacks Project, Tag 0C3B.** The two ambient algebras of the normalization stalk agree:
the total ring of fractions of the reduction is the product of the residue fields of the
minimal primes, as an algebra over the ring. -/
public noncomputable def fractionRingReductionAlgEquivMinimalPrimeResidueFields
    (hA : (minimalPrimes A).Finite) :
    letI : Algebra A (FractionRing (A ⧸ nilradical A)) := (reductionFractionRingHom A).toAlgebra
    letI : Algebra A (minimalPrimeResidueFieldProduct A) :=
      (minimalPrimeResidueFieldProductHom A).toAlgebra
    FractionRing (A ⧸ nilradical A) ≃ₐ[A] minimalPrimeResidueFieldProduct A :=
  letI : Algebra A (FractionRing (A ⧸ nilradical A)) := (reductionFractionRingHom A).toAlgebra
  letI : Algebra A (minimalPrimeResidueFieldProduct A) :=
    (minimalPrimeResidueFieldProductHom A).toAlgebra
  letI : Finite (minimalPrimes A) := hA
  letI := isLocalization_pi_localizationNilradical A hA
  AlgEquiv.ofRingEquiv
    (f := fractionRingReductionRingEquivMinimalPrimeResidueFields A hA)
    (fun a ↦ by
      change (RingEquiv.piCongrRight (localizationNilradicalRingEquivResidueField A))
          (IsLocalization.algEquiv (nonZeroDivisors (A ⧸ nilradical A))
            (FractionRing (A ⧸ nilradical A)) _
            ((algebraMap (A ⧸ nilradical A) (FractionRing (A ⧸ nilradical A)))
              (Ideal.Quotient.mk (nilradical A) a))) = _
      rw [AlgEquiv.commutes]
      funext p
      exact localizationNilradicalRingEquivResidueField_algebraMap A p a)

/-- **Stacks Project, Tag 0C3B.** The integral closure of a ring in the total ring of fractions
of its reduction agrees with its integral closure in the product of the residue fields of its
minimal primes. -/
public noncomputable def integralClosureReductionAlgEquivMinimalPrimeResidueFields
    (hA : (minimalPrimes A).Finite) :
    letI : Algebra A (FractionRing (A ⧸ nilradical A)) := (reductionFractionRingHom A).toAlgebra
    letI : Algebra A (minimalPrimeResidueFieldProduct A) :=
      (minimalPrimeResidueFieldProductHom A).toAlgebra
    integralClosure A (FractionRing (A ⧸ nilradical A)) ≃ₐ[A]
      integralClosure A (minimalPrimeResidueFieldProduct A) :=
  letI : Algebra A (FractionRing (A ⧸ nilradical A)) := (reductionFractionRingHom A).toAlgebra
  letI : Algebra A (minimalPrimeResidueFieldProduct A) :=
    (minimalPrimeResidueFieldProductHom A).toAlgebra
  let e := fractionRingReductionAlgEquivMinimalPrimeResidueFields A hA
  ((integralClosure A (FractionRing (A ⧸ nilradical A))).equivMapOfInjective
      e.toAlgHom e.injective).trans
    (Subalgebra.equivOfEq _ _ (integralClosure_map_algEquiv e))

end Ambient

end Stacks.NormalizationStalkAmbient

end
