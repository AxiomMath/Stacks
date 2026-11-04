module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# Clearing denominators in a multivariate polynomial over a fraction field

Part of Step C of the proof of Stacks Tag 0559. Let `A` be a domain with fraction field `K`.
Every `p : K[xᵢ]` becomes a polynomial with coefficients in `A` after multiplication by a
nonzero element of `A`, because `K[xᵢ]` is the localization of `A[xᵢ]` at the image of the
nonzero elements of `A` (`MvPolynomial.isLocalization`). Multiplying by a nonzero constant does
not change irreducibility over a field, so the resulting `P : A[xᵢ]` is irreducible over any
field extension of `K` as soon as `p` is.

This is the second half of the source's "clearing denominators": the first half, from the
fraction field of the polynomial ring in the transcendence basis down to that polynomial ring,
is `IsFractionRing.exists_isPrimitive_irreducible_aeval_eq_zero_iff_dvd`.

## Main results

* `MvPolynomial.exists_map_eq_C_mul`: the cleared model `P` and the multiplier.
* `MvPolynomial.exists_irreducible_map_of_irreducible_map`: the cleared model together with its
  irreducibility over a field extension of `K`, which is the hypothesis `hP` of
  `AlgebraicGeometry.exists_away_geometricallyIrreducible_mvPolynomialQuotient`.

## Implementation notes

The multiplier is recorded as `C (algebraMap A K a)` for a nonzero `a : A`, rather than as a
`Submonoid` element or as a scalar action, because that is the form in which the two uses
consume it: `a` is the element of `A` whose principal open the base is shrunk to, and
`C (algebraMap A K a)` is the unit of `K̄[xᵢ]` witnessing that `P` and `p` are associated there.

`MvPolynomial.algebraMvPolynomial` is made a local instance, as in
`Mathlib.RingTheory.MvPolynomial.Localization` itself: it is the algebra structure the
localization instance is stated for, and it is deliberately not global.

No Stacks tag is attached: Step C is not itself a tag of the source.

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559), Step C of the first
  proof
-/

@[expose] public section

open scoped nonZeroDivisors

namespace MvPolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]

/-- **Clearing denominators.** Over a domain `A` with fraction field `K`, every multivariate
polynomial over `K` becomes one over `A` after multiplication by a nonzero constant from `A`. -/
theorem exists_map_eq_C_mul (ι : Type*) (p : MvPolynomial ι K) :
    ∃ (P : MvPolynomial ι A) (a : A), a ≠ 0 ∧
      P.map (algebraMap A K) = C (algebraMap A K a) * p := by
  obtain ⟨b, hb⟩ := IsLocalization.exists_integer_multiple
    (A⁰.map (C (σ := ι))) (S := MvPolynomial ι K) p
  obtain ⟨a, ha, hab⟩ := b.property
  obtain ⟨P, hP⟩ := hb
  refine ⟨P, a, mem_nonZeroDivisors_iff_ne_zero.mp ha, ?_⟩
  calc (map (algebraMap A K)) P
      = algebraMap (MvPolynomial ι A) (MvPolynomial ι K) P := rfl
    _ = (b : MvPolynomial ι A) • p := hP
    _ = C (algebraMap A K a) * p := by
      rw [Algebra.smul_def, ← hab]
      simp

/-- **Clearing denominators, with absolute irreducibility.** Over a domain `A` with fraction
field `K` and a field extension `K̄` of `K`, a polynomial over `K` whose image in `K̄[xᵢ]` is
irreducible has a model over `A` whose image in `K̄[xᵢ]` is irreducible. -/
theorem exists_irreducible_map_of_irreducible_map {Kbar : Type*} [Field Kbar] [Algebra K Kbar]
    (ι : Type*) (p : MvPolynomial ι K) (hp : Irreducible (p.map (algebraMap K Kbar))) :
    ∃ (P : MvPolynomial ι A) (a : A), a ≠ 0 ∧
      P.map (algebraMap A K) = C (algebraMap A K a) * p ∧
      Irreducible (P.map ((algebraMap K Kbar).comp (algebraMap A K))) := by
  obtain ⟨P, a, ha, hPa⟩ := exists_map_eq_C_mul (A := A) (K := K) ι p
  refine ⟨P, a, ha, hPa, ?_⟩
  have hmap : P.map ((algebraMap K Kbar).comp (algebraMap A K)) =
      C ((algebraMap K Kbar) (algebraMap A K a)) * p.map (algebraMap K Kbar) := by
    rw [← MvPolynomial.map_map, hPa, _root_.map_mul, MvPolynomial.map_C]
  have hne : (algebraMap K Kbar) (algebraMap A K a) ≠ 0 :=
    (map_ne_zero _).mpr (by simpa [IsFractionRing.to_map_eq_zero_iff] using ha)
  have hunit : IsUnit (C ((algebraMap K Kbar) (algebraMap A K a)) : MvPolynomial ι Kbar) :=
    (isUnit_iff_ne_zero.mpr hne).map (C : Kbar →+* MvPolynomial ι Kbar)
  rw [hmap]
  exact (associated_unit_mul_left _ _ hunit).symm.irreducible hp

end MvPolynomial

end
