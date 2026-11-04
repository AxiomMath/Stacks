module

public import Mathlib.RingTheory.SurjectiveOnStalks
public import StacksFrontier.AlgebraicGeometry.MinimalPrimeResidueLocalization.Restrict

/-!
# The minimal-prime residue fields of a localization

Let `A` be a commutative ring, `M ⊆ A` a submonoid and `Aₘ` a localization of `A` at `M`.  The
product of the residue fields of the minimal primes of `Aₘ` is the product of the residue fields
of the minimal primes of `A` disjoint from `M`: the index sets correspond by
`minimalPrimesEquivDisjoint`, and the residue field of a prime of `Aₘ` is the residue field of
its contraction, because a localization map is surjective on stalks.

## Main definitions

* `Stacks.MinimalPrimeResidueLocalization.residueFieldProductRingEquivDisjoint`: the product of
  the minimal-prime residue fields of a localization is the product of the residue fields of the
  minimal primes of the base ring disjoint from the localized submonoid.

## Main results

* `Stacks.MinimalPrimeResidueLocalization.bijective_residueField_map_under`: the residue field of
  the contraction of a minimal prime of `Aₘ` maps bijectively to the residue field of that prime.
* `Stacks.MinimalPrimeResidueLocalization.residueFieldProductRingEquivDisjoint_algebraMap`: that
  identification is compatible with the two maps from the base ring.

## References

* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
-/

@[expose] public noncomputable section

open Stacks.NormalizationStalkAmbient

universe u

namespace Stacks.MinimalPrimeResidueLocalization

variable (A : Type u) [CommRing A] (M : Submonoid A)
variable (Aₘ : Type u) [CommRing Aₘ] [Algebra A Aₘ] [IsLocalization M Aₘ]

/-- The comparison map from the residue field of the contraction of a minimal prime of a
localization to the residue field of that minimal prime is bijective. -/
public theorem bijective_residueField_map_under (q : minimalPrimes Aₘ) :
    Function.Bijective
      (@Ideal.ResidueField.map A Aₘ _ _ ((q : Ideal Aₘ).under A)
        (under_mem_minimalPrimes A M Aₘ q.2).1.1 (q : Ideal Aₘ) q.2.1.1
        (algebraMap A Aₘ) rfl) :=
  @RingHom.SurjectiveOnStalks.residueFieldMap_bijective A Aₘ _ _ (algebraMap A Aₘ)
    (RingHom.surjectiveOnStalks_of_isLocalization M Aₘ) ((q : Ideal Aₘ).under A)
    (under_mem_minimalPrimes A M Aₘ q.2).1.1 (q : Ideal Aₘ) q.2.1.1 rfl

/-- The product of the residue fields of the minimal primes of a localization is the product of
the residue fields of the minimal primes of the base ring disjoint from the localized
submonoid. -/
public noncomputable def residueFieldProductRingEquivDisjoint :
    minimalPrimeResidueFieldProduct Aₘ ≃+* disjointResidueFieldProduct A M :=
  (RingEquiv.piCongrRight fun q : minimalPrimes Aₘ ↦
      (RingEquiv.ofBijective _ (bijective_residueField_map_under A M Aₘ q)).symm).trans
    (RingEquiv.piCongrLeft
      (fun p : {p : minimalPrimes A // Disjoint (M : Set A) ((p : Ideal A) : Set A)} ↦
        @Ideal.ResidueField A _ p.1.1 p.1.2.1.1)
      (minimalPrimesEquivDisjoint A M Aₘ))

/-- The identification of the two products of residue fields is compatible with the maps from
the base ring. -/
public theorem residueFieldProductRingEquivDisjoint_algebraMap (a : A) :
    residueFieldProductRingEquivDisjoint A M Aₘ
        (minimalPrimeResidueFieldProductHom Aₘ (algebraMap A Aₘ a))
      = restrictResidueFieldProduct A M (minimalPrimeResidueFieldProductHom A a) := by
  funext p
  obtain ⟨q, rfl⟩ := (minimalPrimesEquivDisjoint A M Aₘ).surjective p
  refine (Equiv.piCongrLeft_apply_apply
    (fun p : {p : minimalPrimes A // Disjoint (M : Set A) ((p : Ideal A) : Set A)} ↦
      @Ideal.ResidueField A _ p.1.1 p.1.2.1.1)
    (minimalPrimesEquivDisjoint A M Aₘ) _ q).trans ?_
  refine (RingEquiv.symm_apply_eq (RingEquiv.ofBijective _
    (bijective_residueField_map_under A M Aₘ q))).mpr ?_
  exact (@Ideal.ResidueField.map_algebraMap A Aₘ _ _ (Ideal.under A (q : Ideal Aₘ))
    (under_mem_minimalPrimes A M Aₘ q.2).1.1 (q : Ideal Aₘ) q.2.1.1
    (algebraMap A Aₘ) rfl a).symm

end Stacks.MinimalPrimeResidueLocalization

end
