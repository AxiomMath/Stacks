module

public import Mathlib.Algebra.Group.Pi.Units
public import StacksFrontier.AlgebraicGeometry.MinimalPrimeResidueLocalization.Index
public import StacksFrontier.AlgebraicGeometry.NormalizationStalkAmbient.Reduction

/-!
# Localizing the product of the minimal-prime residue fields

Let `A` be a commutative ring with finitely many minimal primes and let `M ⊆ A` be a submonoid.
Inverting the image of `M` in the product of the residue fields of all minimal primes of `A`
deletes exactly the factors indexed by the minimal primes that `M` meets, leaving the product
over the minimal primes disjoint from `M`.

## Main definitions

* `Stacks.MinimalPrimeResidueLocalization.disjointResidueFieldProduct`: the product of the
  residue fields of the minimal primes disjoint from `M`.
* `Stacks.MinimalPrimeResidueLocalization.restrictResidueFieldProduct`: the restriction map from
  the product over all minimal primes.

## Main results

* `Stacks.MinimalPrimeResidueLocalization.isLocalization_disjointResidueFieldProduct`: that
  restriction map presents the restricted product as the localization of the full product at the
  image of `M`.

## References

* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
-/

@[expose] public noncomputable section

open Stacks.NormalizationStalkAmbient

universe u

namespace Stacks.MinimalPrimeResidueLocalization

variable (A : Type u) [CommRing A] (M : Submonoid A)

/-- The product of the residue fields of those minimal primes of `A` that are disjoint from the
submonoid `M`. -/
public abbrev disjointResidueFieldProduct :=
  ∀ p : {p : minimalPrimes A // Disjoint (M : Set A) ((p : Ideal A) : Set A)},
    @Ideal.ResidueField A _ p.1.1 p.1.2.1.1

/-- Restriction of the product of the residue fields of all minimal primes of `A` to the
product over those disjoint from `M`. -/
public noncomputable def restrictResidueFieldProduct :
    minimalPrimeResidueFieldProduct A →+* disjointResidueFieldProduct A M :=
  RingHom.pi fun p ↦ Pi.evalRingHom _ p.1

/-- The image of a ring element in the product of the minimal-prime residue fields has, at a
minimal prime, the image of that element in the residue field of the prime. -/
public theorem minimalPrimeResidueFieldProductHom_apply (a : A) (p : minimalPrimes A) :
    minimalPrimeResidueFieldProductHom A a p
      = algebraMap A (@Ideal.ResidueField A _ p.1 p.2.1.1) a :=
  rfl

/-- Inverting the image of a submonoid `M` in the product of the residue fields of all minimal
primes of `A` leaves the product over the minimal primes disjoint from `M`. -/
public theorem isLocalization_disjointResidueFieldProduct (hA : (minimalPrimes A).Finite) :
    letI : Algebra A (minimalPrimeResidueFieldProduct A) :=
      (minimalPrimeResidueFieldProductHom A).toAlgebra
    letI : Algebra (minimalPrimeResidueFieldProduct A) (disjointResidueFieldProduct A M) :=
      (restrictResidueFieldProduct A M).toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid (minimalPrimeResidueFieldProduct A) M)
      (disjointResidueFieldProduct A M) := by
  classical
  let : Algebra A (minimalPrimeResidueFieldProduct A) :=
    (minimalPrimeResidueFieldProductHom A).toAlgebra
  let : Algebra (minimalPrimeResidueFieldProduct A) (disjointResidueFieldProduct A M) :=
    (restrictResidueFieldProduct A M).toAlgebra
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨-, s, hs, rfl⟩
    refine Pi.isUnit_iff.mpr fun p ↦ ?_
    have : (p.1 : Ideal A).IsPrime := p.1.2.1.1
    have key : algebraMap (minimalPrimeResidueFieldProduct A) (disjointResidueFieldProduct A M)
        (algebraMap A (minimalPrimeResidueFieldProduct A) s) p
        = algebraMap A (p.1 : Ideal A).ResidueField s := rfl
    rw [key, isUnit_iff_ne_zero, ne_eq, Ideal.algebraMap_residueField_eq_zero]
    exact Set.disjoint_left.mp p.2 hs
  · intro y
    refine ⟨⟨fun p ↦ if h : Disjoint (M : Set A) ((p : Ideal A) : Set A) then y ⟨p, h⟩ else 0,
      1⟩, ?_⟩
    simp only [OneMemClass.coe_one, map_one, mul_one]
    funext p
    change y p = dite (Disjoint (M : Set A) ((p.1 : Ideal A) : Set A))
      (fun h ↦ y ⟨p.1, h⟩) (fun _ ↦ 0)
    rw [dite_eq_left p.2]
  · intro z₁ z₂ h
    obtain ⟨s, hsM, hsp⟩ := exists_mem_mem_of_not_disjoint A M hA
    refine ⟨⟨algebraMap A (minimalPrimeResidueFieldProduct A) s, ⟨s, hsM, rfl⟩⟩, ?_⟩
    funext p
    simp only [Pi.mul_apply]
    by_cases hd : Disjoint (M : Set A) ((p : Ideal A) : Set A)
    · rw [show z₁ p = z₂ p from congrFun h ⟨p, hd⟩]
    · have : (p : Ideal A).IsPrime := p.2.1.1
      have hz : algebraMap A (minimalPrimeResidueFieldProduct A) s p
          = algebraMap A (p : Ideal A).ResidueField s := rfl
      rw [hz, Ideal.algebraMap_residueField_eq_zero.mpr (hsp p hd), zero_mul, zero_mul]

end Stacks.MinimalPrimeResidueLocalization

end
