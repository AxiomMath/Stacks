module

public import StacksFrontier.AlgebraicGeometry.MinimalPrimeResidueLocalization.Reindex

/-!
# The minimal-prime residue field product of a localization is a localization

Let `A` be a commutative ring with finitely many minimal primes, let `M ⊆ A` be a submonoid and
let `Aₘ` be a localization of `A` at `M`.  The product of the residue fields of the minimal
primes of `Aₘ` is the localization, at the image of `M`, of the product of the residue fields of
the minimal primes of `A`.

## Main definitions

* `Stacks.MinimalPrimeResidueLocalization.residueFieldProductAlgebra`: the canonical algebra
  structure of the product for `A` on the product for `Aₘ`, namely restriction to the minimal
  primes disjoint from `M` followed by `residueFieldProductRingEquivDisjoint`.

## Main results

* `Stacks.MinimalPrimeResidueLocalization.isLocalization_minimalPrimeResidueFieldProduct`: that
  algebra structure presents the product for `Aₘ` as a localization of the product for `A`.
* `Stacks.MinimalPrimeResidueLocalization.residueFieldProductAlgebra_algebraMap`: it is
  compatible with the maps from `A`.

## References

* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
-/

@[expose] public noncomputable section

open Stacks.NormalizationStalkAmbient

universe u

namespace Stacks.MinimalPrimeResidueLocalization

variable (A : Type u) [CommRing A] (M : Submonoid A)
variable (Aₘ : Type u) [CommRing Aₘ] [Algebra A Aₘ] [IsLocalization M Aₘ]

/-- The product of the minimal-prime residue fields of a localization, as an algebra over the
product of the minimal-prime residue fields of the base ring. -/
@[instance_reducible]
public noncomputable def residueFieldProductAlgebra :
    Algebra (minimalPrimeResidueFieldProduct A) (minimalPrimeResidueFieldProduct Aₘ) :=
  ((residueFieldProductRingEquivDisjoint A M Aₘ).symm.toRingHom.comp
    (restrictResidueFieldProduct A M)).toAlgebra

/-- That algebra structure is compatible with the maps from the base ring. -/
public theorem residueFieldProductAlgebra_algebraMap (a : A) :
    (residueFieldProductRingEquivDisjoint A M Aₘ).symm
        (restrictResidueFieldProduct A M (minimalPrimeResidueFieldProductHom A a))
      = minimalPrimeResidueFieldProductHom Aₘ (algebraMap A Aₘ a) := by
  rw [← residueFieldProductRingEquivDisjoint_algebraMap A M Aₘ a, RingEquiv.symm_apply_apply]

/-- For a ring with finitely many minimal primes, the product of the residue fields of the minimal
primes of a localization is the localization, at the image of the inverted submonoid, of the
product of the residue fields of the minimal primes of the ring. -/
public theorem isLocalization_minimalPrimeResidueFieldProduct (hA : (minimalPrimes A).Finite) :
    letI : Algebra A (minimalPrimeResidueFieldProduct A) :=
      (minimalPrimeResidueFieldProductHom A).toAlgebra
    letI := residueFieldProductAlgebra A M Aₘ
    IsLocalization (Algebra.algebraMapSubmonoid (minimalPrimeResidueFieldProduct A) M)
      (minimalPrimeResidueFieldProduct Aₘ) := by
  let : Algebra A (minimalPrimeResidueFieldProduct A) :=
    (minimalPrimeResidueFieldProductHom A).toAlgebra
  let : Algebra (minimalPrimeResidueFieldProduct A) (disjointResidueFieldProduct A M) :=
    (restrictResidueFieldProduct A M).toAlgebra
  let : Algebra (minimalPrimeResidueFieldProduct A) (minimalPrimeResidueFieldProduct Aₘ) :=
    residueFieldProductAlgebra A M Aₘ
  have : IsLocalization (Algebra.algebraMapSubmonoid (minimalPrimeResidueFieldProduct A) M)
      (disjointResidueFieldProduct A M) := isLocalization_disjointResidueFieldProduct A M hA
  exact IsLocalization.isLocalization_of_algEquiv _
    (AlgEquiv.ofRingEquiv (f := (residueFieldProductRingEquivDisjoint A M Aₘ).symm) fun _ ↦ rfl)

end Stacks.MinimalPrimeResidueLocalization

end
