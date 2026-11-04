module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.TotalFractionRing

/-!
# Finitely many minimal primes in the local ring of a scheme

Let `X` be a scheme every quasi-compact open of which has finitely many irreducible
components, and let `x` be a point of `X`.  Then the local ring `𝒪_{X,x}` has only finitely
many minimal primes.

## Main results

* `minimalPrimes_eq_preimage_under_of_isLocalization`: the minimal primes of a localization
  are the contraction-preimage of the minimal primes of the base ring.
* `finite_minimalPrimes_of_isLocalization`: a localization of a ring with finitely many
  minimal primes has finitely many minimal primes.
* `finite_minimalPrimes_stalk`: the local ring of such a scheme at a point has finitely many
  minimal primes.

## References

* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.StalkMinimalPrimes.Basic

section Localization

/-- The minimal primes of a localization are the preimage, under contraction, of the minimal
primes of the base ring. -/
public theorem minimalPrimes_eq_preimage_under_of_isLocalization {R : Type*} [CommRing R]
    (M : Submonoid R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S] :
    minimalPrimes S = Ideal.under R (B := S) ⁻¹' minimalPrimes R := by
  simpa only [Ideal.map_bot] using IsLocalization.minimalPrimes_map M S (⊥ : Ideal R)

/-- A localization of a ring with finitely many minimal primes has finitely many minimal
primes. -/
public theorem finite_minimalPrimes_of_isLocalization {R : Type*} [CommRing R]
    (M : Submonoid R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S]
    (hR : (minimalPrimes R).Finite) : (minimalPrimes S).Finite := by
  rw [minimalPrimes_eq_preimage_under_of_isLocalization M S]
  exact Set.Finite.preimage
    (Set.injOn_of_injective (IsLocalization.orderEmbedding M S).injective) hR

end Localization

/-- If every quasi-compact open of `X` has finitely many irreducible components, the local
ring of `X` at `x` has only finitely many minimal primes. -/
@[stacks 0C3B "finiteness of the minimal primes"]
public theorem finite_minimalPrimes_stalk (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) : (minimalPrimes (X.presheaf.stalk x)).Finite := by
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  exact @finite_minimalPrimes_of_isLocalization Γ(X, U) _
    (hU.primeIdealOf (⟨x, hxU⟩ : U)).asIdeal.primeCompl (X.presheaf.stalk x) _
    (X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U))
    (hU.isLocalization_stalk (⟨x, hxU⟩ : U))
    (AlgebraicGeometry.finite_minimalPrimes_of_affine_open hX U hU.isoSpec.symm)

end Stacks.StalkMinimalPrimes.Basic

end
