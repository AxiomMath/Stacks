module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineComparison

/-!
# Weakly associated points over an affine open

Let `F` be a quasi-coherent module on a scheme `X` and let `V` be an affine open of `X`. The
canonical morphism `Spec Γ(X, V) ⟶ X` is injective and carries the primes weakly associated to
the sections `Γ(F, V)` onto the weakly associated points of `F` that lie in `V`.

Consequently the two finiteness hypotheses that govern the flat locus of a finite type module —
local finiteness of the weakly associated points of the base scheme, and finiteness of the
weakly associated primes of the base ring — say the same thing, one on an affine chart and the
other in the ring of sections over it.

## Main results

* `AlgebraicGeometry.weaklyAssociatedPoints_inter_eq_image_fromSpec`: the identification of the
  weakly associated points lying in an affine open with the weakly associated primes of the
  sections there.
* `AlgebraicGeometry.weaklyAssociatedPrimes_sections_finite_iff`: the two finiteness conditions
  are equivalent.
* `AlgebraicGeometry.weaklyAssociatedPrimes_sections_finite`: the sections over an affine open
  contained in an open that meets the weakly associated points in a finite set have finitely many
  weakly associated primes.

## Implementation notes

The weakly associated primes of a module form a set of ideals, while the points of an affine
open are described by a set of prime spectra; the translation between the two is the injection
`PrimeSpectrum.asIdeal`, and the statements below are phrased with the preimage along it rather
than with a new subtype.

## References

* [Stacks Project, Tag 056L](https://stacks.math.columbia.edu/tag/056L)
* [Stacks Project, Tag 056M](https://stacks.math.columbia.edu/tag/056M)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- On an affine open `V` of `X`, the canonical morphism `Spec Γ(X, V) ⟶ X` carries the primes
weakly associated to the sections `Γ(F, V)` onto the weakly associated points of `F` lying in
`V`. -/
theorem weaklyAssociatedPoints_inter_eq_image_fromSpec (F : X.Modules) [F.IsQuasicoherent]
    {V : X.Opens} (hV : IsAffineOpen V) :
    Stacks.Divisors.weaklyAssociatedPoints F ∩ (V : Set X) =
      hV.fromSpec.base '' (PrimeSpectrum.asIdeal ⁻¹' weaklyAssociatedPrimes Γ(X, V) Γ(F, V)) := by
  ext x
  constructor
  · rintro ⟨hxF, hxV⟩
    exact ⟨hV.primeIdealOf ⟨x, hxV⟩,
      (isWeaklyAssociatedPrime_iff_isWeaklyAssociatedPoint F V hV x hxV).mpr hxF,
      hV.fromSpec_primeIdealOf ⟨x, hxV⟩⟩
  · rintro ⟨q, hq, rfl⟩
    have hxV : hV.fromSpec.base q ∈ V := hV.range_fromSpec.le ⟨q, rfl⟩
    have hq' : hV.primeIdealOf ⟨hV.fromSpec.base q, hxV⟩ = q :=
      hV.fromSpec.isOpenEmbedding.injective (hV.fromSpec_primeIdealOf _)
    exact ⟨(isWeaklyAssociatedPrime_iff_isWeaklyAssociatedPoint F V hV _ hxV).mp (by rwa [hq']),
      hxV⟩

/-- Over an affine open `V`, the sections `Γ(F, V)` have finitely many weakly associated primes
exactly when `F` has finitely many weakly associated points in `V`. -/
theorem weaklyAssociatedPrimes_sections_finite_iff (F : X.Modules) [F.IsQuasicoherent]
    {V : X.Opens} (hV : IsAffineOpen V) :
    (weaklyAssociatedPrimes Γ(X, V) Γ(F, V)).Finite ↔
      (Stacks.Divisors.weaklyAssociatedPoints F ∩ (V : Set X)).Finite := by
  rw [weaklyAssociatedPoints_inter_eq_image_fromSpec F hV]
  refine ⟨fun h => Set.Finite.image _ (h.preimage fun _ _ _ _ h => PrimeSpectrum.ext h),
    fun h => ?_⟩
  refine ((h.of_finite_image
    (hV.fromSpec.isOpenEmbedding.injective.injOn)).image PrimeSpectrum.asIdeal).subset ?_
  exact fun p hp => ⟨⟨p, hp.isPrime⟩, hp, rfl⟩

/-- If an open `W` of `X` meets the weakly associated points of `F` in a finite set, then the
sections of `F` over any affine open contained in `W` have finitely many weakly associated
primes. -/
theorem weaklyAssociatedPrimes_sections_finite (F : X.Modules) [F.IsQuasicoherent]
    {V W : X.Opens} (hV : IsAffineOpen V) (hVW : V ≤ W)
    (hW : (Stacks.Divisors.weaklyAssociatedPoints F ∩ (W : Set X)).Finite) :
    (weaklyAssociatedPrimes Γ(X, V) Γ(F, V)).Finite :=
  (weaklyAssociatedPrimes_sections_finite_iff F hV).mpr
    (hW.subset (Set.inter_subset_inter_right _ fun _ hx => hVW hx))

end AlgebraicGeometry
