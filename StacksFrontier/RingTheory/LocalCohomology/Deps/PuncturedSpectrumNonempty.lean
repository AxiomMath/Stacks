module

public import Mathlib.RingTheory.Ideal.Height
public import StacksFrontier.RingTheory.LocalCohomology.Deps.PuncturedSpectrumAffine
import StacksCore.Tactic.EgaSgaAttribute

/-!
# When the punctured spectrum of a local ring is nonempty

For a local ring `A` the punctured spectrum `Spec A ∖ {𝔪}` is nonempty exactly when
`1 ≤ dim A`: a prime other than the maximal ideal is a prime strictly below it, which is a chain
of length one, and conversely a ring of positive dimension has a minimal prime that is not the
maximal ideal.

## Main results

* `Stacks.Divisors.one_le_ringKrullDim_of_ne_maximalIdeal`
* `Stacks.Divisors.exists_isPrime_ne_maximalIdeal_of_one_le_ringKrullDim`
* `Stacks.Divisors.nonempty_puncturedSpectrum_iff_one_le_ringKrullDim`

## Implementation notes

No Noetherian hypothesis is needed, and none is imposed: the identity
`IsLocalRing.maximalIdeal_height_eq_ringKrullDim` holds for every local ring, and a minimal
prime below the maximal ideal exists by `Ideal.exists_minimalPrimes_le`.

The conclusion is stated for `Stacks.Divisors.puncturedSpectrum`.  Two other definitions of the
punctured spectrum exist in the library — `Stacks.puncturedSpectrum` in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/PuncturedSpectrum/Defs.lean` and
`Stacks.LocalCohomology.puncturedSpectrum` in
`StacksFrontier/AlgebraicGeometry/LocalCohomology/PuncturedSpectrum.lean`, the latter indexed by a
`CommRingCat` — and this file deliberately says nothing about them; the consumers that take the
nonemptiness as a hypothesis use this spelling.

The two ring-theoretic halves are stated separately from the iff, because that is the form in
which they are used: the first is applied to a point already in hand, the second produces one.
-/

@[expose] public section

open AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.Divisors

/-- A point of the punctured spectrum is a prime other than the closed point. -/
theorem mem_puncturedSpectrum_iff {A : Type u} [CommRing A] [IsLocalRing A]
    {x : PrimeSpectrum A} : x ∈ puncturedSpectrum A ↔ x ≠ closedPoint A :=
  Iff.rfl

/-- A prime of a local ring other than the maximal ideal lies strictly below it, so the maximal
ideal has height at least one and the ring has dimension at least one. -/
theorem one_le_ringKrullDim_of_ne_maximalIdeal {A : Type u} [CommRing A] [IsLocalRing A]
    (p : Ideal A) [p.IsPrime] (hp : p ≠ maximalIdeal A) : 1 ≤ ringKrullDim A := by
  rw [← maximalIdeal_height_eq_ringKrullDim]
  exact_mod_cast le_add_self.trans
    (Ideal.height_add_one_le_of_lt_of_isPrime ((le_maximalIdeal_of_isPrime p).lt_of_ne hp))

/-- In a local ring of dimension at least one some prime is not the maximal ideal: the maximal
ideal has positive height, hence is not a minimal prime, so any minimal prime below it differs
from it. -/
@[ega "II 7.1.5" "partial"]
theorem exists_isPrime_ne_maximalIdeal_of_one_le_ringKrullDim (A : Type u) [CommRing A]
    [IsLocalRing A] (h : 1 ≤ ringKrullDim A) :
    ∃ p : Ideal A, p.IsPrime ∧ p ≠ maximalIdeal A := by
  rw [← maximalIdeal_height_eq_ringKrullDim] at h
  have h1 : 1 ≤ (maximalIdeal A).height := by exact_mod_cast h
  have hnotmin : maximalIdeal A ∉ minimalPrimes A := fun hm => by
    rw [Ideal.height_eq_zero_iff.mpr hm] at h1
    exact absurd h1 (by simp)
  obtain ⟨q, hq, -⟩ :=
    Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A)) (J := maximalIdeal A) bot_le
  exact ⟨q, hq.1.1, fun he => hnotmin (he ▸ hq)⟩

/-- **The punctured spectrum of a local ring is nonempty exactly when the ring has dimension at
least one.**  Removing the closed point leaves a point precisely when some prime is not the
maximal ideal, which is the same as the maximal ideal having positive height. -/
theorem nonempty_puncturedSpectrum_iff_one_le_ringKrullDim (A : Type u) [CommRing A]
    [IsLocalRing A] :
    Nonempty (puncturedSpectrum A).toScheme ↔ 1 ≤ ringKrullDim A := by
  rw [Scheme.Opens.nonempty_iff]
  constructor
  · rintro ⟨x, hx⟩
    let y : PrimeSpectrum A := x
    exact one_le_ringKrullDim_of_ne_maximalIdeal y.asIdeal fun he =>
      hx (Set.mem_singleton_iff.mpr (PrimeSpectrum.ext he))
  · intro h
    obtain ⟨p, hp, hne⟩ := exists_isPrime_ne_maximalIdeal_of_one_le_ringKrullDim A h
    exact ⟨⟨p, hp⟩, fun hmem =>
      hne (congrArg PrimeSpectrum.asIdeal (Set.mem_singleton_iff.mp hmem))⟩

end Stacks.Divisors

end
