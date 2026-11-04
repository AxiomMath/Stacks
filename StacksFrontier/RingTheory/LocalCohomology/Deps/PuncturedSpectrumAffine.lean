module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.KrullDimension.Zero
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PuncturedSpectrum.Defs
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PuncturedSpectrum.AffineOfKrullDimLEOne

/-!
# The punctured spectrum of a local ring, and when it is affine

For a local ring `A` the *punctured spectrum* is the open subscheme `Spec A ∖ {𝔪}` obtained by
removing the unique closed point.  Stacks Tag 0BCR says that for `A` Noetherian local the
punctured spectrum is affine if and only if `dim A ≤ 1`.

This file sets up the punctured spectrum and treats the elementary implication: if
`dim A ≤ 1` then the punctured spectrum is affine.  If `dim A = 0` the punctured spectrum is
empty.  Otherwise prime avoidance produces an element `f` of the maximal ideal lying in no
minimal prime; since every prime of `A` is either minimal or maximal, the basic open `D(f)` is
exactly the complement of the closed point, and a basic open of an affine scheme is affine.

## Main definitions

* `Stacks.Divisors.puncturedSpectrum` — the open `Spec A ∖ {𝔪}` of `Spec A`.

## Main results

* `Stacks.Divisors.isAffineOpen_puncturedSpectrum_of_krullDimLE_one` — the elementary
  implication of Stacks 0BCR.

## Implementation notes

The reverse implication of Tag 0BCR, that an affine punctured spectrum forces `dim A ≤ 1`, is of
a different nature. The source reduces it to Tag 0BCU (the local ring at a generic point of a
component of the complement of an affine open immersion has dimension at most one), whose own
proof reduces back to Tag 0BCR at the stalk: for `X = Spec A` and `U` the punctured spectrum the
two are the same statement. Either one needs the cohomological finiteness argument of the
source.

## References

* [Stacks Project, Tag 0BCR](https://stacks.math.columbia.edu/tag/0BCR)
-/

@[expose] public section

open AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.Divisors

export Stacks (puncturedSpectrum)

add_to_stacks 0BLF "the punctured spectra" Stacks.puncturedSpectrum

/-- In a local ring that is not zero-dimensional the maximal ideal is contained in no minimal
prime: were it contained in one it would *be* that minimal prime, and then every prime of the
ring, lying below the maximal ideal, would equal it and so be maximal. -/
theorem maximalIdeal_not_le_minimalPrimes_of_not_krullDimLE_zero
    (A : Type u) [CommRing A] [IsLocalRing A] (P : Ideal A)
    (hP : P ∈ minimalPrimes A) (h0 : ¬ Ring.KrullDimLE 0 A) :
    ¬ IsLocalRing.maximalIdeal A ≤ P := by
  intro hmP
  apply h0
  rw [Ring.krullDimLE_zero_iff]
  intro I hI
  obtain ⟨Q, hQ, hQI⟩ :=
    Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A)) (J := I) bot_le
  have hQm : Q ≤ IsLocalRing.maximalIdeal A :=
    le_trans hQI (IsLocalRing.le_maximalIdeal hI.ne_top)
  have hPm : IsLocalRing.maximalIdeal A ∈ minimalPrimes A := by
    have hPle : P ≤ IsLocalRing.maximalIdeal A :=
      IsLocalRing.le_maximalIdeal hP.1.1.ne_top
    have hPeq : P = IsLocalRing.maximalIdeal A := le_antisymm hPle hmP
    simpa [hPeq] using hP
  have hQeq : Q = IsLocalRing.maximalIdeal A :=
    ((IsMinimalPrime.iff_minimal _).mp hPm).eq_of_le hQ.1.1 hQm
  have hIe : I = IsLocalRing.maximalIdeal A := le_antisymm
    (IsLocalRing.le_maximalIdeal hI.ne_top) (hQeq ▸ hQI)
  rw [hIe]
  exact IsLocalRing.maximalIdeal.isMaximal A

/-- **Prime avoidance in a Noetherian local ring of positive dimension.**  If `A` is Noetherian
local and not zero-dimensional, some element of the maximal ideal lies in no minimal prime.

There are only finitely many minimal primes, none of which contains the maximal ideal, so the
maximal ideal is not covered by their union. -/
theorem exists_mem_maximalIdeal_notMem_minimalPrimes
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (h0 : ¬ Ring.KrullDimLE 0 A) :
    ∃ f ∈ IsLocalRing.maximalIdeal A, ∀ P ∈ minimalPrimes A, f ∉ P := by
  have hnotMem : IsLocalRing.maximalIdeal A ∉ minimalPrimes A := fun hmem =>
    maximalIdeal_not_le_minimalPrimes_of_not_krullDimLE_zero A _ hmem h0 le_rfl
  have hnotSubset :
      ¬ ((IsLocalRing.maximalIdeal A : Set A) ⊆ ⋃ P ∈ minimalPrimes A, (P : Set A)) := by
    rw [Ideal.subset_iUnion_iff_mem_of_isMaximal_of_finite
      (minimalPrimes.finite_of_isNoetherianRing A) ⊥ ⊥
      (fun P hP _ _ => hP.1.1) bot_ne_top bot_ne_top]
    exact hnotMem
  obtain ⟨f, hfm, hf⟩ := Set.not_subset.mp hnotSubset
  exact ⟨f, hfm, by simpa using hf⟩

/-- In a Noetherian local ring of dimension at most one and positive dimension, the punctured
spectrum is the basic open of any element of the maximal ideal avoiding every minimal prime:
a prime avoids such an element exactly when it is not the maximal ideal, because every prime is
either minimal or maximal. -/
alias exists_puncturedSpectrum_eq_basicOpen :=
  Stacks.PuncturedSpectrum.exists_puncturedSpectrum_eq_basicOpen

/-- **One implication of Stacks 0BCR.**  The punctured spectrum of a Noetherian local ring of
Krull dimension at most one is affine. -/
@[ega "IV 21.12.9" "special case"]
theorem isAffineOpen_puncturedSpectrum_of_krullDimLE_one
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : Ring.KrullDimLE 1 A) :
    IsAffineOpen (puncturedSpectrum A) := by
  by_cases h0 : Ring.KrullDimLE 0 A
  · apply IsAffineOpen.of_subsingleton
    have : Ring.KrullDimLE 0 (↑(CommRingCat.of A)) := h0
    have : Subsingleton (PrimeSpectrum (↑(CommRingCat.of A))) :=
      Ring.KrullDimLE.subsingleton_primeSpectrum (↑(CommRingCat.of A))
    have : Subsingleton (Spec (.of A)) := by
      show Subsingleton (PrimeSpectrum (↑(CommRingCat.of A)))
      infer_instance
    intro x _ y _
    exact Subsingleton.elim x y
  · obtain ⟨f, hEq⟩ := exists_puncturedSpectrum_eq_basicOpen A hA h0
    rw [hEq]
    exact basicOpen_eq_of_affine f ▸ (isAffineOpen_top (Spec (.of A))).basicOpen _

end Stacks.Divisors
