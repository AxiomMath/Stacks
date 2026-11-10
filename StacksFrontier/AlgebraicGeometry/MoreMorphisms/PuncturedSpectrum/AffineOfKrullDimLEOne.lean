module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.KrullDimension.Zero
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PuncturedSpectrum.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The punctured spectrum of a Noetherian local ring of dimension at most one is affine

Let `A` be a Noetherian local ring of Krull dimension at most one. Then the punctured spectrum
of `A`, the open complement of the closed point of `Spec A`, is an affine open subscheme. When
`A` has dimension zero the punctured spectrum is empty, and otherwise prime avoidance produces an
element of the maximal ideal lying in no minimal prime, whose basic open set is exactly the
punctured spectrum.

## Main results

* `Stacks.PuncturedSpectrum.isAffineOpen_puncturedSpectrum_of_krullDimLE_one`: the punctured
  spectrum of a Noetherian local ring of Krull dimension at most one is an affine open.

## Implementation notes

The dimension-one hypothesis enters only through `Ring.krullDimLE_one_iff`, which says that every
prime of `A` is either minimal or maximal. Prime avoidance is applied in the form
`Ideal.subset_iUnion_iff_mem_of_isMaximal_of_finite`, whose contrapositive supplies the required
element of the maximal ideal: the maximal ideal is not one of the finitely many minimal primes,
because a local ring whose maximal ideal is a minimal prime has dimension zero.
-/

@[expose] public section

open AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.PuncturedSpectrum

/-- In a local ring of positive Krull dimension the maximal ideal is not a minimal prime: were it
minimal, every prime would be squeezed between it and itself, hence maximal. -/
private lemma maximalIdeal_notMem_minimalPrimes (A : Type u) [CommRing A] [IsLocalRing A]
    (h0 : ¬ Ring.KrullDimLE 0 A) : maximalIdeal A ∉ minimalPrimes A := by
  intro hmem
  refine h0 (Ring.krullDimLE_zero_iff.mpr fun I hI => ?_)
  have hle : I ≤ maximalIdeal A := IsLocalRing.le_maximalIdeal hI.ne_top
  rw [le_antisymm hle (((IsMinimalPrime.iff_minimal _).mp hmem).2 hI hle)]
  infer_instance

/-- Prime avoidance in a Noetherian local ring of positive Krull dimension: the maximal ideal
contains an element lying in none of the (finitely many) minimal primes. -/
private lemma exists_mem_maximalIdeal_notMem_minimalPrimes (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (h0 : ¬ Ring.KrullDimLE 0 A) :
    ∃ f ∈ maximalIdeal A, ∀ P ∈ minimalPrimes A, f ∉ P := by
  have hns : ¬ ((maximalIdeal A : Set A) ⊆ ⋃ P ∈ minimalPrimes A, (P : Set A)) := by
    rw [Ideal.subset_iUnion_iff_mem_of_isMaximal_of_finite
      (minimalPrimes.finite_of_isNoetherianRing A) ⊥ ⊥
      (fun P hP _ _ => hP.isPrime) bot_ne_top bot_ne_top]
    exact maximalIdeal_notMem_minimalPrimes A h0
  obtain ⟨f, hf, hf'⟩ := Set.not_subset.mp hns
  exact ⟨f, hf, fun P hP hfP => hf' (Set.mem_biUnion hP hfP)⟩

/-- In a Noetherian local ring of Krull dimension at most one and positive Krull dimension, the
punctured spectrum is the basic open set of any element of the maximal ideal avoiding every
minimal prime: such an element lies in no non-maximal prime, since every prime is minimal or
maximal. -/
@[ega "IV 21.12.9" "special case"]
lemma exists_puncturedSpectrum_eq_basicOpen (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (hA : Ring.KrullDimLE 1 A) (h0 : ¬ Ring.KrullDimLE 0 A) :
    ∃ f : ↑(CommRingCat.of A), puncturedSpectrum A = PrimeSpectrum.basicOpen f := by
  obtain ⟨f, hfm, hf⟩ := exists_mem_maximalIdeal_notMem_minimalPrimes A h0
  refine ⟨f, ?_⟩
  ext x
  change (x : PrimeSpectrum A) ≠ closedPoint A ↔ f ∉ (x : PrimeSpectrum A).asIdeal
  refine ⟨fun hx => ?_, fun hx hxc => hx ?_⟩
  · rcases Ring.krullDimLE_one_iff.mp hA (x : PrimeSpectrum A).asIdeal
      (x : PrimeSpectrum A).isPrime with hmin | hmax
    · exact hf _ hmin
    · exact absurd (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax)) hx
  · exact (congrArg PrimeSpectrum.asIdeal hxc).symm ▸ hfm

/-- **The punctured spectrum of a Noetherian local ring of Krull dimension at most one is
affine.** In dimension zero the spectrum is a single point, so the punctured spectrum is empty;
otherwise it is the basic open set of an element of the maximal ideal avoiding all minimal
primes. -/
@[ega "IV 21.12.9" "special case"]
theorem isAffineOpen_puncturedSpectrum_of_krullDimLE_one
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (hA : Ring.KrullDimLE 1 A) :
    IsAffineOpen (Stacks.puncturedSpectrum A) := by
  by_cases h0 : Ring.KrullDimLE 0 A
  · have hsub : Subsingleton (PrimeSpectrum A) := by
      have : Ring.KrullDimLE 0 A := h0
      exact Ring.KrullDimLE.subsingleton_primeSpectrum A
    exact IsAffineOpen.of_subsingleton fun x _ y _ => hsub.allEq x y
  · obtain ⟨f, hEq⟩ := exists_puncturedSpectrum_eq_basicOpen A hA h0
    exact hEq ▸ IsAffineOpen.Spec_basicOpen (R := .of A) f

end Stacks.PuncturedSpectrum

end
