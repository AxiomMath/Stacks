module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# In a one-dimensional Noetherian local ring every closed set is cut out by one element

Let `R` be a Noetherian local ring of Krull dimension at most one and let `I` be an ideal of
`R`. Then there is a single element `f ∈ I` with

  `∀ p prime, f ∈ p ↔ I ≤ p`,

that is, `V(f) = V(I)` as subsets of `Spec R`.

## Main results

* `Stacks.RetrocompactOneDimensional.exists_mem_isPrime_mem_iff_le`: the statement above.

## References

* [Stacks Project, Tag 09N8](https://stacks.math.columbia.edu/tag/09N8)
* [Stacks Project, Tag 09N9](https://stacks.math.columbia.edu/tag/09N9)
-/

@[expose] public section

universe u

namespace Stacks.RetrocompactOneDimensional

/-- In a Noetherian local ring of dimension at most one, every ideal has the same vanishing locus
as one of its elements: for every ideal `I` there is `f ∈ I` such that a prime `p` contains `f` if
and only if it contains all of `I`. -/
theorem exists_mem_isPrime_mem_iff_le {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R] (I : Ideal R) :
    ∃ f ∈ I, ∀ p : Ideal R, p.IsPrime → (f ∈ p ↔ I ≤ p) := by
  classical
  by_cases htop : I = ⊤
  · subst htop
    exact ⟨1, Submodule.mem_top, fun p _ =>
      ⟨fun h => top_le_iff.2 ((Ideal.eq_top_iff_one p).2 h), fun h => h Submodule.mem_top⟩⟩
  · have hIm : I ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal htop
    set S : Set (Ideal R) := {q | q ∈ minimalPrimes R ∧ ¬ I ≤ q}
    have hSfin : S.Finite :=
      (minimalPrimes.finite_of_isNoetherianRing R).subset fun _ hq => hq.1
    have hSprime : ∀ q ∈ S, q ≠ ⊥ → q ≠ ⊥ → ((fun r : Ideal R => r) q).IsPrime :=
      fun _ hq _ _ => Ideal.IsMinimalPrime.isPrime hq.1
    have hnotsub : ¬ ((I : Set R) ⊆ ⋃ q ∈ S, (q : Set R)) := by
      rw [Ideal.subset_union_prime_finite (f := fun r : Ideal R => r) hSfin
        (⊥ : Ideal R) (⊥ : Ideal R) hSprime]
      rintro ⟨q, hq, hle⟩
      exact hq.2 hle
    obtain ⟨f, hfI, hf⟩ := Set.not_subset.mp hnotsub
    refine ⟨f, hfI, fun p hp => ⟨fun hfp => ?_, fun hle => hle hfI⟩⟩
    rcases Ring.krullDimLE_one_iff.mp ‹Ring.KrullDimLE 1 R› p hp with hmin | hmax
    · by_contra hcon
      exact hf (Set.mem_biUnion (show p ∈ S from ⟨hmin, hcon⟩) hfp)
    · exact (IsLocalRing.eq_maximalIdeal hmax) ▸ hIm

end Stacks.RetrocompactOneDimensional

end
