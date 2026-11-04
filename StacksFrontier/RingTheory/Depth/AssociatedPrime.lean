module

public import StacksFrontier.RingTheory.Depth.Nakayama
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs

/-!
# Depth one rules out the maximal ideal as an associated prime

Over a local ring `(R, 𝔪)`, a finite module of depth at least one along `𝔪` does not have `𝔪`
among its associated primes in the exact-annihilator sense of
`IsAssociatedPrimeStacks`: an element of `𝔪` acting regularly kills any element whose
annihilator is `𝔪`, and the annihilator of `0` is the unit ideal, not `𝔪`.

## Main results

* `maximalIdeal_not_isAssociatedPrimeStacks_of_one_le_depth`.

## Implementation notes

The statement needs both `Module.depth` (through
`Module.one_le_depth_iff_exists_isSMulRegular`) and `IsAssociatedPrimeStacks`, and no module
carrying one of those reaches the other, so this is their meeting point. Unlike the Mathlib
predicate `IsAssociatedPrime`, `IsAssociatedPrimeStacks` asks for the annihilator of an element
to be the prime *exactly*, which is what makes the regular element argument immediate and the
Noetherian hypothesis unnecessary.

## References

* [Stacks Project, Tag 00LI](https://stacks.math.columbia.edu/tag/00LI)
-/

@[expose] public section

/-- Over a local ring, depth at least one rules out the maximal ideal being an associated prime
in the exact-annihilator sense. -/
public lemma maximalIdeal_not_isAssociatedPrimeStacks_of_one_le_depth
    {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    (hdepth : 1 ≤ Module.depth R (IsLocalRing.maximalIdeal R) M) :
    ¬ IsAssociatedPrimeStacks R M (IsLocalRing.maximalIdeal R) := by
  intro hass
  obtain ⟨r, hr, hrreg⟩ :=
    (Module.one_le_depth_iff_exists_isSMulRegular (R := R) (M := M)
      (IsLocalRing.maximalIdeal R)).mp hdepth
  obtain ⟨_, m, hm⟩ := hass
  have hrann : r ∈ (⊥ : Submodule R M).colon (Submodule.span R {m}) := by
    rw [hm]
    exact hr
  have hrm0 : r • m ∈ (⊥ : Submodule R M) :=
    Submodule.mem_colon_span_singleton.mp hrann
  have hrm : r • m = 0 := by simpa only [Submodule.mem_bot] using hrm0
  have hm0 : m = 0 := hrreg (by simp [hrm])
  have htop : IsLocalRing.maximalIdeal R = ⊤ := by
    apply le_antisymm le_top
    rw [← hm, hm0]
    simp
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top htop

end
