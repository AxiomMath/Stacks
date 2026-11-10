module

public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.RingHom.Flat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Going down for minimal primes, across universes

The contraction of a minimal prime along a flat ring map is a minimal prime, for source and
target in arbitrary universes.

## Main results

* `StacksDraft.comap_mem_minimalPrimes_of_ringHom_flat`: the contraction of a minimal prime along
  a flat ring map is a minimal prime.
-/

@[expose] public section

universe u v

namespace StacksDraft

/-- **Going down for minimal primes.** The contraction of a minimal prime along a flat ring map
is a minimal prime; source and target may live in different universes. -/
@[ega "IV 4.7.2" "more general"]
theorem comap_mem_minimalPrimes_of_ringHom_flat {A : Type u} {C : Type v} [CommRing A]
    [CommRing C] (f : A →+* C) (hf : f.Flat) {q : Ideal C} (hq : q ∈ minimalPrimes C) :
    q.comap f ∈ minimalPrimes A := by
  have : q.IsPrime := hq.1.1
  let : Algebra A C := f.toAlgebra
  have : Module.Flat A C := hf
  have : Algebra.HasGoingDown A C := Algebra.HasGoingDown.of_flat
  change q.comap (algebraMap A C) ∈ minimalPrimes A
  refine ⟨⟨Ideal.comap_isPrime _ _, bot_le⟩, ?_⟩
  rintro P ⟨hP, -⟩ hPq
  have : q.LiesOver (q.comap (algebraMap A C)) := ⟨rfl⟩
  obtain ⟨P', hP'q, hP', hP'P⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := P) q hPq
  exact (Ideal.comap_mono (hq.2 ⟨hP', bot_le⟩ hP'q)).trans hP'P.over.ge

end StacksDraft
