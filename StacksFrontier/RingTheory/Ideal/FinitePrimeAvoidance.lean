module

public import Mathlib.RingTheory.Ideal.Operations
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Prime avoidance in element form

An ideal contained in none of finitely many prime ideals has an element lying outside all of
them. This is the contrapositive, in element form, of `Ideal.subset_union_prime_finite`.

## Main results

* `exists_mem_forall_notMem_of_forall_not_le`: prime avoidance in element form.
-/

@[expose] public section

/-- Prime avoidance, in element form: an ideal `I` contained in none of the finitely many primes
of a family `s` has an element lying outside every member of `s`. -/
@[sga "3 V 4.1" "more general"]
theorem exists_mem_forall_notMem_of_forall_not_le {R : Type*} [CommRing R]
    {s : Set (Ideal R)} (hs : s.Finite) (hp : ∀ q ∈ s, q.IsPrime) {I : Ideal R}
    (h : ∀ q ∈ s, ¬I ≤ q) : ∃ x ∈ I, ∀ q ∈ s, x ∉ q := by
  by_contra! H
  obtain ⟨q, hq, hle⟩ := (Ideal.subset_union_prime_finite hs (f := fun q : Ideal R => q) I I
    fun q hq _ _ => hp q hq).mp fun x hx => by simpa using H x hx
  exact h q hq hle

end
