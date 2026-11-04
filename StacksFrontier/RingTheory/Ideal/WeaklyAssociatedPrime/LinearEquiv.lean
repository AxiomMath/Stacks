module

public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.Defs

/-!
# Weakly associated primes across a linear equivalence

Linearly equivalent modules have the same weakly associated primes.

## Main results

* `LinearEquiv.isWeaklyAssociatedPrime_iff`: a prime is weakly associated to `M` if and only if
  it is weakly associated to `N`.
-/

@[expose] public section

namespace LinearEquiv

/-- For a linear equivalence `e : M ≃ₗ[R] N`, a prime `p` is weakly associated to `M` if and only
if it is weakly associated to `N`. -/
theorem isWeaklyAssociatedPrime_iff {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (p : Ideal R) :
    IsWeaklyAssociatedPrime R M p ↔ IsWeaklyAssociatedPrime R N p := by
  refine ⟨fun ⟨m, hm⟩ ↦ ⟨e m, ?_⟩, fun ⟨n, hn⟩ ↦ ⟨e.symm n, ?_⟩⟩ <;>
    convert ‹p ∈ _› using 2 <;>
    ext r <;>
    simp only [Submodule.mem_annihilator_span_singleton, ← map_smul, LinearEquiv.map_eq_zero_iff]

end LinearEquiv
