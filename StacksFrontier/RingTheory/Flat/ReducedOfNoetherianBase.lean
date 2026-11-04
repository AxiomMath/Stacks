module

public import StacksFrontier.RingTheory.Flat.ReducedFibres

/-!
# Reducedness ascends along a flat map from a reduced Noetherian ring with reduced generic fibres

Let `R` be a reduced Noetherian ring and `S` a flat `R`-algebra, with no finiteness condition on
`S`.  If the fibre ring `κ(𝔭) ⊗_R S` is reduced at every *minimal* prime `𝔭` of `R`, then `S` is
reduced.

## Main results

* `isReduced_of_flat_of_isNoetherianRing_of_isReduced_minimalFibres`.

## Implementation notes

This is the argument of `Stacks.Flatness.ReducedFibreAscent.solution` (Stacks 0C21), which uses
neither the Noetherian hypothesis on `S` nor the fibres away from the minimal primes: `R` embeds
into the finite product `∏ κ(𝔭)` over its minimal primes because `R` is reduced, flatness keeps
`S ↪ S ⊗_R ∏ κ(𝔭) ≅ ∏ (S ⊗_R κ(𝔭))`, and a subring of a reduced ring is reduced.  It is
`Stacks.Flatness.ReducedFibreAscent.isReduced_of_flat_of_forall_isReduced_fiber` at the family of
minimal primes.
-/

@[expose] public section

universe u v

/-- **Reducedness ascends along a flat map from a reduced Noetherian ring whose fibres at the
minimal primes are reduced.**  Let `R` be a reduced Noetherian ring and `S` a flat `R`-algebra,
not necessarily Noetherian.  If the fibre ring `κ(𝔭) ⊗_R S` is reduced for every minimal prime
`𝔭` of `R`, then `S` is reduced. -/
theorem isReduced_of_flat_of_isNoetherianRing_of_isReduced_minimalFibres {R : Type u}
    {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R] [IsReduced R]
    [Module.Flat R S]
    (hfibre : ∀ (p : Ideal R) [p.IsPrime], p ∈ minimalPrimes R → IsReduced (p.Fiber S)) :
    IsReduced S := by
  have : Finite {q : Ideal R // q ∈ minimalPrimes R} :=
    (minimalPrimes.finite_of_isNoetherianRing R).to_subtype
  exact Stacks.Flatness.ReducedFibreAscent.isReduced_of_flat_of_forall_isReduced_fiber
    (S := S) (ι := {q : Ideal R // q ∈ minimalPrimes R}) Subtype.val
    (hp := fun i => Ideal.IsMinimalPrime.isPrime i.2)
    (fun r hr => Stacks.Flatness.ReducedFibreAscent.eq_zero_of_forall_mem_minimalPrimes
      fun q hq => hr ⟨q, hq⟩)
    (fun i => @hfibre i.1 (Ideal.IsMinimalPrime.isPrime i.2) i.2)

end
