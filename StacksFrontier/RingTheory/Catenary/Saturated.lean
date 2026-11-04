module

public import StacksFrontier.RingTheory.Catenary.Basic

/-!
# Catenarity with a common chain length implies the pairwise formulation

`Ring.IsCatenary` asks that two comparable primes admit a saturated chain of some common length;
`IsCatenaryRingSaturated` asks that every saturated chain between them has that length. The first
implies the second.

## Main results

* `isCatenaryRingSaturated_of_isCatenary`: `Ring.IsCatenary A` implies `IsCatenaryRingSaturated A`.
-/

@[expose] public section

universe u

/-- A ring which is catenary in the sense of `Ring.IsCatenary` is catenary in the saturated-chain
sense `IsCatenaryRingSaturated`. -/
theorem isCatenaryRingSaturated_of_isCatenary {A : Type u} [CommRing A]
    (hcat : Ring.IsCatenary A) : IsCatenaryRingSaturated A := by
  intro p q hpq
  obtain ⟨⟨N, hN⟩, n, hn⟩ := hcat p q hpq
  refine ⟨⟨N, hN⟩, fun s t hsp hsq htp htq => ?_⟩
  exact (hn (covToLT s) hsp hsq s.step).trans (hn (covToLT t) htp htq t.step).symm

end
