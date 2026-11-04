module

public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge

/-!
# Finite local freeness of a prescribed rank

A module which is finite locally free of some rank `r`, in the sense of
`Module.IsFiniteLocallyFreeOfRank`, is finite locally free, and hence finite and projective.

## Main results

* `Module.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree`: forgetting the rank.
* `Module.IsFiniteLocallyFreeOfRank.finite_and_projective`: such a module is finite and
  projective.
-/

@[expose] public section

universe u

/-- A module which is finite locally free of some rank is finite locally free: a basis indexed by
`Fin r` makes each localization free and finite over the localized ring. -/
public theorem Module.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree {R : Type u} [CommRing R]
    {M : Type u} [AddCommGroup M] [Module R M] {r : ℕ}
    (h : Module.IsFiniteLocallyFreeOfRank R M r) : Module.IsFiniteLocallyFree R M := by
  obtain ⟨ι, f, hspan, hbasis⟩ := h
  refine ⟨ι, f, hspan, fun i => ?_⟩
  obtain ⟨b⟩ := hbasis i
  exact ⟨Module.Free.of_basis b, Module.Finite.of_basis b⟩

/-- **A module finite locally free of a rank is finite and projective.** The Fitting criterion of
[Stacks, Tag 07ZD] delivers finite local freeness of a prescribed rank; this is the form in which
a consumer that needs a presentation, rather than a rank, uses it. -/
public theorem Module.IsFiniteLocallyFreeOfRank.finite_and_projective {R : Type u} [CommRing R]
    {M : Type u} [AddCommGroup M] [Module R M] {r : ℕ}
    (h : Module.IsFiniteLocallyFreeOfRank R M r) :
    Module.Finite R M ∧ Module.Projective R M :=
  (Module.isFiniteLocallyFree_iff_finite_projective R M).mp h.isFiniteLocallyFree

end
