module

public import Mathlib.Topology.Sober
import StacksCore.Tactic.StacksAttribute

/-!
# An indiscrete space is quasi-sober but not Kolmogorov (Stacks 0B32)

Let `X` carry the indiscrete topology and have at least two points (`Nontrivial X`). The
only closed subsets are `∅` and `X`, and the closure of any singleton is `X`, so the only
irreducible closed subset, `X` itself, has a generic point: `X` is quasi-sober.
But any two points of an indiscrete space are inseparable (`Inseparable.all`), so with two
distinct points `X` is not Kolmogorov.

Stacks 0B32 also observes that `X` is nevertheless covered by Kolmogorov subspaces, namely
its singletons. The covering and discreteness of the singleton subspaces are registered
directly from Mathlib's `Set.iUnion_of_singleton` and `Subsingleton.discreteTopology`.

## References

* [Stacks Project, Tag 0B32](https://stacks.math.columbia.edu/tag/0B32)
-/

@[expose] public section

/-- **Stacks 0B32.** An indiscrete topological space with at least two points is
quasi-sober: its only nonempty closed subset is the whole space, and every point is a
generic point for it. -/
@[stacks 0B32 "quasi-sober"]
theorem quasiSober_of_indiscreteTopology (X : Type*) [TopologicalSpace X]
    [IndiscreteTopology X] [Nontrivial X] : QuasiSober X := by
  refine ⟨fun {S} hirr hclos => ?_⟩
  rcases (IndiscreteTopology.isClosed_iff S).mp hclos with rfl | rfl
  · exact absurd hirr.nonempty (by simp)
  · obtain ⟨x⟩ : Nonempty X := inferInstance
    exact ⟨x, closure_indiscrete (Set.singleton_nonempty x)⟩

/-- **Stacks 0B32.** An indiscrete topological space with at least two points is not
Kolmogorov: any two of its points are inseparable. -/
@[stacks 0B32 "not Kolmogorov"]
theorem not_t0Space_of_indiscreteTopology (X : Type*) [TopologicalSpace X]
    [IndiscreteTopology X] [Nontrivial X] : ¬ T0Space X := by
  intro h
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  exact hxy (T0Space.t0 (Inseparable.all x y))

add_to_stacks 0B32 "the singleton subspaces cover the space" Set.iUnion_of_singleton
add_to_stacks 0B32 "the singleton subspaces are discrete" Subsingleton.discreteTopology
