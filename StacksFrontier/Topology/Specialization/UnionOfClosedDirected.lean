module

public import Mathlib.Topology.Inseparable

import StacksCore.Tactic.StacksAttribute

/-!
# Sets stable under specialization are directed unions of closed sets

Stacks 0EES: a subset `T` of a topological space is stable under specialization if and only if it
is a (directed) union of closed subsets. Mathlib's `stableUnderSpecialization_iff_exists_sUnion_eq`
gives the equivalence with an arbitrary union of closed subsets; here the family is moreover
directed under inclusion: one can take all closed subsets contained in `T`, which is directed since
a union of two closed sets is closed.

## References

* [Stacks Project, Tag 0EES](https://stacks.math.columbia.edu/tag/0EES)
-/

@[expose] public section

variable {X : Type*} [TopologicalSpace X]

/-- A subset `T` of a topological space is stable under specialization if and only if it is the
union of a family of closed subsets which is directed under inclusion. -/
@[stacks 0EES "directed form: (1) ⇔ (2) with the family of closed subsets directed under inclusion;
the undirected form is Mathlib's `stableUnderSpecialization_iff_exists_sUnion_eq`"]
theorem stableUnderSpecialization_iff_exists_directedOn_sUnion_eq {T : Set X} :
    StableUnderSpecialization T ↔
      ∃ S : Set (Set X), DirectedOn (· ⊆ ·) S ∧ (∀ Z ∈ S, IsClosed Z) ∧ ⋃₀ S = T := by
  constructor
  · intro hT
    refine ⟨{Z | IsClosed Z ∧ Z ⊆ T}, ?_, fun Z hZ => hZ.1, ?_⟩
    · rintro Z₁ ⟨h₁, h₁T⟩ Z₂ ⟨h₂, h₂T⟩
      exact ⟨Z₁ ∪ Z₂, ⟨h₁.union h₂, Set.union_subset h₁T h₂T⟩,
        Set.subset_union_left, Set.subset_union_right⟩
    · refine Set.Subset.antisymm (Set.sUnion_subset fun Z hZ => hZ.2) fun x hx => ?_
      refine Set.mem_sUnion.2 ⟨closure {x}, ⟨isClosed_closure, ?_⟩, subset_closure rfl⟩
      intro y hy
      exact hT (specializes_iff_mem_closure.2 hy) hx
  · rintro ⟨S, -, hS, rfl⟩
    exact stableUnderSpecialization_iff_exists_sUnion_eq.2 ⟨S, hS, rfl⟩
