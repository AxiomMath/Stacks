module

public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.UniformSpace.Cauchy
public import StacksCore.Tactic.StacksAttribute

@[expose] public section

/-!
# Baire category for complete linearly topologized groups

Stacks Project, Chapter 15 "More on Algebra". The tags treated here are

0CQU, 0CQV.

## Tag 0CQU — Baire category for complete linearly topologized groups

A complete linearly topologized abelian group with a countable fundamental system of
neighbourhoods of zero satisfies the Baire category conclusion for sequences of open dense sets.

### Main definitions

### Main results

* `dense_iInter_of_isOpen_of_complete_linearTopology`: a countable intersection of
  open dense subsets of such a group is dense.

### Implementation notes

Linear topologization is expressed as `IsLinearTopology ℤ M`, and completeness is taken with
respect to the canonical right uniformity of the topological additive group. A sequence indexed
from one in the source is reindexed by `ℕ`.

### References

* [Stacks Project, Tag 0CQU](https://stacks.math.columbia.edu/tag/0CQU)

## Tag 0CQV — Open subgroups in countable closed covers

A countable cover of a complete linearly topologized abelian group by closed subgroups contains
an open subgroup.

### Main definitions

### Main results

* `exists_isOpen_of_iUnion_eq_univ_of_complete_linearTopology`: one member of a
  countable closed-subgroup cover is open.

### Implementation notes

Completeness is taken with respect to the canonical right uniformity of the topological additive
group. A sequence indexed from one in the source is reindexed by `ℕ`.

### References

* [Stacks Project, Tag 0CQV](https://stacks.math.columbia.edu/tag/0CQV)

-/

/-! ### Stacks Tag 0CQU -/

section

section

public section

open Filter Topology

/-- The Baire category theorem for complete linearly topologized abelian groups with a
countable fundamental system of neighbourhoods of zero. -/
@[stacks 0CQU]
public theorem dense_iInter_of_isOpen_of_complete_linearTopology
    {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [T2Space M] [IsLinearTopology ℤ M]
    (hcomplete : @CompleteSpace M (IsTopologicalAddGroup.rightUniformSpace M))
    (hcount : (nhds (0 : M)).IsCountablyGenerated)
    {U : ℕ → Set M} (hUopen : ∀ n, IsOpen (U n)) (hUdense : ∀ n, Dense (U n)) :
    Dense (⋂ n, U n) := by
  let : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
  let : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup
  let _ : CompleteSpace M := hcomplete
  let _ : (nhds (0 : M)).IsCountablyGenerated := hcount
  let _ : (uniformity M).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  let _ : TopologicalSpace.IsCompletelyPseudoMetrizableSpace M := inferInstance
  exact dense_iInter_of_isOpen_nat hUopen hUdense

end

end

end

/-! ### Stacks Tag 0CQV -/

section

section

public section

open Filter Topology

/-- A countable closed-subgroup cover of a complete linearly topologized abelian group contains
an open subgroup. -/
@[stacks 0CQV]
public theorem exists_isOpen_of_iUnion_eq_univ_of_complete_linearTopology
    {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [T2Space M] [IsLinearTopology ℤ M]
    (hcomplete : @CompleteSpace M (IsTopologicalAddGroup.rightUniformSpace M))
    (hcount : (nhds (0 : M)).IsCountablyGenerated)
    (N : ℕ → AddSubgroup M) (hNclosed : ∀ n, IsClosed (N n : Set M))
    (hNcover : (⋃ n, (N n : Set M)) = Set.univ) :
    ∃ n, IsOpen (N n : Set M) := by
  by_contra h
  push Not at h
  have hdense : ∀ n, Dense ((N n : Set M)ᶜ) := fun n ↦
    interior_eq_empty_iff_dense_compl.1 <| Set.eq_empty_iff_forall_notMem.2 fun x hx ↦
      h n <| AddSubgroup.isOpen_of_mem_nhds (N n) (mem_interior_iff_mem_nhds.1 hx)
  have hinter := dense_iInter_of_isOpen_of_complete_linearTopology
    hcomplete hcount (fun n ↦ (hNclosed n).isOpen_compl) hdense
  have hempty : (⋂ n, ((N n : Set M)ᶜ)) = ∅ := by
    rw [← Set.compl_iUnion, hNcover, Set.compl_univ]
  rw [hempty] at hinter
  simpa using hinter.nonempty

end

end

end

end
