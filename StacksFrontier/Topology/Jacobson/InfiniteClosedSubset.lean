module

public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.NoetherianSpace

/-!
# An infinite closed subset of a Noetherian Jacobson space

In a Noetherian space every closed subset is a finite union of irreducible closed subsets, so a
closed subset with infinitely many points has an irreducible closed piece with infinitely many
points.  In a Jacobson space the closed points of a closed subset are dense in it, and a finite
set of closed points is closed; so an irreducible closed subset with infinitely many points has
infinitely many closed points.

Together: a closed subset of a Noetherian Jacobson space which is infinite contains an
irreducible closed subset carrying infinitely many closed points of the ambient space.  This is
the topological content of the step of [Stacks, Tag 0AEM] which extracts a contracted curve from
an infinite fibre: the fibre is closed because the morphism is proper, and the irreducible piece
is the subvariety that gets mapped to a point, two of whose rational points drive the rest of
the argument.

## Main results

* `Set.Infinite.exists_isIrreducible_infinite_inter_closedPoints`: the statement above.
* `Set.Infinite.exists_pair_ne_mem_closedPoints_of_isClosed`: the two distinct closed points of
  a common irreducible closed piece, which is the form the extraction consumes.

## References

* [Stacks Project, Tag 005U](https://stacks.math.columbia.edu/tag/005U)
* [Stacks Project, Tag 0052](https://stacks.math.columbia.edu/tag/0052)
* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
-/

@[expose] public section

open TopologicalSpace

variable {α : Type*} [TopologicalSpace α]

/-- In a Jacobson space an irreducible closed subset with infinitely many points carries
infinitely many closed points of the ambient space: the closed points of a closed subset are
dense in it, and were there only finitely many of them they would form a closed set, which
would then be the whole subset. -/
theorem Set.Infinite.infinite_inter_closedPoints [JacobsonSpace α] {C : Set α} (hC : IsClosed C)
    (hinf : C.Infinite) : (C ∩ closedPoints α).Infinite := by
  intro hfin
  refine hinf ?_
  have hclosed : IsClosed (C ∩ closedPoints α) := by
    rw [← Set.biUnion_of_singleton (C ∩ closedPoints α)]
    exact hfin.isClosed_biUnion fun x hx ↦ hx.2
  rw [← JacobsonSpace.closure_inter_closedPoints hC, hclosed.closure_eq]
  exact hfin

/-- **An infinite closed subset of a Noetherian Jacobson space has an irreducible closed piece
with infinitely many closed points.**  The Noetherian hypothesis writes the subset as a finite
union of irreducible closed subsets, one of which must be infinite; the Jacobson hypothesis
then supplies the closed points of that one. -/
theorem Set.Infinite.exists_isIrreducible_infinite_inter_closedPoints [NoetherianSpace α]
    [JacobsonSpace α] {S : Set α} (hS : IsClosed S) (hinf : S.Infinite) :
    ∃ C : Set α, C ⊆ S ∧ IsClosed C ∧ IsIrreducible C ∧ (C ∩ closedPoints α).Infinite := by
  obtain ⟨𝒮, h𝒮fin, h𝒮closed, h𝒮irr, hSU⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hS
  have hex : ∃ C ∈ 𝒮, C.Infinite := by
    by_contra h
    push Not at h
    exact hinf (hSU ▸ h𝒮fin.sUnion fun C hC ↦ h C hC)
  obtain ⟨C, hC𝒮, hCinf⟩ := hex
  exact ⟨C, hSU ▸ Set.subset_sUnion_of_mem hC𝒮, h𝒮closed C hC𝒮, h𝒮irr C hC𝒮,
    hCinf.infinite_inter_closedPoints (h𝒮closed C hC𝒮)⟩

/-- **Two distinct closed points of one irreducible closed piece of an infinite closed subset
of a Noetherian Jacobson space.**  This is the shape in which the extraction step of
[Stacks, Tag 0AEM] uses an infinite fibre. -/
theorem Set.Infinite.exists_pair_ne_mem_closedPoints_of_isClosed [NoetherianSpace α]
    [JacobsonSpace α] {S : Set α} (hS : IsClosed S) (hinf : S.Infinite) :
    ∃ (C : Set α) (x y : α), C ⊆ S ∧ IsClosed C ∧ IsIrreducible C ∧
      x ∈ C ∧ y ∈ C ∧ IsClosed {x} ∧ IsClosed {y} ∧ x ≠ y := by
  obtain ⟨C, hCS, hCclosed, hCirr, hCinf⟩ :=
    hinf.exists_isIrreducible_infinite_inter_closedPoints hS
  obtain ⟨x, hx, y, hy, hxy⟩ := hCinf.nontrivial
  exact ⟨C, x, y, hCS, hCclosed, hCirr, hx.1, hy.1, hx.2, hy.2, hxy⟩

end
