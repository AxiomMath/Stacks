module

public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOver

/-!
# Cofinality of the projection kernels in the completion over a subring

Let `B` be a weakly pre-admissible topological ring, let `f : B →+* A` be a ring map and
let `A^∧ = CompletionOver f` be the completion of `A` along the extensions of the weak ideals
of definition of `B`. Each kernel `ker (A^∧ → A ⧸ JA)`, for `J` a weak ideal of definition of
`B`, is a weak ideal of definition of `A^∧`
(`TopologicalRing.projection_ker_isWeakIdealOfDefinition`). This file proves the converse
cofinality statement: *every* open ideal of `A^∧` — in particular every weak ideal of
definition of `A^∧` — contains one of those kernels.

So the kernels of the projections are cofinal among the weak ideals of definition of `A^∧`,
which is what identifies the diagram `J ↦ Spec (A ⧸ JA)` indexed by the weak ideals of
definition of `B` as a cofinal subdiagram of the canonical diagram of quotient stages of
`A^∧`, and hence `Spf A^∧` with `colim_J Spec (A ⧸ JA)`.

## Main results

* `TopologicalRing.CompletionOver.exists_ker_projection_le_of_isOpen`: an open ideal of the
  completion contains the kernel of one of the projections.
* `TopologicalRing.CompletionOver.exists_ker_projection_le_of_isWeakIdealOfDefinition`: the
  same for a weak ideal of definition, which is the cofinality statement.

## Implementation notes

Both are read off from tautness of the canonical map `B → A^∧`
(`TopologicalRing.CompletionOver.isTaut_canonicalMap`, Tag 0AN6): the second clause of
`RingHom.IsTaut` says that the closures of the extended open ideals of `B` form a
neighbourhood basis of zero in `A^∧`, and
`TopologicalRing.CompletionOver.ker_projection_eq_closure` identifies the closure of the
extension of a weak ideal of definition with the kernel of the corresponding projection. An
open ideal `I ⊆ B` produced by the basis is cut down to a weak ideal of definition by
intersecting it with any weak ideal of definition of `B`, the intersection of an open set with
an open ideal being open and the topological nilpotence being inherited.

## References

* [Stacks Project, Tag 0AMY](https://stacks.math.columbia.edu/tag/0AMY)
* [Stacks Project, Tag 0AN6](https://stacks.math.columbia.edu/tag/0AN6)
-/

@[expose] public section

namespace TopologicalRing.CompletionOver

universe u v

variable {B : Type u} {A : Type v} [CommRing B] [TopologicalSpace B] [CommRing A]

/-- A weakly pre-admissible ring has a weak ideal of definition inside every open ideal: the
intersection of a weak ideal of definition with the given ideal is again one. -/
public theorem exists_weakIdealOfDefinitionIndex_le
    (hB : TopologicalRing.IsWeaklyPreAdmissible B) (I : Ideal B) (hI : IsOpen (I : Set B)) :
    ∃ J : TopologicalRing.WeakIdealOfDefinitionIndex B, (J.1 : Ideal B) ≤ I := by
  obtain ⟨J, hJ⟩ := hB
  exact ⟨⟨J ⊓ I, ⟨hJ.1.inter hI, fun x hx => hJ.2 x hx.1⟩⟩, inf_le_right⟩

/-- An open ideal of the completion of `A` over `B` contains the kernel of one of the
projections `A^∧ → A ⧸ JA`.

The closures of the extensions of the open ideals of `B` form a neighbourhood basis of zero in
`A^∧` because the canonical map is taut, and the closure of the extension of a weak ideal of
definition is the kernel of the corresponding projection. -/
public theorem exists_ker_projection_le_of_isOpen (f : B →+* A)
    (hB : TopologicalRing.IsWeaklyPreAdmissible B) {K : Ideal (CompletionOver f)}
    (hK : IsOpen (K : Set (CompletionOver f))) :
    ∃ J : TopologicalRing.WeakIdealOfDefinitionIndex B,
      RingHom.ker (projection f J) ≤ K := by
  obtain ⟨I, hI, hIK⟩ :=
    (isTaut_canonicalMap f hB).2.mem_iff.mp (hK.mem_nhds (Ideal.zero_mem K))
  obtain ⟨J, hJI⟩ := exists_weakIdealOfDefinitionIndex_le hB I hI
  refine ⟨J, ?_⟩
  rw [ker_projection_eq_closure f J]
  exact fun x hx => hIK (closure_mono (Ideal.map_mono hJI) hx)

/-- **The kernels of the projections `A^∧ → A ⧸ JA` are cofinal among the weak ideals of
definition of the completion of `A` over `B`.** Every weak ideal of definition of `A^∧`
contains one of them; each of them is one by
`TopologicalRing.projection_ker_isWeakIdealOfDefinition`. -/
public theorem exists_ker_projection_le_of_isWeakIdealOfDefinition
    (f : B →+* A) (hB : TopologicalRing.IsWeaklyPreAdmissible B)
    {K : Ideal (CompletionOver f)} (hK : TopologicalRing.IsWeakIdealOfDefinition K) :
    ∃ J : TopologicalRing.WeakIdealOfDefinitionIndex B,
      RingHom.ker (projection f J) ≤ K :=
  exists_ker_projection_le_of_isOpen f hB hK.1

end TopologicalRing.CompletionOver

end
