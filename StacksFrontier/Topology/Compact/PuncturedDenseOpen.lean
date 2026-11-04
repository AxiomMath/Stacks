module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Separation.Basic

/-!
# Quasi-compact dense opens and a closed point

Let `x` be a closed point of a topological space `X` and suppose the punctured space
`X ∖ {x}` has no subset which is at once open, compact and dense. Then every open compact
dense subset of `X` contains `x`: otherwise it would be such a subset of the punctured
space, the complement of a closed point being open.

This turns a statement about the punctured space — which is how the counterexamples of
Stacks 086H and Stacks 087I are formulated — into one about the whole space.

## Main results

* `TopologicalSpace.mem_of_isOpen_of_isCompact_of_dense`: the point lies in every open
  compact dense subset.

## References

* [Stacks Project, Tag 086H](https://stacks.math.columbia.edu/tag/086H)
-/

@[expose] public section

open Topology

namespace TopologicalSpace

/-- **A quasi-compact dense open contains a closed point whose complement has none.** If the
complement of a closed point `x` of `X` contains no open compact dense subset, then every
open compact dense subset of `X` contains `x`.

The complement of `x` is open, so its inclusion is an open embedding; the preimage of an
open compact dense subset avoiding `x` along that inclusion is again open, compact and
dense. -/
theorem mem_of_isOpen_of_isCompact_of_dense {X : Type*} [TopologicalSpace X] (x : X)
    (h : ¬ ∃ V : Set {y : X // y ≠ x}, IsOpen V ∧ IsCompact V ∧ Dense V)
    {U : Set X} (hU : IsOpen U) (hcompact : IsCompact U) (hdense : Dense U)
    (hx : IsClosed ({x} : Set X)) : x ∈ U := by
  by_contra hnot
  refine h ?_
  have hj : IsOpenEmbedding (Subtype.val : {y : X // y ≠ x} → X) :=
    hx.isOpen_compl.isOpenEmbedding_subtypeVal
  refine ⟨Subtype.val ⁻¹' U, hU.preimage continuous_subtype_val, ?_,
    hdense.preimage hj.isOpenMap⟩
  refine hj.isEmbedding.isCompact_iff.mpr ?_
  have himage : (Subtype.val : {y : X // y ≠ x} → X) '' (Subtype.val ⁻¹' U) = U := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    refine ⟨fun ⟨z, hz, hzy⟩ => hzy ▸ hz, fun hy => ⟨⟨y, fun he => hnot (he ▸ hy)⟩, hy, rfl⟩⟩
  rwa [himage]

end TopologicalSpace

end
