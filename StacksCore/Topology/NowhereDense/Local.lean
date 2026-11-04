module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.GDelta.Basic

/-!
# Nowhere density is local on an open cover

For the inclusion of an open subset, preimages commute with closure and interior. Any point
in the interior of the global closure would therefore lie in the interior of the local
closure in a member of the cover, contradicting local nowhere density.

## Main results

* `nowhere_dense_local` (Stacks 03HP): a subset that is nowhere dense in each member of an open
  cover is nowhere dense.

## References

* [Stacks Project, Tag 03HP](https://stacks.math.columbia.edu/tag/03HP)
-/

@[expose] public section

/-- **Stacks 03HP.** Nowhere density is local on open covers: if `{U i}` is an open cover of `X`
and `T ∩ U i` (encoded as the preimage of `T` under the inclusion `U i → X`) is nowhere dense in
the subspace `U i` for every `i`, then `T` is nowhere dense in `X`. -/
@[stacks 03HP]
theorem nowhere_dense_local
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} (U : ι → Set X)
    (hU_open : ∀ i, IsOpen (U i))
    (hU_cover : ⋃ i, U i = Set.univ)
    (T : Set X)
    (hT_local : ∀ i, IsNowhereDense ((Subtype.val : U i → X) ⁻¹' T)) :
    IsNowhereDense T := by
  rw [IsNowhereDense, Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨i, hxU⟩ := Set.iUnion_eq_univ_iff.mp hU_cover x
  have hmap := (hU_open i).isOpenMap_subtype_val
  have hlift : (⟨x, hxU⟩ : U i) ∈ interior (closure ((Subtype.val : U i → X) ⁻¹' T)) := by
    rw [← hmap.preimage_closure_eq_closure_preimage continuous_subtype_val,
      ← hmap.preimage_interior_eq_interior_preimage continuous_subtype_val]
    exact hx
  exact absurd hlift (hT_local i ▸ Set.notMem_empty _)
