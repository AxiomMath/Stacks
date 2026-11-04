module

public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober
public import StacksCore.Tactic.StacksAttribute
public import StacksCore.Topology.NowhereDense.Defs

/-!
# Nowhere dense closed subsets and generic points

Two topological facts about nowhere dense subsets, used to recognise when the support of a
subsheaf is nowhere dense in the support of the ambient sheaf.

The first says that a nowhere dense closed subset of a space misses the generic point of every
irreducible component of any Noetherian open subspace: an irreducible component contains a
nonempty open subset of the ambient space, and if the component were contained in the subset,
that open subset would land in its interior.

The second says that the closure of a point which is not the generic point of an irreducible
component is nowhere dense: any point in the interior of the closure witnesses that the closure
is maximal among irreducible closed subsets.

## Main definitions

* `Stacks.AlgebraicGeometry.EmbeddedPoints.subtypeCommHomeomorph`: for subsets `U` and `S` of a
  space, the points of `U` lying in `S` and the points of `S` lying in `U` are homeomorphic.

## Main results

* `Stacks.AlgebraicGeometry.EmbeddedPoints.notMem_of_isGenericPoint_of_isNowhereDense`: the
  generic point of an irreducible component of a Noetherian open subspace is not in a nowhere
  dense closed subset.
* `Stacks.AlgebraicGeometry.EmbeddedPoints.isNowhereDense_closure_singleton`: the closure of a
  point which is not the generic point of an irreducible component is nowhere dense.
* `Stacks.AlgebraicGeometry.EmbeddedPoints.isNowhereDense_setOf_mem_closure_singleton`: the same,
  relative to a closed subspace containing the point.

## References

* [Stacks Project, Tag 02OL](https://stacks.math.columbia.edu/tag/02OL)
* [Stacks Project, Tag 03HN](https://stacks.math.columbia.edu/tag/03HN)
-/

@[expose] public section

open TopologicalSpace

namespace Stacks.AlgebraicGeometry.EmbeddedPoints

/-- The points of `U` that lie in `S` and the points of `S` that lie in `U` are the same points of
the ambient space, so the two nested subspaces are homeomorphic. -/
def subtypeCommHomeomorph {Y : Type*} [TopologicalSpace Y] (U S : Set Y) :
    {u : ↥U // (u : Y) ∈ S} ≃ₜ {x : ↥S // (x : Y) ∈ U} where
  toEquiv :=
    { toFun := fun u ↦ ⟨⟨u.1.1, u.2⟩, u.1.2⟩
      invFun := fun x ↦ ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  continuous_toFun := by
    refine continuous_induced_rng.mpr (continuous_induced_rng.mpr ?_)
    change Continuous fun z : {u : ↥U // (u : Y) ∈ S} ↦ (z.1.1 : Y)
    exact continuous_subtype_val.comp continuous_subtype_val
  continuous_invFun := by
    refine continuous_induced_rng.mpr (continuous_induced_rng.mpr ?_)
    change Continuous fun z : {x : ↥S // (x : Y) ∈ U} ↦ (z.1.1 : Y)
    exact continuous_subtype_val.comp continuous_subtype_val

/-- The image of the generic point of an irreducible component of a Noetherian space under an
open embedding is not in a nowhere dense closed subset of the target.

Were it in the subset, the whole component would be, since the component is the closure of the
generic point and the preimage of the subset is closed. A Noetherian space has, inside every
irreducible component, a nonempty open subset of the whole space, and the image of that subset is
then a nonempty open subset of the closure of the nowhere dense subset. -/
@[ega "0 2.1.4" "special case"]
lemma notMem_of_isGenericPoint_of_isNowhereDense
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    (e : T → S) (he : Topology.IsOpenEmbedding e) [NoetherianSpace T]
    {A : Set S} (hAclosed : IsClosed A) (hAND : IsNowhereDense A)
    {Z : Set T} (hZ : Z ∈ irreducibleComponents T)
    {y : T} (hy : IsGenericPoint y Z) : e y ∉ A := by
  intro hey
  have hZsub : Z ⊆ e ⁻¹' A := by
    rw [← hy.def]
    refine closure_minimal ?_ (hAclosed.preimage he.continuous)
    intro z hz
    simpa only [Set.mem_singleton_iff] using hz ▸ hey
  obtain ⟨o, hopen, hne, hoZ⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ
  have hImgsub : e '' o ⊆ A := by
    rintro _ ⟨z, hz, rfl⟩
    exact hZsub (hoZ hz)
  obtain ⟨z, hz⟩ := hne
  have hInterior : (interior (closure A)).Nonempty :=
    ⟨e z, mem_interior.mpr ⟨e '' o, hImgsub.trans subset_closure, he.isOpenMap _ hopen, z, hz, rfl⟩⟩
  rw [IsNowhereDense] at hAND
  rw [hAND] at hInterior
  exact absurd hInterior.choose_spec (Set.notMem_empty _)

/-- The closure of a point whose closure is not an irreducible component is nowhere dense: a
point of the interior of that closure would make it maximal among the irreducible closed
subsets. -/
lemma isNowhereDense_closure_singleton {Y : Type*} [TopologicalSpace Y] (x : Y)
    (hx : ¬ closure ({x} : Set Y) ∈ irreducibleComponents Y) :
    IsNowhereDense (closure ({x} : Set Y)) := by
  rw [IsNowhereDense, closure_closure]
  refine Set.eq_empty_iff_forall_notMem.mpr fun y hy ↦ hx ⟨isIrreducible_singleton.closure, ?_⟩
  intro C hC hsub
  have hd := (isPreirreducible_iff_subset_closure_inter_open C).mp hC.2
    (interior (closure ({x} : Set Y))) isOpen_interior
    ⟨y, hsub (interior_subset hy), hy⟩
  exact hd.trans (closure_minimal (fun _ h ↦ interior_subset h.2) isClosed_closure)

/-- Inside a closed subspace `S`, the trace of the closure of a point `x` of `S` is nowhere dense
as soon as `x` is not the generic point of an irreducible component of `S`.

The trace is the closure of `x` taken in `S`, because `S` is closed, and
`Stacks.AlgebraicGeometry.EmbeddedPoints.isNowhereDense_closure_singleton` applies to it. -/
lemma isNowhereDense_setOf_mem_closure_singleton {Y : Type*} [TopologicalSpace Y] (S : Set Y)
    (hS : IsClosed S) {x : Y} (hx : x ∈ S)
    (hng : ¬ ∃ Z ∈ irreducibleComponents S, IsGenericPoint x (Subtype.val '' Z)) :
    IsNowhereDense {y : S | (y : Y) ∈ closure ({x} : Set Y)} := by
  have hc : closure ({(⟨x, hx⟩ : S)} : Set S) = {y : S | (y : Y) ∈ closure ({x} : Set Y)} := by
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
    simp only [Set.image_singleton]
    rfl
  rw [← hc]
  refine isNowhereDense_closure_singleton _ fun h ↦ hng ⟨_, h, ?_⟩
  refine isGenericPoint_def.mpr ?_
  have he := hS.isClosedEmbedding_subtypeVal.isClosedMap.closure_image_eq_of_continuous
    continuous_subtype_val ({(⟨x, hx⟩ : S)} : Set S)
  simpa only [Set.image_singleton] using he

end Stacks.AlgebraicGeometry.EmbeddedPoints

end
