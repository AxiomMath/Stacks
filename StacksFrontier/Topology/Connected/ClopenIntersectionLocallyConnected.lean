module

public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Intersections of clopen sets in a locally connected space

In a locally connected space the connected component of every point is open, and a clopen set
containing a point contains its connected component.  So an intersection of *any* family of
clopen sets is a union of connected components, hence open as well as closed.  This fails in
general: in the Cantor set every point is an intersection of clopen sets.

Applied to the level sets of a family of locally constant functions, this says that the locus
where infinitely many locally constant functions take prescribed values is open and closed as
soon as the space is locally connected.  A space that is only *locally* the source of a
continuous map to a locally connected space, along which the functions factor, has the same
property; this is the shape of an argument by reduction to a locally Noetherian situation, a
locally Noetherian space being locally connected.

## Main results

* `isOpen_iInter_of_isClopen`: in a locally connected space, an arbitrary intersection of clopen
  sets is open.
* `isClopen_iInter_of_isClopen`: and so clopen.
* `IsLocallyConstant.isClosed_setOf_forall_eq`: in any space, the locus where a family of
  locally constant functions takes prescribed values is closed.
* `IsLocallyConstant.isClopen_setOf_forall_eq`: in a locally connected space that locus is also
  open.
* `isClopen_setOf_forall_eq_of_locally_factors`: the same conclusion when the family factors,
  near every point and after pulling back along an open map, through a continuous map to a
  locally connected space and a family of locally constant functions there.
-/

@[expose] public section

open Set Topology

variable {X : Type*} [TopologicalSpace X] {ι : Sort*}

/-- In a locally connected space an arbitrary intersection of clopen sets is open: it contains
the connected component of each of its points, and those components are open. -/
theorem isOpen_iInter_of_isClopen [LocallyConnectedSpace X] {s : ι → Set X}
    (hs : ∀ i, IsClopen (s i)) : IsOpen (⋂ i, s i) := by
  refine isOpen_iff_mem_nhds.2 fun x hx => ?_
  refine Filter.mem_of_superset (isOpen_connectedComponent.mem_nhds mem_connectedComponent) ?_
  exact subset_iInter fun i => (hs i).connectedComponent_subset (mem_iInter.1 hx i)

/-- In a locally connected space an arbitrary intersection of clopen sets is clopen. -/
theorem isClopen_iInter_of_isClopen [LocallyConnectedSpace X] {s : ι → Set X}
    (hs : ∀ i, IsClopen (s i)) : IsClopen (⋂ i, s i) :=
  ⟨isClosed_iInter fun i => (hs i).isClosed, isOpen_iInter_of_isClopen hs⟩

namespace IsLocallyConstant

variable {β : Type*} {f : ι → X → β}

/-- The locus where a family of locally constant functions takes prescribed values is closed,
being an intersection of fibres, each of which is clopen. -/
theorem isClosed_setOf_forall_eq (hf : ∀ i, IsLocallyConstant (f i)) (c : ι → β) :
    IsClosed {x | ∀ i, f i x = c i} := by
  rw [Set.ofPred_forall]
  exact isClosed_iInter fun i => ((hf i).isClopen_fiber (c i)).isClosed

/-- In a locally connected space the locus where a family of locally constant functions takes
prescribed values is open and closed, however large the family. -/
theorem isClopen_setOf_forall_eq [LocallyConnectedSpace X] (hf : ∀ i, IsLocallyConstant (f i))
    (c : ι → β) : IsClopen {x | ∀ i, f i x = c i} := by
  rw [Set.ofPred_forall]
  exact isClopen_iInter_of_isClopen fun i => (hf i).isClopen_fiber (c i)

end IsLocallyConstant

/-- Let `f` be a family of functions on `X`.  Suppose that every point `x` is the image of a point
`x'` under an open map `p : X' ⟶ X`, and that near `x'` the family `f ∘ p` factors as `f₀ i ∘ g`
through a map `g` to a locally connected space `Y`, continuous at `x'`, and a family `f₀` of
locally constant functions on `Y`.  Then near every point the whole family is constant. -/
theorem eventually_forall_eq_of_locally_factors {β : Type*} {f : ι → X → β}
    (hf : ∀ x : X, ∃ (X' : Type*) (_ : TopologicalSpace X') (p : X' → X) (x' : X'),
      p x' = x ∧ IsOpenMap p ∧ ∃ V ∈ 𝓝 x', ∃ (Y : Type*) (_ : TopologicalSpace Y)
        (_ : LocallyConnectedSpace Y) (g : X' → Y) (f₀ : ι → Y → β),
          ContinuousAt g x' ∧ (∀ i, IsLocallyConstant (f₀ i)) ∧
            ∀ i, ∀ y ∈ V, f i (p y) = f₀ i (g y))
    (x : X) : ∀ᶠ y in 𝓝 x, ∀ i, f i y = f i x := by
  obtain ⟨X', _, p, x', rfl, hp, V, hV, Y, _, _, g, f₀, hg, hf₀, hfac⟩ := hf x
  have hW : {z : Y | ∀ i, f₀ i z = f₀ i (g x')} ∈ 𝓝 (g x') :=
    (IsLocallyConstant.isClopen_setOf_forall_eq hf₀ fun i => f₀ i (g x')).isOpen.mem_nhds
      fun i => rfl
  have hN : V ∩ g ⁻¹' {z : Y | ∀ i, f₀ i z = f₀ i (g x')} ∈ 𝓝 x' :=
    Filter.inter_mem hV (hg hW)
  filter_upwards [hp.image_mem_nhds hN]
  rintro _ ⟨y', ⟨hy'V, hy'W⟩, rfl⟩ i
  rw [hfac i y' hy'V, hfac i x' (mem_of_mem_nhds hV)]
  exact hy'W i

/-- Let `f` be a family of functions on `X`.  Suppose that every point `x` is the image of a point
`x'` under an open map `p : X' ⟶ X`, and that near `x'` the family `f ∘ p` factors as `f₀ i ∘ g`
through a map `g` to a locally connected space `Y`, continuous at `x'`, and a family `f₀` of
locally constant functions on `Y`.  Then the locus where the family takes prescribed values is
open and closed.

The spaces, the maps and the families may change from point to point.  This is the topological
content of the reduction of such a statement to the case where the functions live on a locally
connected (for instance a locally Noetherian) space, after passing to an open covering, or to a
covering by the images of open maps such as étale or smooth morphisms. -/
theorem isClopen_setOf_forall_eq_of_locally_factors {β : Type*} {f : ι → X → β}
    (hf : ∀ x : X, ∃ (X' : Type*) (_ : TopologicalSpace X') (p : X' → X) (x' : X'),
      p x' = x ∧ IsOpenMap p ∧ ∃ V ∈ 𝓝 x', ∃ (Y : Type*) (_ : TopologicalSpace Y)
        (_ : LocallyConnectedSpace Y) (g : X' → Y) (f₀ : ι → Y → β),
          ContinuousAt g x' ∧ (∀ i, IsLocallyConstant (f₀ i)) ∧
            ∀ i, ∀ y ∈ V, f i (p y) = f₀ i (g y))
    (c : ι → β) : IsClopen {x | ∀ i, f i x = c i} := by
  have key := eventually_forall_eq_of_locally_factors hf
  refine ⟨isOpen_compl_iff.1 (isOpen_iff_mem_nhds.2 fun x hx => ?_),
    isOpen_iff_mem_nhds.2 fun x hx => ?_⟩
  · filter_upwards [key x] with y hy
    exact fun h => hx fun i => (hy i).symm.trans (h i)
  · filter_upwards [key x] with y hy
    exact fun i => (hy i).trans (hx i)
