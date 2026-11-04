module

public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Spectral.Hom
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Spectral.ConstructiblyClosed

/-!
# W-local spaces and w-local maps

A *w-local* space is a spectral space whose closed points form a closed subset and in which
every point has a unique closed specialization. A *w-local* map is a spectral map carrying
closed points to closed points. Closed subspaces of w-local spaces are again w-local.

## Main definitions

* `AlgebraicGeometry.ProEtale.WLocalSpace`: the class of w-local topological spaces.
* `AlgebraicGeometry.ProEtale.IsWLocalMap`: the predicate that a map of topological spaces is
  w-local.

## Main results

* `AlgebraicGeometry.ProEtale.WLocalSpace.existsUnique_closedPoint_specializes`: a point of a
  w-local space has a unique closed specialization.
* `AlgebraicGeometry.ProEtale.IsWLocalMap.isClosed_singleton`: a w-local map carries closed
  points to closed points.
* `AlgebraicGeometry.ProEtale.wLocalSpace_of_isClosed`: a closed subspace of a w-local space is
  w-local.
* `AlgebraicGeometry.ProEtale.wLocalSpace_of_homeomorph`: w-locality transports backwards along a
  homeomorphism.

## Implementation notes

In a spectral space the existence of a closed specialization follows from compactness and the
Kolmogorov separation axiom, so `WLocalSpace` records only its uniqueness and the
existence-and-uniqueness formulation is supplied as a theorem. Closed points are Mathlib's
`closedPoints` and specialization is Mathlib's `Specializes`.

The predicate `IsWLocalMap` does not require its source and target to be w-local. This harmless
generalization makes the two defining properties reusable independently of ambient instances.

A closed subset is regarded as a subtype with its induced topology, and the statement about it is
class-valued, so clients install the resulting structure locally when they need it. The same holds
for the transport of w-locality along a homeomorphism, whose source needs no ambient spectrality
assumption: a homeomorphism is an open embedding of a compact space, so spectrality transports
too.

## References

* [Stacks Project, Tag 096A](https://stacks.math.columbia.edu/tag/096A)
* [Stacks Project, Tag 096B](https://stacks.math.columbia.edu/tag/096B)
-/

@[expose] public section

namespace AlgebraicGeometry.ProEtale

/-- A spectral space is w-local if its closed points form a closed subset and every point has a
unique closed specialization. Existence of a closed specialization is automatic for spectral
spaces, so the class records its uniqueness. -/
@[stacks 096A "w-local spaces"]
class WLocalSpace (X : Type*) [TopologicalSpace X] : Prop extends SpectralSpace X where
  /-- Two closed specializations of the same point in a w-local space coincide. -/
  eq_of_specializes {x c c' : X} (hc : IsClosed {c}) (hc' : IsClosed {c'})
    (hxc : Specializes x c) (hxc' : Specializes x c') : c = c'
  /-- The set of closed points of a w-local space is closed. -/
  isClosed_closedPoints : IsClosed (closedPoints X)

attribute [instance] WLocalSpace.isClosed_closedPoints

/-- Every point of a w-local space has a unique closed specialization. -/
theorem WLocalSpace.existsUnique_closedPoint_specializes {X : Type*} [TopologicalSpace X]
    [WLocalSpace X] (x : X) :
    ∃! c : X, c ∈ closedPoints X ∧ Specializes x c := by
  obtain ⟨c, hc, hclosed⟩ :=
    isClosed_closure.exists_closed_singleton ⟨x, subset_closure (Set.mem_singleton x)⟩
  exact ⟨c, ⟨mem_closedPoints_iff.mpr hclosed, specializes_iff_mem_closure.mpr hc⟩,
    fun c' hc' => WLocalSpace.eq_of_specializes (mem_closedPoints_iff.mp hc'.1) hclosed hc'.2
      (specializes_iff_mem_closure.mpr hc)⟩

/-- A map is w-local if it is spectral and sends every closed point to a closed point. -/
@[mk_iff, stacks 096A "w-local maps"]
structure IsWLocalMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop extends IsSpectralMap f where
  /-- A w-local map sends closed points to closed points. -/
  closedPoints_subset_preimage_closedPoints :
    closedPoints X ⊆ f ⁻¹' closedPoints Y

/-- A w-local map sends closed points to closed points. -/
theorem IsWLocalMap.isClosed_singleton {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsWLocalMap f) {x : X} (hx : IsClosed {x}) :
    IsClosed {f x} :=
  mem_closedPoints_iff.mp
    (hf.closedPoints_subset_preimage_closedPoints (mem_closedPoints_iff.mpr hx))

/-- A spectral space with a continuous injection into a w-local space, pulling closed points back
to closed points, is w-local. -/
private theorem wLocalSpace_of_injective {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SpectralSpace X] [WLocalSpace Y] {f : X → Y} (hf : Continuous f) (hinj : f.Injective)
    (hpoints : f ⁻¹' closedPoints Y = closedPoints X) : WLocalSpace X := by
  refine ⟨fun {x c c'} hc hc' hxc hxc' => hinj ?_, ?_⟩
  · have hcl {d : X} (hd : IsClosed {d}) : IsClosed {f d} :=
      mem_closedPoints_iff.mp (hpoints.ge (mem_closedPoints_iff.mpr hd))
    exact WLocalSpace.eq_of_specializes (hcl hc) (hcl hc') (hxc.map hf) (hxc'.map hf)
  · rw [← hpoints]
    exact WLocalSpace.isClosed_closedPoints.preimage hf

/-- A closed subspace of a w-local space is w-local. -/
@[stacks 096B]
theorem wLocalSpace_of_isClosed {X : Type*} [TopologicalSpace X] [WLocalSpace X]
    {Y : Set X} (hY : IsClosed Y) : WLocalSpace Y :=
  have : SpectralSpace Y :=
    spectralSpace_of_isClosed_constructibleTopology Y hY.isClosed_constructibleTopology
  wLocalSpace_of_injective continuous_subtype_val Subtype.val_injective
    hY.isClosedEmbedding_subtypeVal.preimage_closedPoints

/-- A space homeomorphic to a w-local space is w-local. -/
theorem wLocalSpace_of_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [WLocalSpace Y] (e : X ≃ₜ Y) : WLocalSpace X :=
  have : CompactSpace X := e.symm.compactSpace
  have : SpectralSpace X := e.isOpenEmbedding.spectralSpace
  wLocalSpace_of_injective e.continuous e.injective (by
    ext x
    simpa only [Set.mem_preimage, mem_closedPoints_iff] using
      (by simpa using e.isClosed_image (s := {x}) : IsClosed ({e x} : Set Y) ↔ IsClosed {x}))

end AlgebraicGeometry.ProEtale
