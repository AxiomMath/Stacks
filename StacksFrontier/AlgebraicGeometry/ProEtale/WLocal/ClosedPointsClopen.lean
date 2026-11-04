module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Limits.ClopenLift
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.Basic
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.ClopenRefinement
public import StacksFrontier.Topology.Spectral.BijectionHomeomorph
public import StacksFrontier.Topology.Spectral.ComponentSpace
public import StacksFrontier.Topology.Spectral.ConstructiblyClosed
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Clopen subsets of a w-local space and of its closed points

Let `X` be a w-local space. Restricting along the inclusion of the closed points identifies the
clopen subsets of `X` with those of `closedPoints X`, because both are identified with the clopen
subsets of the space of connected components of `X`. This file records the ingredients of that
identification that are used to cut a w-local spectrum into the pieces produced by a finite
vanishing stratification of a base ring.

## Main definitions

* `AlgebraicGeometry.ProEtale.closedPointsHomeoConnectedComponents`: the closed points of a
  w-local space are homeomorphic to its space of connected components.
The clopen subset of `X` attached to a clopen subset of `closedPoints X` is
`AlgebraicGeometry.ProEtale.closedPointsClopenLift`, in
`StacksFrontier.AlgebraicGeometry.ProEtale.Limits.ClopenLift`, re-exported here.

## Main results

* `AlgebraicGeometry.ProEtale.isClopen_preimage_closedPoints_of_isConstructible`: a constructible
  subset of a w-local space meets the closed points in a clopen subset.
* `AlgebraicGeometry.ProEtale.mem_closedPointsClopenLift_iff`: a point lies in the lift of a
  clopen subset of the closed points exactly when its closed specialization does.

## Implementation notes

The set of closed points of a w-local space is closed, hence spectral in the induced topology,
and it is `T1` because its points are closed in `X`. A constructible subset of a spectral space
whose complement and itself are both stable under generalization is clopen, and in a `T1` space
every subset is stable under generalization; this is the whole content of the first result.

The homeomorphism with the space of connected components is the continuous bijection sending a
closed point to its component, promoted using that the source is quasi-compact and the target is
Hausdorff. The lift of a clopen subset is the preimage of its image in the space of connected
components, so it is a union of connected components.

## References

* [Stacks Project, Tag 096A](https://stacks.math.columbia.edu/tag/096A)
* [Stacks Project, Tag 0968](https://stacks.math.columbia.edu/tag/0968)
-/

@[expose] public section

namespace AlgebraicGeometry.ProEtale

open TopologicalSpace

private lemma connectedComponents_mk_eq_of_specializes
    {X : Type*} [TopologicalSpace X] {x y : X} (hxy : Specializes x y) :
    ConnectedComponents.mk x = ConnectedComponents.mk y := by
  have hycl : y ∈ closure ({x} : Set X) := specializes_iff_mem_closure.mp hxy
  have hycc : y ∈ connectedComponent x :=
    isPreconnected_singleton.closure.subset_connectedComponent
      (subset_closure (Set.mem_singleton x)) hycl
  exact (ConnectedComponents.coe_eq_coe'.2 hycc).symm

/-- A constructible subset of a w-local space meets the closed points in a clopen subset. -/
lemma isClopen_preimage_closedPoints_of_isConstructible
    {X : Type*} [TopologicalSpace X] [WLocalSpace X]
    {s : Set X} (hs : Topology.IsConstructible s) :
    IsClopen ((Subtype.val : closedPoints X → X) ⁻¹' s) := by
  have : SpectralSpace (closedPoints X) :=
    spectralSpace_of_isClosed_constructibleTopology _
      WLocalSpace.isClosed_closedPoints.isClosed_constructibleTopology
  have : T1Space (closedPoints X) := ⟨fun x => by
    refine (isClosed_induced_iff).2 ⟨{(x : X)},
      mem_closedPoints_iff.mp x.2, ?_⟩
    ext y
    simp [Subtype.ext_iff]⟩
  have hval : IsSpectralMap (Subtype.val : closedPoints X → X) :=
    (IsRetrocompact_iff_isSpectralMap_subtypeVal).mp fun U hUcompact hUopen => by
      simpa [Set.inter_comm] using hUcompact.inter_right WLocalSpace.isClosed_closedPoints
  have hcons : Topology.IsConstructible ((Subtype.val : closedPoints X → X) ⁻¹' s) :=
    hs.preimage continuous_subtype_val fun U hUopen hUcompact =>
      (hval.isCompact_preimage_of_isOpen hUopen hUcompact.isCompact).isRetrocompact
        (hUopen.preimage continuous_subtype_val)
  have hgen (t : Set (closedPoints X)) : StableUnderGeneralization t :=
    fun _ _ hxy hx => by rwa [hxy.eq]
  exact ⟨isOpen_compl_iff.mp (hcons.compl.isOpen_of_stableUnderGeneralization (hgen _)),
    hcons.isOpen_of_stableUnderGeneralization (hgen _)⟩

/-- The closed points of a w-local space are homeomorphic to its space of connected components,
by the map sending a closed point to the component containing it. -/
noncomputable def closedPointsHomeoConnectedComponents
    {X : Type*} [TopologicalSpace X] [WLocalSpace X] :
    closedPoints X ≃ₜ ConnectedComponents X := by
  letI : SpectralSpace (closedPoints X) :=
    spectralSpace_of_isClosed_constructibleTopology _
      WLocalSpace.isClosed_closedPoints.isClosed_constructibleTopology
  have huniq : ∀ x : X, ∃! x₀ : closedPoints X, Specializes x x₀.1 := by
    intro x
    obtain ⟨c, ⟨hc, hxc⟩, hunique⟩ :=
      WLocalSpace.existsUnique_closedPoint_specializes x
    exact ⟨⟨c, hc⟩, hxc, fun c' hc' => Subtype.ext (hunique c'.1 ⟨c'.2, hc'⟩)⟩
  have hbij :=
    closedPoints_to_connectedComponents_bijective_of_unique_specialization
      WLocalSpace.isClosed_closedPoints huniq
  letI : T2Space (ConnectedComponents X) := (connectedComponents_isProfinite X).1
  exact (isHomeomorph_iff_continuous_bijective.mpr
    ⟨ConnectedComponents.continuous_coe.comp continuous_subtype_val, hbij⟩).homeomorph

/-- A point of a w-local space lies in the lift of a clopen subset `S` of the closed points
exactly when its closed specialization lies in `S`. -/
theorem mem_closedPointsClopenLift_iff
    {X : Type*} [TopologicalSpace X] [WLocalSpace X]
    (S : Clopens (closedPoints X)) (x : X) :
    x ∈ closedPointsClopenLift S ↔
      ∃ c : closedPoints X, Specializes x c.1 ∧ c ∈ S :=
  mem_closedPointsClopenLift_iff_specialization S x

end AlgebraicGeometry.ProEtale

end
