module

public import StacksCore.Tactic.StacksAttribute
public import StacksCore.Topology.Compact.LocallyQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique

/-!
# Local quasi-compactness of the point space of an algebraic space

Every point of an algebraic space over `S` has a fundamental system of quasi-compact open
neighbourhoods, so its space of points is locally quasi-compact in the sense of Stacks 0068,
that is Mathlib's `LocallyCompactSpace`.

On a scheme the affine opens are a basis of the topology and are quasi-compact, which gives
the fundamental system there; the point space of a represented presheaf is homeomorphic to
the representing scheme, and a surjective étale atlas is a continuous open surjection onto
the point space of the algebraic space, so the system is carried over by taking images.

## Main results

* `AlgebraicGeometry.Scheme.hasBasis_nhds_isOpen_isCompact`: the quasi-compact open
  neighbourhoods of a point of a scheme are a fundamental system.
* `AlgebraicGeometry.Space.hasBasis_nhds_isOpen_isCompact`: the quasi-compact open
  neighbourhoods of a point of an algebraic space are a fundamental system.
* `AlgebraicGeometry.Space.locallyCompactSpace`: the space of points of an algebraic space is
  locally quasi-compact.

## Implementation notes

`AlgebraicGeometry.Space.pointTopology` is a plain definition rather than an instance and is
made a local instance here.

## References

* [Stacks Project, Tag 04NN](https://stacks.math.columbia.edu/tag/04NN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The quasi-compact open neighbourhoods of a point of a scheme are a fundamental system of
neighbourhoods. -/
theorem Scheme.hasBasis_nhds_isOpen_isCompact {X : Scheme.{u}} (x : X) :
    (nhds x).HasBasis (fun U : Set X ↦ IsOpen U ∧ IsCompact U ∧ x ∈ U) id :=
  (nhds_basis_opens x).to_hasBasis (fun O ⟨hxO, hO⟩ ↦ by
      obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAO⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxO hO
      exact ⟨A, ⟨A.2, hA.isCompact, hxA⟩, hAO⟩)
    fun U ⟨hU, _, hxU⟩ ↦ ⟨U, ⟨hxU, hU⟩, subset_rfl⟩

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The quasi-compact open neighbourhoods of a point of the point space of a represented
presheaf are a fundamental system, that space being homeomorphic to the representing scheme
by `AlgebraicGeometry.Space.schemePointsHomeomorph`. -/
theorem hasBasis_nhds_isOpen_isCompact_points_yoneda (U : BigFppfOver B S hS)
    (x : points B S hS (yoneda.obj U)) :
    (nhds x).HasBasis
      (fun W : Set (points B S hS (yoneda.obj U)) ↦ IsOpen W ∧ IsCompact W ∧ x ∈ W) id :=
  (schemePointsHomeomorph B S hS U).symm.isOpenMap.hasBasis_nhds_isOpen_isCompact
    (schemePointsHomeomorph B S hS U).symm.continuous
    (schemePointsHomeomorph B S hS U).symm.surjective
    (fun z ↦ Scheme.hasBasis_nhds_isOpen_isCompact z) x

/-- The quasi-compact open neighbourhoods of a point of an algebraic space over `S` are a
fundamental system of neighbourhoods of that point. -/
@[stacks 04NN "fundamental system of open quasi-compact neighbourhoods"]
theorem hasBasis_nhds_isOpen_isCompact (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (x : points B S hS F) :
    (nhds x).HasBasis
      (fun W : Set (points B S hS F) ↦ IsOpen W ∧ IsCompact W ∧ x ∈ W) id := by
  obtain ⟨U, f, hsurj, hetale⟩ := hF.exists_atlas
  exact (isOpenMap_pointsMap_of_etale B S hS hF U f hetale).hasBasis_nhds_isOpen_isCompact
    (continuous_pointsMap B S hS f)
    ((surjective_iff_surjective_pointsMap B S hS F hF U f).mp hsurj)
    (hasBasis_nhds_isOpen_isCompact_points_yoneda B S hS U) x

/-- The space of points of an algebraic space over `S` is locally quasi-compact. -/
@[stacks 04NN "local quasi-compactness"]
theorem locallyCompactSpace (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) : LocallyCompactSpace (points B S hS F) :=
  LocallyCompactSpace.of_hasBasis (hasBasis_nhds_isOpen_isCompact B S hS F hF)
    fun _ _ h ↦ h.2.1

end Space

end AlgebraicGeometry

end
