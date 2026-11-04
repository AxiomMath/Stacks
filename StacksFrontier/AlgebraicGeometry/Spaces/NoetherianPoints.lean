module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactTopology
public import StacksFrontier.Topology.Noetherian.Image
public import StacksFrontier.Topology.Noetherian.QuasiCompactLocally

/-!
# The topology of a locally Noetherian algebraic space

The point space of an algebraic space over `S` which is locally Noetherian — meaning that
`AlgebraicGeometry.IsLocallyNoetherian` holds étale-locally on it in the sense of Tag 03E6 —
is a locally Noetherian topological space, and it is a Noetherian topological space as soon
as the algebraic space is in addition quasi-compact.

A chart witnessing local Noetherianity is a scheme whose topological space is locally
Noetherian by Tag 01OZ; its point space is homeomorphic to that scheme by clause (1) of Tag
03BX, and the chart is a continuous open surjection on points, so local Noetherianity passes
to the point space of the algebraic space by Tag 04Z8 (2). Quasi-compactness of the point
space comes from Tag 03E4, and a quasi-compact locally Noetherian space is Noetherian by
Tag 04ZB.

## Main results

* `AlgebraicGeometry.Space.isLocallyNoetherianSpace_of_isLocallyNoetherian` and
  `AlgebraicGeometry.Space.noetherianSpace_of_isQuasiCompact_of_isLocallyNoetherian` are
  parts (1) and (2) of **Stacks 04ZF**.

## Implementation notes

`AlgebraicGeometry.Space.pointTopology` is a plain definition rather than an instance and is
made a local instance here.

## References

* [Stacks Project, Tag 04ZF](https://stacks.math.columbia.edu/tag/04ZF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

include hF

/-- **Stacks 04ZF, part (1).** The space of points of a locally Noetherian algebraic space
over `S` is a locally Noetherian topological space. -/
@[stacks 04ZF "part (1)"]
theorem isLocallyNoetherianSpace_of_isLocallyNoetherian
    (hN : HasEtaleLocalProperty B S hS F (fun X : Scheme.{u} ↦ IsLocallyNoetherian X)) :
    IsLocallyNoetherianSpace (points B S hS F) := by
  obtain ⟨U, f, hsurj, hetale, hloc⟩ := hN
  have hUloc : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) := hloc
  have hU : IsLocallyNoetherianSpace (points B S hS (yoneda.obj U)) :=
    (_root_.AlgebraicGeometry.isLocallyNoetherianSpace_of_isLocallyNoetherian
      ((BigFppfOver.toScheme B S hS).obj U)).of_homeomorph
      (schemePointsHomeomorph B S hS U).symm
  exact hU.of_isOpenMap_surjective _ (continuous_pointsMap B S hS f)
    (isOpenMap_pointsMap_of_etale B S hS hF U f hetale)
    ((surjective_iff_surjective_pointsMap B S hS F hF U f).mp hsurj)

/-- **Stacks 04ZF, part (2).** The space of points of a quasi-compact locally Noetherian
algebraic space over `S` is a Noetherian topological space. -/
@[stacks 04ZF "part (2)"]
theorem noetherianSpace_of_isQuasiCompact_of_isLocallyNoetherian
    (hqc : IsQuasiCompactSpace B S hS F)
    (hN : HasEtaleLocalProperty B S hS F (fun X : Scheme.{u} ↦ IsLocallyNoetherian X)) :
    NoetherianSpace (points B S hS F) :=
  have : CompactSpace (points B S hS F) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS F hF).mp hqc
  noetherianSpace_of_isLocallyNoetherianSpace _
    (isLocallyNoetherianSpace_of_isLocallyNoetherian B S hS F hF hN)

end AlgebraicGeometry.Space

end
