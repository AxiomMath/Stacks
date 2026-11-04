module

public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.Curves.PinchedProjectiveLine.CoordinateRing
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineFiniteType
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineIntegral
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.Topology.Dimension.LocalKrullDim

/-!
# The projective line over a field is a proper curve

The projective line over a field has Krull dimension one, and is therefore a curve over that
field, and in fact a proper variety: integrality is
`AlgebraicGeometry.projectiveLine_isIntegral`, separatedness, quasi-compactness and finite type
are in the two neighbouring files, and properness is
`AlgebraicGeometry.projectiveLine_isProper`.

The dimension is computed chart by chart. The Krull dimension of a space is the supremum of its
local Krull dimensions (Stacks 0B7I), and the local Krull dimension at a point only depends on
an open neighbourhood of it; so the supremum over the projective line equals the supremum over
either chart, which is the Krull dimension of `Spec k[X]`, that is the Krull dimension of the
ring `k[X]`, which is one.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_projectiveLine`: the projective line over a field has
  Krull dimension one.
* `AlgebraicGeometry.projectiveLine_isCurve`: the projective line over a field is a curve.
* `AlgebraicGeometry.projectiveLine_isProperVariety`: the projective line over a field is a
  proper variety.
* `AlgebraicGeometry.projectiveLine_isLocallyNoetherian` and
  `AlgebraicGeometry.projectiveLineXChart_isDominant`: the two instances the order of vanishing
  on the projective line needs.

## Implementation notes

The upper bound and the lower bound both go through
`TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim`, so nothing has to be said about
chains of irreducible closed subsets of the glued space directly: the only geometric input is
that the two charts are open immersions from `Spec k[X]` and are jointly surjective.

## References

* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
* [Stacks Project, Tag 0A23](https://stacks.math.columbia.edu/tag/0A23)
* [Stacks Project, Tag 0B7I](https://stacks.math.columbia.edu/tag/0B7I)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k]

/-- The local Krull dimension of the projective line at a point of a chart is the local Krull
dimension of the affine line at the corresponding point, because a chart is an open
immersion. -/
theorem localKrullDim_projectiveLine_chart
    (c : Spec (.of (Polynomial k)) ⟶ projectiveLine k) [IsOpenImmersion c]
    (y : Spec (.of (Polynomial k))) :
    localKrullDim (projectiveLine k) (c.base y) =
      localKrullDim (Spec (.of (Polynomial k))) y := by
  rw [← topologicalKrullDimAt_eq_localKrullDim, ← topologicalKrullDimAt_eq_localKrullDim]
  exact c.isOpenEmbedding.topologicalKrullDimAt_eq y

/-- **The projective line over a field has Krull dimension one.** Both bounds come from the
description of the Krull dimension as the supremum of the local Krull dimensions: every point
lies in a chart, and on a chart the local dimensions are those of the affine line. -/
theorem topologicalKrullDim_projectiveLine : topologicalKrullDim (projectiveLine k) = 1 := by
  rw [topologicalKrullDim_eq_iSup_localKrullDim, ← topologicalKrullDim_spec_polynomial k,
    topologicalKrullDim_eq_iSup_localKrullDim]
  refine le_antisymm (iSup_le fun x ↦ ?_) (iSup_le fun y ↦ ?_)
  · obtain ⟨⟨i⟩, y, rfl⟩ := (projectiveLineGluingData k).ι_jointly_surjective x
    cases i <;> exact (localKrullDim_projectiveLine_chart k _ y).trans_le (le_iSup _ y)
  · exact (localKrullDim_projectiveLine_chart k (projectiveLineXChart k) y).ge.trans
      (le_iSup _ _)

/-- The projective line over a field is locally Noetherian, being of finite type over a
field. -/
instance projectiveLine_isLocallyNoetherian : IsLocallyNoetherian (projectiveLine k) :=
  LocallyOfFiniteType.isLocallyNoetherian (projectiveLine k ↘ Spec (.of k))

/-- The first chart of the projective line over a field is dominant, since it is dense. -/
instance projectiveLineXChart_isDominant : IsDominant (projectiveLineXChart k) :=
  ⟨denseRange_projectiveLineXChart k⟩

/-- The projective line over a field is a variety over that field. -/
instance projectiveLine_isVariety : IsVariety k (projectiveLine k ↘ Spec (.of k)) where

/-- **The projective line over a field is a curve**: a variety of Krull dimension one. -/
instance projectiveLine_isCurve : IsCurve k (projectiveLine k ↘ Spec (.of k)) where
  topologicalKrullDim_eq_one := topologicalKrullDim_projectiveLine k

/-- **The projective line over a field is a proper variety.** This is the hypothesis a target
of a rational map from a normal curve has to satisfy in Stacks 0BXZ. -/
instance projectiveLine_isProperVariety :
    IsProperVariety k (projectiveLine k ↘ Spec (.of k)) where

end AlgebraicGeometry

end
