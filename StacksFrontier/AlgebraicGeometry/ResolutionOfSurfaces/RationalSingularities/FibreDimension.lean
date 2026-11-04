module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.Basic
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.HigherDirectImageBoundedness

/-!
# The fibres of a normal modification of a rational surface singularity are at most curves

In Situation [Stacks, Tag 0B4W] the base `Spec(A)` is the spectrum of a two-dimensional local
normal Nagata domain and `f : X ⟶ Spec(A)` is a modification with `X` normal. Every fibre of `f`
then has dimension at most one.

## Main definitions

* `AlgebraicGeometry.RationalSingularitySituation.toVanishingSituation`: Situation
  [Stacks, Tag 0B4W] is in particular Situation [Stacks, Tag 0AX8].

## Main results

* `AlgebraicGeometry.RationalSingularitySituation.topologicalKrullDim_fiber_le_one`: every fibre of
  the modification has dimension at most one.

## References

* [Stacks Project, Tag 0B4W](https://stacks.math.columbia.edu/tag/0B4W)
* [Stacks Project, Tag 0AX8](https://stacks.math.columbia.edu/tag/0AX8)
* [Stacks Project, Tag 0B2K](https://stacks.math.columbia.edu/tag/0B2K)
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.RationalSingularitySituation

variable (S : RationalSingularitySituation.{u})

/-- Situation [Stacks, Tag 0B4W] is in particular Situation [Stacks, Tag 0AX8]: a local normal
Nagata domain of dimension two is a two-dimensional Noetherian normal local domain, and the
remaining data, the modification and the enumeration of the components of its special fibre, is the
same in both situations. -/
abbrev toVanishingSituation : VanishingSituation.{u} where
  A := S.A
  dimension_two := S.dimension_two
  X := S.X
  f := S.f
  modification := S.modification
  numberOfComponents := S.numberOfComponents
  components := S.components

/-- Situation [Stacks, Tag 0B4W] read as the situation of [Stacks, Tag 0AXF] with the identity as
the second modification. -/
abbrev toTwoModifications : SemistableReduction.TwoModifications.{u} where
  situation := S.toVanishingSituation
  X' := S.X
  g := 𝟙 S.X
  modification' := by simpa using S.modification
  normal := S.normalSource

/-- Every fibre of the modification has dimension at most one. -/
theorem topologicalKrullDim_fiber_le_one (y : S.base) :
    topologicalKrullDim (S.f.fiber y) ≤ 1 := by
  have h : topologicalKrullDim ((𝟙 S.X ≫ S.f).fiber y) ≤ 1 :=
    S.toTwoModifications.topologicalKrullDim_fiber_f'_le_one y
  rwa [Category.id_comp] at h

/-- Every fibre of the modification has dimension at most one, with the bound written as the cast
of `(1 : ℕ)`. -/
theorem topologicalKrullDim_fiber_le_natCast_one (y : S.base) :
    topologicalKrullDim (S.f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
  simpa using S.topologicalKrullDim_fiber_le_one y

end AlgebraicGeometry.RationalSingularitySituation

end

end
