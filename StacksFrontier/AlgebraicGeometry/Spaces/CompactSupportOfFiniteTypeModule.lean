module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperModuleSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology

/-!
# Quasi-compactness of the support of a finite type module

Let `F` be a quasi-coherent `𝒪_X`-module of finite type on an algebraic space `X` over `S`.
Its support (Stacks 04KA) is the set of points of its scheme theoretic support (Stacks 07U1), so
if that closed subspace is quasi-compact then the support is a compact subset of `|X|`.

## Main results

* `AlgebraicGeometry.Space.isCompact_supportOfSheaf_of_compactSpace`: the support of a
  quasi-coherent module of finite type whose scheme theoretic support is quasi-compact is a
  compact set of points.

## Implementation notes

The identification of the two is
`AlgebraicGeometry.Space.supportOfSheaf_eq_range_pointsMap_schemeTheoreticSupport`, part (4) of
Stacks 07U0, which asks only for quasi-coherence of the module and its finite type.  Given
that, the support is the image of a continuous map (Stacks 03BX clause (2),
`AlgebraicGeometry.Space.continuous_pointsMap`) out of a compact space.

`AlgebraicGeometry.Space.pointTopology` is not a global instance, so it is made a local one here;
a consumer of this statement has to do the same.

This is the hypothesis-handling step of the finite presentation clause of Stacks 083K — *"the
scheme theoretic support of `ℱ` is quasi-compact"* — in the form
`AlgebraicGeometry.Space.exists_affine_etale_chart_of_isCompact` consumes it, namely as
`IsCompact` of a set of points.

## References

* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 07U0](https://stacks.math.columbia.edu/tag/07U0)
* [Stacks Project, Tag 07U1](https://stacks.math.columbia.edu/tag/07U1)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- **The support of a quasi-coherent module of finite type with quasi-compact scheme theoretic
support is compact.**

The support is the image on points of the closed immersion of the scheme theoretic support, which
is continuous, and the source is compact by hypothesis. -/
theorem isCompact_supportOfSheaf_of_compactSpace (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (hFft : SheafOfModules.IsFiniteTypeOnSite F)
    (hcpt : CompactSpace (points B S hS (schemeTheoreticSupport B S hS X F).toFunctor)) :
    IsCompact (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F)) := by
  rw [supportOfSheaf_eq_range_pointsMap_schemeTheoreticSupport B S hS X F hF hFft]
  exact isCompact_range (continuous_pointsMap B S hS _)

end AlgebraicGeometry.Space

end
