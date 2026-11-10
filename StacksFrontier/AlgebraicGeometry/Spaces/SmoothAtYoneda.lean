module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Smooth

/-!
# Smoothness at a point of a morphism of schemes read as algebraic spaces

For a morphism `g : U ⟶ V` of the big fppf site of `S` whose underlying morphism of schemes is
locally of finite presentation, the induced morphism of algebraic spaces `yoneda.map g` is smooth
at a point of `|U|` (Stacks 03ZC, part (2)) exactly when the morphism of schemes is smooth at the
corresponding scheme point, that is, exactly when that point lies in Mathlib's
`AlgebraicGeometry.Scheme.Hom.smoothLocus`.

Smoothness at a point of a morphism of algebraic spaces is the pointed-chart condition of Stacks
04NC for the germ property induced by smoothness (part (2) of Stacks 04RF); for a morphism of the
site that condition is read on the identity chart, where it is the germ condition at the point,
which for a morphism locally of finite presentation is membership of the smooth locus.

## Main results

* `AlgebraicGeometry.Space.isSmoothAt_yoneda_map_iff`

## References

* [Stacks Project, Tag 03ZC](https://stacks.math.columbia.edu/tag/03ZC)
* [Stacks Project, Tag 04NC](https://stacks.math.columbia.edu/tag/04NC)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- For a morphism of the site whose underlying morphism of schemes is locally of finite
presentation, the induced morphism of algebraic spaces is smooth at a point exactly when the
morphism of schemes is smooth at the corresponding scheme point. -/
theorem isSmoothAt_yoneda_map_iff {U V : BigFppfOver B S hS} (g : U ⟶ V)
    [LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map g)]
    (x : points B S hS (yoneda.obj U)) :
    IsSmoothAt B S hS (yoneda.map g) x ↔
      pointsToScheme B S hS U x ∈ ((BigFppfOver.toScheme B S hS).map g).smoothLocus := by
  rw [isSmoothAt_iff_holdsOnEveryEtaleChartAtPoint B S hS (isAlgebraicSpace_yoneda B S hS U)
      (isAlgebraicSpace_yoneda B S hS V),
    holdsOnEveryEtaleChartAtPoint_yoneda_map_iff B S hS _
      (MorphismOfGerms.hasRepresentativeWithProperty_isEtaleLocalOnSourceAndTarget _
        Smooth.isEtaleLocalOnSourceAndTarget) g x,
    ← smoothAt_iff_hasRepresentativeWithProperty]
  change Stacks.SmoothAtJacobian.Condition1 _ _ ↔ _
  exact Stacks.SmoothAtJacobian.condition1_iff_mem_smoothLocus _ _

end AlgebraicGeometry.Space

end
