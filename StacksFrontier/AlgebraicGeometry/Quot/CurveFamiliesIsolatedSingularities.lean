module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth

/-!
# Families of curves with isolated singularities (Stacks 0DZW)

A family of curves `X ⟶ S` has *isolated singularities* when the non-smooth locus of its
structure morphism, endowed with its reduced closed subspace structure, is finite over the
base. The families with isolated singularities form a strictly full subcategory
`Curves⁺ ⊂ Curves`, and that subcategory is the substack of Stacks 0DZW.

## Main definitions

* `AlgebraicGeometry.hasFiniteNonSmoothLocus`: the property of a family of curves that the
  reduced closed subspace supported on the non-smooth locus of its structure morphism is
  finite over the base.
* `AlgebraicGeometry.CurvesWithFiniteNonSmoothLocus`: **Stacks 0DZW**, the strictly full
  subcategory `Curves⁺` it cuts out.
* `AlgebraicGeometry.curvesWithFiniteNonSmoothLocusProjection`: its projection to the big
  fppf site, which is how `Curves⁺` is regarded as a category over that site.

## Implementation notes

The reduced closed subspace supported on the non-smooth locus is specified by its inclusion
rather than constructed: the condition asks for a subfunctor of the total space which is a
closed subspace (Stacks 02YU, part (4)), whose set of points is exactly the non-smooth locus
of the structure morphism, which is reduced as an étale-local property of schemes (Stacks
03E6), and whose composite inclusion to the base is finite (Stacks 03ZP). Such a subspace is
unique when it exists, by Stacks 03IQ in the form
`AlgebraicGeometry.Space.eq_reducedClosedSubspace`, so this existential form is the
"any/some closed subspace structure" of the source; stating it existentially avoids carrying
a proof that the non-smooth locus is closed, which is not part of the condition.

Smoothness at a point is `AlgebraicGeometry.Space.IsSmoothAt` of Stacks 03ZC, part (2), so
the non-smooth locus is the complement of the set where that holds, taken inside the set of
points `AlgebraicGeometry.Space.points` of Stacks 03BU.

Being a full subcategory, `Curves⁺` inherits the full-subcategory inclusion and its fullness
and faithfulness instances, which is what a consumer needs of the inclusion
`Curves⁺ ⟶ Curves`.

## References

* [Stacks Project, Tag 0DZW](https://stacks.math.columbia.edu/tag/0DZW)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The property of a family of curves that the reduced closed subspace of its total space
supported on the non-smooth locus of its structure morphism is finite over the base. -/
abbrev hasFiniteNonSmoothLocus : ObjectProperty (CurveFamily B hZ) := fun X ↦
  ∃ Z : Subfunctor X.total.obj,
    Space.IsClosedSubspace B integerBase hZ Z ∧
    Set.range (Space.pointsMap B integerBase hZ Z.toFunctor Z.ι) =
      {x : Space.points B integerBase hZ X.total.obj |
        ¬ Space.IsSmoothAt B integerBase hZ X.toBase.hom x} ∧
    Space.HasEtaleLocalProperty B integerBase hZ Z.toFunctor
      (fun Y : Scheme.{u} ↦ IsReduced Y) ∧
    Space.IsFinite B integerBase hZ (Z.ι ≫ X.toBase.hom)

/-- **Stacks 0DZW.** The strictly full subcategory `Curves⁺ ⊂ Curves` of the families of
curves whose non-smooth locus, with its reduced closed subspace structure, is finite over
the base. -/
@[stacks 0DZW "the substack of curves with isolated singularities"]
abbrev CurvesWithFiniteNonSmoothLocus := (hasFiniteNonSmoothLocus B hZ).FullSubcategory

/-- **Stacks 0DZW.** The projection taking a family of curves with isolated singularities to
its base scheme, which is how `Curves⁺` is regarded as a category over the big fppf site. -/
@[stacks 0DZW "the projection of the substack"]
abbrev curvesWithFiniteNonSmoothLocusProjection :
    CurvesWithFiniteNonSmoothLocus B hZ ⥤ B.Schemes :=
  (hasFiniteNonSmoothLocus B hZ).ι ⋙ curvesProjection B hZ

end AlgebraicGeometry

end
