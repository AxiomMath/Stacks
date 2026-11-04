module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth

/-!
# Families of curves with finite singular locus (Stacks 0DZW)

Stacks 0DZW produces the open substack `Curves⁺ ⊂ Curves` of families of curves whose singular
locus is finite over the base. Its defining condition, which is what this file states, is the
one the proof of 0DZW uses: the locus of points of the total space where the structure morphism
is not smooth, endowed with its reduced induced closed subspace structure (Stacks 047X), is
finite over the base.

That subspace is specified here by its properties rather than constructed: a closed subspace
whose points are exactly the non-smooth points, which is reduced and finite over the base. Its
uniqueness is Stacks 03IQ, so the existential form loses nothing, and it lets the condition be
stated before the non-smooth locus has been shown to be closed. It is closed, and the subspace
is constructed from it, in
`StacksFrontier/AlgebraicGeometry/Quot/CurvesPlusOpenLocus.lean`, where
`AlgebraicGeometry.CurveFamily.isFiniteNonSmoothLocus_iff_isFinite_singularSubspace` discharges
the existential against that one subspace.

## Main definitions

* `AlgebraicGeometry.IsFiniteNonSmoothLocus`: the defining condition of `Curves⁺`.
* `AlgebraicGeometry.CurvesPlus`: **Stacks 0DZW**, the strictly full subcategory `Curves⁺` of
  families of curves cut out by that condition.

## Implementation notes

`CurvesPlus` is an abbreviation for an `ObjectProperty.FullSubcategory`, so the inclusion
functor, its fullness and faithfulness, and the induced category structure all come from
Mathlib rather than being restated.

Openness is not proved here. The singular locus is shown to be closed, the "any/some closed
subspace structure" clause and the open locus in the base are proved in
`StacksFrontier/AlgebraicGeometry/Quot/CurvesPlusOpenLocus.lean`, and the open substack together
with parts (1) and (2) of Stacks 0DZW is assembled in
`StacksFrontier/AlgebraicGeometry/Quot/CurvesPlusOpenSubstack.lean`.

## References

* [Stacks Project, Tag 0DZW](https://stacks.math.columbia.edu/tag/0DZW)
* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
* [Stacks Project, Tag 047X](https://stacks.math.columbia.edu/tag/047X)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The reduced closed subspace supported on the non-smooth locus of a family of curves is
finite over the base: there is a closed subspace `Z` of the total space whose set of points is
exactly the set of points at which the structure morphism fails to be smooth, which is reduced,
and which is finite over the base. -/
abbrev IsFiniteNonSmoothLocus (X : CurveFamily B hZ) : Prop :=
  ∃ Z : Subfunctor X.total.1,
    Space.IsClosedSubspace B integerBase hZ Z ∧
    Set.range (Space.pointsMap B integerBase hZ Z.toFunctor Z.ι) =
      {x : Space.points B integerBase hZ X.total.1 |
        ¬ Space.IsSmoothAt B integerBase hZ X.toBase.hom x} ∧
    Space.HasEtaleLocalProperty B integerBase hZ Z.toFunctor
      (fun Y : Scheme.{u} => IsReduced Y) ∧
    Space.IsFinite B integerBase hZ (Z.ι ≫ X.toBase.hom)

/-- **Stacks 0DZW.** The substack `Curves⁺`: the strictly full subcategory of families of
curves whose reduced non-smooth locus is finite over the base. -/
@[stacks 0DZW "the_substack_curves"]
abbrev CurvesPlus :=
  (show ObjectProperty (CurveFamily B hZ) from IsFiniteNonSmoothLocus B hZ).FullSubcategory

end AlgebraicGeometry

end
