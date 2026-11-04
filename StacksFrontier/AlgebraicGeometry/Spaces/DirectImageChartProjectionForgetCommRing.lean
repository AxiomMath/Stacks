module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionRing
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionSquare

/-!
# The ring form of the chart projections, on the sheaf of sets of the commutative structure sheaf

`AlgebraicGeometry.Space.directImageChartProjectionRingHom` reads a section of a direct image of
the structure sheaf at a chart on the sheaf of sets underlying the structure sheaf of *rings*;
the chart computations of `StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionSquare`
are stated on the sheaf of sets underlying the structure sheaf of *commutative* rings.  This file
records that the two readings agree.

## Main results

* `AlgebraicGeometry.Space.directImageChartProjectionRingHom_apply_forgetCommRing`.

## Implementation notes

The imports of this file are those of
`StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionSquare` together with the ring
form of the chart projections, and nothing that provides a second instance of the sheaf
condition along the forgetful functors of `CommRingCat` and `RingCat` on a small étale site, so
that the sheaf of sets in the statement is the one of the lemmas of that file; across two
different instances the comparison does not finish in the default budget.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS}

/-- The chart projection of a section of a direct-image algebra, read on the sheaf of sets
underlying the structure sheaf of commutative rings. -/
theorem directImageChartProjectionRingHom_apply_forgetCommRing {A : AlgebraicSpaces B S hS}
    {p : A ⟶ X} (V : SmallEtale B S hS X.1)
    (j : StructuredArrow (op (chartBaseChange B S hS p V)) (comparisonFunctor B S hS A).op)
    (x : ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS p).toToposHom).obj
          (smallEtaleRingedTopos B S hS A).O).obj.obj (op V)) :
    (directImageChartProjectionRingHom B S hS p V j).hom x =
      (directImageChartProjection B S hS p V j).app
        ((sheafCompose _ (forget CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS A).O) x :=
  rfl

end AlgebraicGeometry.Space

end
