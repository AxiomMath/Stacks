module

public import Mathlib.CategoryTheory.Sites.Point.Map
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointsOtherTopologies.BigAffineFppf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Equivalence
public import StacksCore.Tactic.StacksAttribute

/-!
# Enough points for the big fppf site

The big fppf site over a scheme has enough points, because the big affine fppf site is a dense
subsite of it and has enough points.

## Main results

* `AlgebraicGeometry.bigFppf_hasConservativeFamily` states that the big fppf site has a
  conservative family of points.

## Implementation notes

The site is relative to a chosen big fppf site containing the base scheme. Enough points means
that there is a conservative family of points, without requiring a small family in a prescribed
universe.

## References

* [Stacks Project, Tag 06VX](https://stacks.math.columbia.edu/tag/06VX)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **Stacks 06VX, big fppf case.** The big fppf site over a scheme has
enough points. -/
@[stacks 06VX "big_fppf"]
public theorem bigFppf_hasConservativeFamily
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (AlgebraicGeometry.BigFppfOver.topology B S hS).HasConservativeFamily.{u + 1} :=
  hasConservativeFamily_of_denseSubsite.{u + 1, u + 1, u + 1}
    (AlgebraicGeometry.BigAffineFppf.topology B S hS)
    (AlgebraicGeometry.BigFppfOver.topology B S hS)
    (AlgebraicGeometry.BigAffineFppf.inclusion B S hS)
    (AlgebraicGeometry.bigAffineFppf_hasConservativeFamily B S hS)

end AlgebraicGeometry
