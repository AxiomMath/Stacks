module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Sites.Point.Map
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointsOtherTopologies.BigAffineSmooth
public import StacksFrontier.AlgebraicGeometry.Topologies.Smooth.AffineDenseSubsite
public import StacksCore.Tactic.StacksAttribute

/-!
# Enough points for the big smooth site

The big smooth site over a scheme has enough points, because the big affine smooth site is a
dense subsite of it and has enough points.

## Main results

* `AlgebraicGeometry.bigSmooth_hasConservativeFamily` states that the big smooth site has a
  conservative family of points.

## Implementation notes

The site is the size-bounded slice site over `S`. Enough points is expressed by the existence
of a conservative family of points, with no prescribed smallness condition on its indexing
family.

## References

* [Stacks Project, Tag 06VX](https://stacks.math.columbia.edu/tag/06VX)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **Stacks 06VX, big smooth case.** The big smooth site over `S` has enough
points. -/
@[stacks 06VX "big_smooth"]
public theorem bigSmooth_hasConservativeFamily
    (B : AlgebraicGeometry.BigSmoothSite.{u}) (S : Scheme.{u})
    (hS : S.size < B.cutoff) :
    (AlgebraicGeometry.BigSmoothOver.topology B S hS).HasConservativeFamily.{u + 1} := by
  obtain ⟨_, _⟩ := BigAffineSmooth.inclusion_isSpecialCocontinuous B S hS
  exact hasConservativeFamily_of_denseSubsite.{u + 1, u + 1, u + 1} _ _
    (BigAffineSmooth.inclusion B S hS) (bigAffineSmooth_hasConservativeFamily B S hS)

end AlgebraicGeometry
