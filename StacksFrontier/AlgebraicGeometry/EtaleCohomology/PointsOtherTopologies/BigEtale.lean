module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Sites.Point.Map
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointsOtherTopologies.BigAffineEtale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.AffineDenseSubsite
public import StacksCore.Tactic.StacksAttribute

/-!
# Enough points for the big étale site

The big étale site over a scheme has enough points, because the big affine étale site is a
dense subsite of it and has enough points.

## Main results

* `AlgebraicGeometry.bigEtale_hasConservativeFamily` states that the big étale site has a
  conservative family of points.

## Implementation notes

The site is relative to a chosen big étale site containing the base scheme, as in the
construction of the big étale site over `S`. A conservative family is not required to be small
in a prescribed universe.

## References

* [Stacks Project, Tag 06VX](https://stacks.math.columbia.edu/tag/06VX)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **Stacks 06VX, big étale case.** The big étale site over a scheme has
enough points. -/
@[stacks 06VX "big_etale"]
public theorem bigEtale_hasConservativeFamily
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    GrothendieckTopology.HasConservativeFamily.{u + 1}
      (AlgebraicGeometry.BigEtaleOver.topology B S hS) := by
  obtain ⟨_, _⟩ := BigAffineEtale.inclusion_isSpecialCocontinuous B S hS
  exact hasConservativeFamily_of_denseSubsite _ _ (BigAffineEtale.inclusion B S hS)
    (bigAffineEtale_hasConservativeFamily B S hS)

end AlgebraicGeometry
