module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sieves.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointsOtherTopologies.FiniteRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksCore.Tactic.StacksAttribute

/-!
# Enough points for the big affine étale site

The big affine étale site over a scheme has enough points: its covering families may be taken
finite, so the criterion for the existence of points applies directly.

## Main results

* `AlgebraicGeometry.bigAffineEtale_hasConservativeFamily` states that the big affine étale site
  has enough points.

## Implementation notes

The site is relative to a chosen big étale site containing the base scheme, as in the
construction of the big affine étale site. Enough points means
`CategoryTheory.GrothendieckTopology.HasConservativeFamily`; the family of points is not
required to be small.

## References

* [Stacks Project, Tag 06VX](https://stacks.math.columbia.edu/tag/06VX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

universe u₁ v₁ w₁

/-- **Stacks 06VX, big affine étale case.** The big affine étale site over a
scheme has enough points. -/
@[stacks 06VX "big_affine_etale"]
public theorem bigAffineEtale_hasConservativeFamily
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    GrothendieckTopology.HasConservativeFamily.{u + 1}
      (AlgebraicGeometry.BigAffineEtale.topology B S hS) :=
  Precoverage.hasConservativeFamily_toGrothendieck_of_finite.{u + 1, u, u + 1} _
    fun _ _ hR ↦ by
      obtain ⟨E, hEq, hCov⟩ := (AlgebraicGeometry.BigAffineEtale.mem_precoverage_iff B S hS).mp hR
      exact ⟨E, hCov.2.2.1, hEq⟩

end AlgebraicGeometry
