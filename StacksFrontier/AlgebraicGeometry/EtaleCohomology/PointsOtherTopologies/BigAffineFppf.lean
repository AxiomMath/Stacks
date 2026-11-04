module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointsOtherTopologies.FiniteRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.BigSite
public import StacksCore.Tactic.StacksAttribute

/-!
# Enough points for the big affine fppf site

The big affine fppf site over a scheme has enough points: its covering families may be taken
finite, so the criterion for the existence of points applies directly.

## Main results

* `AlgebraicGeometry.bigAffineFppf_hasConservativeFamily` states that the big affine fppf site
  has enough points.

## Implementation notes

The site is relative to a chosen big fppf site containing the base scheme. Enough points is
expressed by the existence of a conservative family of points, without requiring the family to
be small.

## References

* [Stacks Project, Tag 06VX](https://stacks.math.columbia.edu/tag/06VX)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

universe u₁ v₁ w₁

/-- **Stacks 06VX, big affine fppf case.** The big affine fppf site over a
scheme has enough points. -/
@[stacks 06VX "big_affine_fppf"]
public theorem bigAffineFppf_hasConservativeFamily
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (AlgebraicGeometry.BigAffineFppf.topology B S hS).HasConservativeFamily.{u + 1} :=
  Precoverage.hasConservativeFamily_toGrothendieck_of_finite.{u + 1, u, u + 1} _
    fun _ _ hR ↦ by
      obtain ⟨E, hEq, hCov⟩ := (AlgebraicGeometry.BigAffineFppf.mem_precoverage_iff B S hS).mp hR
      exact ⟨E, hCov.2.finite_index, hEq⟩

end AlgebraicGeometry
