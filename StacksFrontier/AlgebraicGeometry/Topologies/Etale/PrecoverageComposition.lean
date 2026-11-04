module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Precoverage

/-!
# The precoverage of a big étale site is stable under composition

The precoverage of a big étale site is the étale precoverage of schemes comapped along the
inclusion of the site, and the étale precoverage of schemes is stable under composition
(`AlgebraicGeometry.Scheme.etalePrecoverage_isStableUnderComposition`, on the base).

## Main results

* `AlgebraicGeometry.bigEtalePrecoverage_isStableUnderComposition`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The precoverage of a big étale site is stable under composition: it is the étale precoverage
of schemes comapped along the inclusion of the site. -/
public instance bigEtalePrecoverage_isStableUnderComposition
    (B : AlgebraicGeometry.BigEtaleSite.{u}) :
    B.precoverage.IsStableUnderComposition := by
  have := Scheme.etalePrecoverage_isStableUnderComposition.{u}
  rw [bigEtalePrecoverage_eq_comap B]
  infer_instance

end AlgebraicGeometry
