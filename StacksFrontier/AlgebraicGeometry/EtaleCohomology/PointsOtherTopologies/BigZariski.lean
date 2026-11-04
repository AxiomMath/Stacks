module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointsOtherTopologies.FiniteRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.AffineZariskiDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ZariskiLimits
public import StacksCore.Tactic.StacksAttribute

/-!
# Enough points for the big Zariski and big affine Zariski sites

The big affine Zariski site over a scheme has enough points, because its covering families are
standard Zariski coverings, which are finite, so Deligne's criterion applies. The big Zariski
site over the scheme then has enough points because the big affine Zariski site is a dense
subsite of it (Stacks 020W).

## Main results

* `AlgebraicGeometry.bigAffineZariski_hasConservativeFamily`: the big affine Zariski site
  `(Aff/S)_Zar` has a conservative family of points.
* `AlgebraicGeometry.bigZariski_hasConservativeFamily`: the big Zariski site `(Sch/S)_Zar` has
  a conservative family of points.

## Implementation notes

The sites are relative to a chosen big Zariski site containing the base scheme. Enough points
is expressed by the existence of a conservative family of points, without requiring the family
to be small.

## References

* [Stacks Project, Tag 06VX](https://stacks.math.columbia.edu/tag/06VX)
* [Stacks Project, Tag 020W](https://stacks.math.columbia.edu/tag/020W)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks 06VX, big affine Zariski case.** The big affine Zariski site over a scheme has
enough points. -/
@[stacks 06VX "big_affine_zariski"]
public theorem bigAffineZariski_hasConservativeFamily
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (BigAffineZariski.topology B S hS).HasConservativeFamily.{u + 1} :=
  Precoverage.hasConservativeFamily_toGrothendieck_of_finite.{u + 1, u, u + 1} _
    fun _ _ hR ↦ by
      obtain ⟨E, hEq, hE⟩ := (BigAffineZariski.mem_precoverage_iff B S hS).mp hR
      exact ⟨E, hE.2.choose_spec.1, hEq⟩

/-- **Stacks 06VX, big Zariski case.** The big Zariski site over a scheme has enough
points. -/
@[stacks 06VX "big_zariski"]
public theorem bigZariski_hasConservativeFamily
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (BigZariskiOver.topology B S hS).HasConservativeFamily.{u + 1} := by
  have hSpec := BigAffineZariski.inclusion_isSpecialCocontinuous B S hS
  let : (BigAffineZariski.inclusion B S hS).IsCocontinuous
      (BigAffineZariski.topology B S hS) (BigZariskiOver.topology B S hS) := hSpec.1
  let : (BigAffineZariski.inclusion B S hS).IsDenseSubsite
      (BigAffineZariski.topology B S hS) (BigZariskiOver.topology B S hS) := hSpec.2
  exact hasConservativeFamily_of_denseSubsite.{u + 1, u + 1, u + 1} _ _
    (BigAffineZariski.inclusion B S hS) (bigAffineZariski_hasConservativeFamily B S hS)

end AlgebraicGeometry
