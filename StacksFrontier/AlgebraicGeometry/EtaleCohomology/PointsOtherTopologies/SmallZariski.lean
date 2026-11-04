module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointsOtherTopologies.FiniteRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ZariskiLimits
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.SmallAffineDenseSubsite
public import StacksCore.Tactic.StacksAttribute

/-!
# Enough points for the small Zariski and small affine Zariski sites

The small affine Zariski site of a scheme — its affine open subschemes — has enough points,
because its covering families are standard Zariski coverings, which are finite, so Deligne's
criterion applies. The small Zariski site of the scheme then has enough points because the
small affine Zariski site is a dense subsite of it (Stacks 0F1B).

## Main results

* `AlgebraicGeometry.smallAffineZariski_hasConservativeFamily`: the small affine Zariski site
  `S_{affine, Zar}` has a conservative family of points.
* `AlgebraicGeometry.smallZariski_hasConservativeFamily`: the small Zariski site `S_Zar` has a
  conservative family of points.

## Implementation notes

The sites are relative to a chosen big Zariski site containing the base scheme. Enough points
is expressed by the existence of a conservative family of points, without requiring the family
to be small.

Fibre products in the small affine Zariski site exist because the base of a cospan is itself an
affine open: two affine opens of an affine scheme meet in an affine open. This is what lets
Deligne's criterion be applied to the affine site directly, as it is for the big affine sites,
rather than through a small model.

## References

* [Stacks Project, Tag 06VX](https://stacks.math.columbia.edu/tag/06VX)
* [Stacks Project, Tag 0F1B](https://stacks.math.columbia.edu/tag/0F1B)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks 06VX, small affine Zariski case.** The small affine Zariski site of a scheme has
enough points. -/
@[stacks 06VX "small_affine_zariski"]
public theorem smallAffineZariski_hasConservativeFamily
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (SmallAffineZariski.topology B S hS).HasConservativeFamily.{u + 1} :=
  Precoverage.hasConservativeFamily_toGrothendieck_of_finite.{u + 1, u, u + 1} _
    fun _ _ hR ↦ by
      obtain ⟨E, hEq, hE⟩ := (SmallAffineZariski.mem_precoverage_iff B S hS).mp hR
      exact ⟨E, hE.2.choose_spec.1, hEq⟩

/-- **Stacks 06VX, small Zariski case.** The small Zariski site of a scheme has enough
points. -/
@[stacks 06VX "small_zariski"]
public theorem smallZariski_hasConservativeFamily
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (SmallZariski.topology B S hS).HasConservativeFamily.{u + 1} := by
  have hSpec := SmallAffineZariski.inclusion_isSpecialCocontinuous B S hS
  let : (SmallAffineZariski.inclusion B S hS).IsCocontinuous
      (SmallAffineZariski.topology B S hS) (SmallZariski.topology B S hS) := hSpec.1
  let : (SmallAffineZariski.inclusion B S hS).IsDenseSubsite
      (SmallAffineZariski.topology B S hS) (SmallZariski.topology B S hS) := hSpec.2
  exact hasConservativeFamily_of_denseSubsite.{u + 1, u + 1, u + 1} _ _
    (SmallAffineZariski.inclusion B S hS) (smallAffineZariski_hasConservativeFamily B S hS)

end AlgebraicGeometry
