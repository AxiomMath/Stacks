module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointsOtherTopologies.FiniteRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.AffineSyntomicDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.ChosenFlatSiteSheaves
public import StacksCore.Tactic.StacksAttribute

/-!
# Enough points for the big syntomic and big affine syntomic sites

The big affine syntomic site over a scheme has enough points, because its covering families are
standard syntomic coverings, which are finite, so Deligne's criterion applies. The big syntomic
site over the scheme then has enough points because the big affine syntomic site is a dense
subsite of it (Stacks 06VD).

## Main results

* `AlgebraicGeometry.bigAffineSyntomic_hasConservativeFamily`: the big affine syntomic site
  `(Aff/S)_syntomic` has a conservative family of points.
* `AlgebraicGeometry.bigSyntomic_hasConservativeFamily`: the big syntomic site
  `(Sch/S)_syntomic` has a conservative family of points.

## Implementation notes

The sites are relative to a chosen big syntomic site containing the base scheme. Enough points
is expressed by the existence of a conservative family of points, without requiring the family
to be small.

## References

* [Stacks Project, Tag 06VX](https://stacks.math.columbia.edu/tag/06VX)
* [Stacks Project, Tag 06VD](https://stacks.math.columbia.edu/tag/06VD)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks 06VX, big affine syntomic case.** The big affine syntomic site over a scheme has
enough points. -/
@[stacks 06VX "big_affine_syntomic"]
public theorem bigAffineSyntomic_hasConservativeFamily
    (B : BigSyntomicSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (BigAffineSyntomic.topology B S hS).HasConservativeFamily.{u + 1} :=
  Precoverage.hasConservativeFamily_toGrothendieck_of_finite.{u + 1, u, u + 1} _
    fun _ _ hR ↦ by
      obtain ⟨E, hEq, -, hStd⟩ := hR
      exact ⟨E, hStd.finite_index, hEq⟩

/-- **Stacks 06VX, big syntomic case.** The big syntomic site over a scheme has enough
points. -/
@[stacks 06VX "big_syntomic"]
public theorem bigSyntomic_hasConservativeFamily
    (B : BigSyntomicSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (BigSyntomicOver.topology B S hS).HasConservativeFamily.{u + 1} := by
  have hSpec := BigAffineSyntomic.inclusion_isSpecialCocontinuous B S hS
  let : (BigAffineSyntomic.inclusion B S hS).IsCocontinuous
      (BigAffineSyntomic.topology B S hS) (BigSyntomicOver.topology B S hS) := hSpec.1
  let : (BigAffineSyntomic.inclusion B S hS).IsDenseSubsite
      (BigAffineSyntomic.topology B S hS) (BigSyntomicOver.topology B S hS) := hSpec.2
  exact hasConservativeFamily_of_denseSubsite.{u + 1, u + 1, u + 1} _ _
    (BigAffineSyntomic.inclusion B S hS) (bigAffineSyntomic_hasConservativeFamily B S hS)

end AlgebraicGeometry
