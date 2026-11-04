module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The small étale site has enough affine objects

Every object `T` of the small étale site `AlgebraicGeometry.SmallEtale B S hS` of a scheme `S`
carries a covering family, indexed in the universe of the homs of the site, by objects whose
underlying scheme is affine.

## Main results

* `AlgebraicGeometry.SmallEtale.hasEnoughObjects_isAffine`: the small étale site of `S` has
  enough affine objects, for the object property `AlgebraicGeometry.SmallEtale.IsAffine`.

## References

* [Stacks Project, Tag 090L](https://stacks.math.columbia.edu/tag/090L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The small étale site of `S` has enough affine objects: every object `T` carries a covering
family, indexed in the universe of the homs of the site, by objects whose underlying scheme is
affine, namely the affine opens of `T` lying over an affine open of `S`. -/
@[sga "4 VI 1.22.1" "partial", sga "4 VII 3.1" "special case"]
public theorem SmallEtale.hasEnoughObjects_isAffine :
    (SmallEtale.topology B S hS).HasEnoughObjects (SmallEtale.IsAffine B S hS) := by
  intro T
  refine ⟨_,
    ((SmallEtale.affineSubordinateCover B S hS T).reindex Equiv.ulift.symm).X,
    ((SmallEtale.affineSubordinateCover B S hS T).reindex Equiv.ulift.symm).f, ?_,
    fun i => i.1.2⟩
  rw [show Sieve.ofArrows _ _ = (SmallEtale.affineSubordinateCover B S hS T).sieve₀ from
    congrArg Sieve.generate
      ((SmallEtale.affineSubordinateCover B S hS T).presieve₀_reindex Equiv.ulift.symm)]
  exact SmallEtale.mem_topology_sieve₀_affineSubordinateCover B S hS T

end AlgebraicGeometry

end
