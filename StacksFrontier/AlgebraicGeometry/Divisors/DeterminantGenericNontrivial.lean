module

public import StacksFrontier.AlgebraicGeometry.Divisors.DeterminantGenericRank
public import StacksFrontier.AlgebraicGeometry.Divisors.DeterminantNonzero

/-!
# The determinant of a module of generic rank `r` is nontrivial at the generic point

`AlgebraicGeometry.Scheme.Modules.detMap_ne_zero_of_surjective_of_ker_le_torsion` needs one
point at which the stalk of the determinant of `F` is nontrivial. On an integral scheme the
generic point is such a point as soon as `F` is finite locally free of rank `r` over some
nonempty open: the stalk there is an `r`-dimensional vector space over the function field, its
top exterior power is one-dimensional, and a one-dimensional space is reflexive and nonzero, so
its double dual is nonzero too.

This is the hypothesis `Nontrivial (modStalk (reflexiveHull (exteriorPower F r)) x)` of
`AlgebraicGeometry.Scheme.Modules.detMap_ne_zero_of_surjective_of_ker_le_torsion`, discharged at
`x = η`; `StacksFrontier/AlgebraicGeometry/Divisors/DeterminantNonzero.lean` records in its
implementation notes that this identification of the stalk with `K ^ r` was what the library
lacked.

## Main results

* `AlgebraicGeometry.Scheme.Modules.nontrivial_dual_dual_exteriorPower_stalk_genericPoint`: the
  double dual of the top exterior power of the stalk at the generic point is nontrivial.
* `AlgebraicGeometry.Scheme.Modules.nontrivial_modStalk_det_genericPoint`: **the stalk of the
  determinant of `F` at the generic point is nontrivial.**

## Implementation notes

**Reflexivity, not a dimension count on the double dual.** `Module.evalEquiv` identifies a
finite-dimensional vector space with its double dual, so nontriviality transports along an
equivalence and the dimension of the dual is never needed. The dimension of the exterior power
itself is `Nat.choose r r = 1` by `exteriorPower.finrank_eq`, which needs the stalk to be a
finite free module; finiteness comes from the trivialization over the nonempty open, freeness
from the base being a field.

**No `@[stacks]` attribute.** This is a step of the proof of Tag 0B3T, not one of its
assertions.

## References

* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.SheafOfModules.SheafHomStalk

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- **The double dual of the top exterior power of the stalk at the generic point is
nontrivial**, for a module which is finite locally free of rank `r` over a nonempty open of an
integral scheme. The stalk is `r`-dimensional over the function field, so its `r`-th exterior
power is one-dimensional, hence nonzero and reflexive. -/
theorem nontrivial_dual_dual_exteriorPower_stalk_genericPoint [IsIntegral X]
    (F : X.Modules) (U : X.Opens) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (F.over U) r] (hU : ∃ x : X, x ∈ U) :
    Nontrivial (Module.Dual (ringStalk X.sheaf (genericPoint X))
      (Module.Dual (ringStalk X.sheaf (genericPoint X))
        (⋀[ringStalk X.sheaf (genericPoint X)]^r (modStalk F (genericPoint X))))) := by
  have := finite_stalk_genericPoint_of_isFiniteLocallyFreeOfRank_over F U r hU
  have hr : Module.finrank (X.presheaf.stalk (genericPoint X) : Type u)
      (⋀[(X.presheaf.stalk (genericPoint X) : Type u)]^r
        (F.presheaf.stalk (genericPoint X))) = 1 := by
    rw [exteriorPower.finrank_eq,
      finrank_stalk_genericPoint_eq_of_isFiniteLocallyFreeOfRank_over F U r hU,
      Nat.choose_self]
  have : Nontrivial (⋀[(X.presheaf.stalk (genericPoint X) : Type u)]^r
      (F.presheaf.stalk (genericPoint X))) :=
    Module.nontrivial_of_finrank_pos (R := (X.presheaf.stalk (genericPoint X) : Type u))
      (by rw [hr]; exact Nat.one_pos)
  exact (Module.evalEquiv (X.presheaf.stalk (genericPoint X) : Type u)
    (⋀[(X.presheaf.stalk (genericPoint X) : Type u)]^r
      (F.presheaf.stalk (genericPoint X)))).symm.toEquiv.nontrivial

/-- **The stalk of the determinant of `F` at the generic point of an integral scheme is
nontrivial**, for `F` finite locally free of rank `r` over a nonempty open. This is the
nontriviality hypothesis of
`AlgebraicGeometry.Scheme.Modules.detMap_ne_zero_of_surjective_of_ker_le_torsion`. -/
theorem nontrivial_modStalk_det_genericPoint [IsIntegral X]
    (F : X.Modules) (U : X.Opens) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (F.over U) r] (hU : ∃ x : X, x ∈ U)
    [(exteriorPower F (r : ℤ)).IsFinitePresentation]
    [(dualSheaf (exteriorPower F (r : ℤ))).IsFinitePresentation] :
    Nontrivial (modStalk (reflexiveHull (exteriorPower F (r : ℤ))) (genericPoint X)) :=
  have := nontrivial_dual_dual_exteriorPower_stalk_genericPoint F U r hU
  nontrivial_modStalk_det (F := F) r (genericPoint X)

end AlgebraicGeometry.Scheme.Modules

end
