module

public import StacksFrontier.AlgebraicTopology.SimplicialObject.Skeleton

/-!
# The unit of the adjunction `i_{m!} ⊣ sk_m` is an isomorphism

Let `C` be a category with finite colimits and `m : ℕ`. The skeleton functor
`sk_m : Simp(C) ⥤ Simp_m(C)` has a left adjoint `i_{m!}`, the left Kan extension along the
inclusion `Δ_{≤ m} ⊆ Δ`, with `(i_{m!}U)_n = colim_{(⦋n⦌/Δ)^{opp}_{≤ m}} U`. For an `m`-truncated
simplicial object `U`, the unit `U ⟶ sk_m i_{m!} U` of this adjunction is an isomorphism.

## Main results

* `CategoryTheory.SimplicialObject.Truncated.isIso_lanAdjunction_unit_app`: for `C` with finite
  colimits and `U` an `m`-truncated simplicial object of `C`, the unit
  `U ⟶ sk_m i_{m!} U` of `i_{m!} ⊣ sk_m` is an isomorphism.

## References

* [Stacks, Tag 018N](https://stacks.math.columbia.edu/tag/018N)
-/

public section

universe v u

namespace CategoryTheory.SimplicialObject.Truncated

open Limits

variable {C : Type u} [Category.{v} C] [HasFiniteColimits C]

/-- Let `C` be a category with finite colimits and let `U` be an `m`-truncated simplicial object
of `C`. The unit `U ⟶ sk_m i_{m!} U` of the adjunction `i_{m!} ⊣ sk_m`, where
`i_{m!} = CategoryTheory.SimplicialObject.Truncated.sk m` is the left Kan extension along the
inclusion `Δ_{≤ m} ⊆ Δ` and `sk_m = CategoryTheory.SimplicialObject.truncation m` is restriction
along it, is an isomorphism. -/
@[stacks 018N]
theorem isIso_lanAdjunction_unit_app (m : ℕ) (U : SimplicialObject.Truncated C m) :
    IsIso (X := U) (Y := (truncation m).obj ((Truncated.sk m).obj U))
      (((SimplexCategory.Truncated.inclusion m).op.lanAdjunction C).unit.app U) :=
  inferInstanceAs (IsIso (((SimplexCategory.Truncated.inclusion m).op.lanAdjunction C).unit.app U))

end CategoryTheory.SimplicialObject.Truncated

end
