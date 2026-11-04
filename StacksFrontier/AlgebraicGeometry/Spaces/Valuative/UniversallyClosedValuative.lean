module

public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ValuativeCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.Valuative.PushDownSolution

/-!
# The valuative criterion for universal closedness

Let `B` be a big fppf site containing a scheme `S` and let `f : X ⟶ Y` be a quasi-compact
separated morphism of algebraic spaces over `S`. Then `f` is universally closed exactly when it
satisfies the existence part of the valuative criterion of Stacks 03IX, in which the valuation
ring may be enlarged, and exactly when every valuative square for `f` already has a lift over
the given valuation ring, with no extension of the fraction field and no domination.

## Main results

* `AlgebraicGeometry.Space.universallyClosed_tfae_of_isQuasiCompact_of_isSeparated`: the
  equivalence of the three conditions above.

## References

* [Stacks Project, Tag 0A3Y](https://stacks.math.columbia.edu/tag/0A3Y)
* [Stacks Project, Tag 0A3X](https://stacks.math.columbia.edu/tag/0A3X)
* [Stacks Project, Tag 0A3W](https://stacks.math.columbia.edu/tag/0A3W)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- For a quasi-compact separated morphism `f : X ⟶ Y` of algebraic spaces over `S`, universal
closedness, the existence part of the valuative criterion of Stacks 03IX, and the existence of a
lift in every valuative square for `f` over the valuation ring itself are equivalent. -/
@[stacks 0A3Y]
public theorem universallyClosed_tfae_of_isQuasiCompact_of_isSeparated
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hqc : IsQuasiCompact B S hS f) (hsep : IsSeparated B S hS f) :
    List.TFAE
      [UniversallyClosed B S hS f,
        ValuativeCriterion.Existence f,
        ∀ q : ValuativeSquare f, Nonempty q.Lift] := by
  tfae_have 1 ↔ 2 :=
    universallyClosed_iff_valuativeCriterion_existence_of_isQuasiCompact_of_isQuasiSeparated
      hX hY f hqc (isQuasiSeparated_of_isSeparated B S hS hsep)
  tfae_have 2 ↔ 3 := ⟨fun h q => (h q).elim (exists_lift_of_dominatingExtension hX hY hsep q),
    valuativeCriterionExistence_of_forall_nonempty_lift f⟩
  tfae_finish

end AlgebraicGeometry.Space

end
