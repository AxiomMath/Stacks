module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillanCriterion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillanSupplement

/-!
# Further results on `StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillanCriterion`

Results of this development stated next to
`StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillanCriterion` but kept in a module of their own,
so that that module stays as it is on the base.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

/-- **Stacks 0AIC, condition (2) implies condition (3)**, for the conditions with the morphism
to `Spec A` recorded as a `AlgebraicGeometry.FormalSpace.MapToScheme`. If some morphism from `X`
to an affine scheme turns every closed immersion of an *affine* scheme into `X` into a closed
immersion of schemes, then it does so for every *scheme* of the site: a scheme closed-immersed in
an affine formal algebraic space is already affine. -/
@[stacks 0AIC "part (2) implies part (3)"]
theorem HasAffineClosedImmersionCriterionMapToSpec.hasSchemeClosedImmersionCriterionMapToSpec
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X : FppfSheaf B S hS}
    (hX : HasAffineClosedImmersionCriterionMapToSpec B S hS X) :
    HasSchemeClosedImmersionCriterionMapToSpec B S hS X := by
  obtain ⟨hA, A, f, hf⟩ := hX
  refine ⟨hA, A, f, fun T g hg ↦ ?_⟩
  exact hf ⟨T, isAffine_of_isClosedImmersionInto B S hS hA g hg⟩ g hg

end AlgebraicGeometry.FormalSpace

end
