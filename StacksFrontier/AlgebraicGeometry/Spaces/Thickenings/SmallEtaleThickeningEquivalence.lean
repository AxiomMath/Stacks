module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpacesEtaleChartLift
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpacesGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTopologicalInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SchemeOfThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurjThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurjThickeningAdditions
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FormallyEtaleOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleFullyFaithfulThickening

/-!
# The small étale site of a thickening

Let `i : X ⟶ X'` be a thickening of algebraic spaces over a scheme `S`. Base change
`V' ↦ X ×_{X'} V'` of étale scheme charts is an equivalence from the small étale site of `X'`
to that of `X` ([Stacks Project, Tag 05ZS]).

## Main results

* `AlgebraicGeometry.Space.isEquivalence_smallBaseChange_of_isThickeningHom`: Stacks 05ZS.

## Implementation notes

The comparison functors of Stacks 03G1 embed the small étale sites fully faithfully into the
spaces-étale sites, and base change of scheme charts is the restriction of base change of
spaces étale over `X'` (Stacks 03G2, part (4)), which is an equivalence at a thickening
(Stacks 05ZH, `AlgebraicGeometry.Space.isEquivalence_spacesBaseChange_of_isThickeningHom`).
What is left is that an algebraic space `V'` étale over `X'` whose base change to `X` is a
scheme is itself a scheme: the projection `X ×_{X'} V' ⟶ V'` is a base change of `i`, hence a
thickening, and a thickening of a scheme is a scheme by Stacks 05ZR
(`AlgebraicGeometry.Space.isRepresentable_of_isThickeningHom_of_isRepresentable`).
Unlike `AlgebraicGeometry.Space.smallEtalePullback_isEquivalence_of_isThickeningHom`, which
passes through Stacks 07VV for integral universally injective surjective morphisms, nothing is
assumed beyond the thickening.

## References

* [Stacks Project, Tag 05ZS](https://stacks.math.columbia.edu/tag/05ZS)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 05ZS.** Let `i : X ⟶ X'` be a thickening of algebraic spaces over `S`. Base change
`V' ↦ X ×_{X'} V'` is an equivalence from the small étale site of `X'` to that of `X`. -/
@[stacks 05ZS]
theorem isEquivalence_smallBaseChange_of_isThickeningHom {X X' : AlgebraicSpaces B S hS}
    (i : X ⟶ X') (hi : IsThickeningHom B S hS i) :
    (smallBaseChange B S hS i hi.isClosedImmersion.rep).IsEquivalence := by
  have := comparisonFunctor_full B S hS X
  have := comparisonFunctor_faithful B S hS X
  have := comparisonFunctor_full B S hS X'
  have := comparisonFunctor_faithful B S hS X'
  have := isEquivalence_spacesBaseChange_of_isThickeningHom B S hS i hi
  refine isEquivalence_of_restriction (comparisonFunctor B S hS X')
    (comparisonFunctor B S hS X) _ ((spacesBaseChange B S hS i).functor)
    (smallBaseChange_comparison B S hS i hi.isClosedImmersion.rep) fun V hV ↦ ?_
  refine (essImage_comparisonFunctor_iff B S hS X' V).2 ?_
  exact isRepresentable_of_isThickeningHom_of_isRepresentable B S hS _
    (isThickeningHom_of_isPullback B S hS ((spacesBaseChange B S hS i).isPullback V).flip hi)
    ((essImage_comparisonFunctor_iff B S hS X _).1 hV)

end AlgebraicGeometry.Space

end
