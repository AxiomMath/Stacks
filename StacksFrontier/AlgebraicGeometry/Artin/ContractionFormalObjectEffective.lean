module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionFormalObjectExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.CompletionProperOverIsEquivalenceBaseObject

/-!
# Every formal object of Artin's contraction functor is effective

In Situation 0GH8 (`AlgebraicGeometry.Artin.ContractionSituation`) assume `X' ⟶ S` is separated.
Then every formal object for the functor `F` of Stacks 0GHA
(`AlgebraicGeometry.Artin.contractionFunctor`) is effective: this is Artin's axiom `[4]` in the
functor form `AlgebraicGeometry.LocallyNoetherianOver.HasEffectiveFormalObjects`.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.hasEffectiveFormalObjects`: if `X' ⟶ S` is
  separated, every formal object of the contraction functor is effective (Stacks 0GI8).

## References

* [Stacks Project, Tag 0GI8](https://stacks.math.columbia.edu/tag/0GI8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (c : ContractionSituation B S hS)

attribute [local instance] Space.isAffine_toScheme_baseObject
  Space.isLocallyNoetherian_toScheme_baseObject

/-- In Situation 0GH8 assume `X' ⟶ S` is separated. Then every formal object for the contraction
functor `F` is effective. -/
@[stacks 0GI8]
theorem hasEffectiveFormalObjects (hX' : Space.IsSeparated B S hS (terminal.from c.X')) :
    LocallyNoetherianOver.HasEffectiveFormalObjects B S hS (contractionFunctor c) :=
  c.hasEffectiveFormalObjects_of_completionProperOverIsEquivalence
    (fun R _ _ hR J _ f' => Space.C1573.completionProperOverIsEquivalence_baseObject R hR J f')
    hX'

end AlgebraicGeometry.Artin.ContractionSituation

end
