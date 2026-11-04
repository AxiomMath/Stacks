module

public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingTensorStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.ChangeOfBaseScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRelocalize

/-!
# The space of Stacks 07UY viewed over `Spec ℤ`

In the situation of Stacks 07UY, with `X` an algebraic space over a scheme `S` and
`A = Γ(X, 𝒪_X)`, the source's canonical morphism `p : X → Spec(A)` is a morphism of algebraic
spaces over `Spec ℤ`: `Spec(A)` carries no morphism to the base `S`, so Stacks forms `p`
(Properties of Spaces, Lemma 05Z1) after regarding `X` as an algebraic space over `ℤ`.  This file
identifies the global functions of that view with `A`.

## Main definitions

* `AlgebraicGeometry.Space.CohomologyVanishingSituation.spaceOverIntegersGlobalFunctionsEquiv`
  identifies the global functions of
  `AlgebraicGeometry.Space.CohomologyVanishingSituation.spaceOverIntegers`, `X` viewed as an
  algebraic space over `Spec ℤ`, with `A`.

## Implementation notes

The view over `Spec ℤ` is `AlgebraicGeometry.Space.viewOverIntegers`, the lower-shriek extension
along `S → Spec ℤ`, and it does not change the small étale site, the structure sheaf or the
global functions of `X` (`AlgebraicGeometry.Space.SmallEtale.relocalizeEquivalence`).

## References

* [Stacks Project, Tag 07UY](https://stacks.math.columbia.edu/tag/07UY)
* [Stacks Project, Tag 05Z1](https://stacks.math.columbia.edu/tag/05Z1)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u m

namespace CohomologyVanishingSituation

variable (T : CohomologyVanishingSituation.{u, m})

/-- **Viewing `X` over `Spec ℤ` does not change its global functions**: the ring of global
functions of `AlgebraicGeometry.Space.CohomologyVanishingSituation.spaceOverIntegers` is
`A = Γ(X, 𝒪_X)`, by restriction along the equivalence of small étale sites. -/
def spaceOverIntegersGlobalFunctionsEquiv :
    Space.globalFunctions T.site (⊤_ Scheme.{u}) T.containsTerminal T.spaceOverIntegers.1 ≃+*
      T.globalFunctions :=
  globalFunctionsRelocalizeEquiv T.site T.base (⊤_ Scheme.{u}) T.containsBase T.containsTerminal
    ⟨terminal.from T.base⟩ T.space.1

end CohomologyVanishingSituation

end AlgebraicGeometry.Space

end
