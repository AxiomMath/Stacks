module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianValuativeCriterionUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedSmoothLocalQuasiCompact
import StacksFrontier.AlgebraicGeometry.Stacks.ReducedClosedSubstackExistence

/-!
# Stacks 0H2C with nothing assumed

This file restates the three results of
`StacksFrontier/AlgebraicGeometry/Stacks/NoetherianValuativeCriterionUniversallyClosed.lean` on
**Stacks 0H2C** under primed names; they are proved there with nothing assumed.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isClosed_of_discreteExistence'`: steps 3 and 4 of the
  proof, closedness on points.
* `AlgebraicGeometry.Stack.AlgebraicStacks`
  `.isClosed_baseChange_affine_isLocallyOfFinitePresentation_of_discreteExistence'`: clause (2)
  of Stacks 0H2A for `f`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.universallyClosed_of_discreteExistence'`:
  **Stacks 0H2C**.

## References

* [Stacks Project, Tag 0H2A](https://stacks.math.columbia.edu/tag/0H2A)
* [Stacks Project, Tag 0H2C](https://stacks.math.columbia.edu/tag/0H2C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}

namespace AlgebraicStacks

/-- **Stacks 0H2C, steps 3 and 4: closedness on points, with nothing assumed.** Let `f : 𝒳 ⟶ 𝒴`
be a finite-type 1-morphism of algebraic stacks over `S` with `𝒴` locally Noetherian which
satisfies the discrete existence part of the valuative criterion. Then `f` is closed on points.

This is `AlgebraicGeometry.Stack.AlgebraicStacks.isClosed_of_discreteExistence`. -/
@[stacks 0H2C "steps 3 and 4 of the proof: closedness on points"]
alias isClosed_of_discreteExistence' := isClosed_of_discreteExistence

/-- **Stacks 0H2A, item (2), from the hypothesis of Stacks 0H2C, with nothing assumed.** For
every object `Z` of the site whose scheme is affine and every 1-morphism
`Stack.schemeStack Z ⟶ 𝒴` locally of finite presentation, the map `|𝒳 ×_𝒴 Z| → |Z|` is closed.

This is
`AlgebraicGeometry.Stack.AlgebraicStacks`
`.isClosed_baseChange_affine_isLocallyOfFinitePresentation_of_discreteExistence`. -/
@[stacks 0H2C "clause (2) of Tag 0H2A for `f`"]
alias isClosed_baseChange_affine_isLocallyOfFinitePresentation_of_discreteExistence' :=
  isClosed_baseChange_affine_isLocallyOfFinitePresentation_of_discreteExistence

/-- **Stacks 0H2C.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` with `𝒴`
locally Noetherian and `f` of finite type. If every valuative square for `f` whose valuation ring
is a discrete valuation ring admits a dotted arrow after an extension of the fraction field and
passage to a dominating valuation ring, then `f` is universally closed.

This is `AlgebraicGeometry.Stack.AlgebraicStacks.universallyClosed_of_discreteExistence`. -/
@[stacks 0H2C "the lemma"]
alias universallyClosed_of_discreteExistence' := universallyClosed_of_discreteExistence

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
