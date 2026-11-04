module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidPresentationBootstrap
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack

/-!
# A smooth surjective cover by an algebraic stack is equivalent to algebraicity

Let `𝒴` be a category fibred in groupoids over the big fppf site of a scheme `S` which is an
fppf stack and whose diagonal is representable by algebraic spaces. This module shows that `𝒴`
is an algebraic stack **if and only if** it receives a 1-morphism from an algebraic stack which
is representable by algebraic spaces, surjective and smooth.

## Main results

* `AlgebraicGeometry.Stack.exists_smoothSurjectiveAlgebraicCover_of_isAlgebraicStack`: an
  algebraic stack is covered by an algebraic stack — by the stack of its own scheme atlas, which
  is an algebraic stack by **Stacks 04X5**, along the atlas 1-morphism itself.
* `AlgebraicGeometry.Stack.isAlgebraicStack_iff_exists_smoothSurjectiveAlgebraicCover`: the
  resulting equivalence, whose forward implication is
  `AlgebraicGeometry.Stack.isAlgebraicStack_of_smoothSurjectiveAlgebraicCover`.

## Implementation notes

The atlas clause of `AlgebraicGeometry.Stack.IsAlgebraicStack` is the condition of Stacks 03YK
spelled out for the meet of surjectivity and smoothness, so the atlas 1-morphism of an algebraic
stack *is* a term of `AlgebraicGeometry.Stack.HasRelativeProperty` at
`AlgebraicGeometry.Space.surjectiveMorphismProperty ⊓
AlgebraicGeometry.Space.smoothMorphismProperty` with no transport: this is already how
`AlgebraicGeometry.Stack.isAlgebraicStack_of_smoothSurjectiveAlgebraicCover` consumes the atlas
clause of the covering stack. Likewise the fibred-in-groupoids witness that
`IsAlgebraicStack` existentially quantifies over is a proof of a proposition, so the bundled
`CategoryTheory.CatFiberedInGroupoids` it builds is the one the statement started from.

The reverse implication is what makes the equivalence worth stating. The hypothesis `hcover` of
`AlgebraicGeometry.Stack.isAlgebraicStack_of_flatPresentation` — **Stacks 06DC** — is exactly
the right-hand side here, and the conclusion of that theorem is exactly the left-hand side. The
two further hypotheses of the equivalence below are available there: `hstack` is a hypothesis of
that theorem, and `hdiagonal` is what it now proves from its flat presentation by **Stacks
05XW**. So `hcover` is *equivalent* to the conclusion it is used to produce: nothing weaker than
Artin's theorem on representability of flat groupoids can discharge it, and a declaration
assuming it assumes the tag it registers. It is the one input of Stacks 06DC still carried, the
diagonal input having been discharged. The same observation is made at
`AlgebraicGeometry.Space.isBootstrapAlgebraicSpaceAlongFlatSurjection_iff` about Stacks 0AMP and
Stacks 04S6 part (3).

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
* [Stacks Project, Tag 06DC](https://stacks.math.columbia.edu/tag/06DC)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- **An algebraic stack receives a representable surjective smooth 1-morphism from an algebraic
stack**: its own scheme atlas, read as a 1-morphism out of the category fibred in groupoids of
the presenting scheme of the site.

That category fibred in groupoids is an algebraic stack by **Stacks 04X5**
(`AlgebraicGeometry.Stack.isAlgebraicStack_schemeFibredCategory`), the atlas is representable by
algebraic spaces by the atlas clause of `AlgebraicGeometry.Stack.IsAlgebraicStack`, and that same
clause is the relative-property condition of **Stacks 03YK** at the meet of
`AlgebraicGeometry.Space.surjectiveMorphismProperty` and
`AlgebraicGeometry.Space.smoothMorphismProperty`. -/
theorem exists_smoothSurjectiveAlgebraicCover_of_isAlgebraicStack
    (h𝒴 : IsAlgebraicStack.{u, w} B S hS 𝒴.val) :
    ∃ (𝒲 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
      (q : 𝒲 ⟶ 𝒴) (hq : IsRepresentableByAlgebraicSpaces B S hS q.hom),
      IsAlgebraicStack.{u, w} B S hS 𝒲.val ∧
        HasRelativeProperty.{u, u, u + 1, u} B S hS
          (Space.surjectiveMorphismProperty B S hS ⊓ Space.smoothMorphismProperty B S hS)
          q hq := by
  obtain ⟨hfib, -, -, U, a, ha, hAtlas⟩ := h𝒴
  exact ⟨schemeFibredCategory B S hS U,
    Bicategory.InducedBicategory.mkHom (X := schemeFibredCategory B S hS U) (Y := 𝒴) a, ha,
    isAlgebraicStack_schemeFibredCategory.{u, w} B S hS U, hAtlas⟩

/-- **An fppf stack in groupoids with representable diagonal is an algebraic stack exactly when
it is covered by an algebraic stack.** Both implications are about the same two conditions:

* if `𝒴` receives a 1-morphism from an algebraic stack which is representable by algebraic
  spaces, surjective and smooth, then `𝒴` is an algebraic stack — this is
  `AlgebraicGeometry.Stack.isAlgebraicStack_of_smoothSurjectiveAlgebraicCover`, which composes
  the covering stack's atlas with the covering 1-morphism (**Stacks 0301** and **Stacks 045B**);
* if `𝒴` is an algebraic stack then its own scheme atlas is such a cover, by
  `AlgebraicGeometry.Stack.exists_smoothSurjectiveAlgebraicCover_of_isAlgebraicStack`.

In particular the hypothesis `hcover` of
`AlgebraicGeometry.Stack.isAlgebraicStack_of_flatPresentation` (**Stacks 06DC**) is equivalent,
under the remaining hypotheses of that theorem, to its conclusion. -/
theorem isAlgebraicStack_iff_exists_smoothSurjectiveAlgebraicCover
    (hstack : 𝒴.val.p.IsStack (BigFppfOver.topology B S hS))
    (hdiagonal : IsRepresentableByAlgebraicSpaces B S hS (diagonalBasedFunctor B S hS 𝒴)) :
    IsAlgebraicStack.{u, w} B S hS 𝒴.val ↔
      ∃ (𝒲 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
        (q : 𝒲 ⟶ 𝒴) (hq : IsRepresentableByAlgebraicSpaces B S hS q.hom),
        IsAlgebraicStack.{u, w} B S hS 𝒲.val ∧
          HasRelativeProperty.{u, u, u + 1, u} B S hS
            (Space.surjectiveMorphismProperty B S hS ⊓ Space.smoothMorphismProperty B S hS)
            q hq := by
  refine ⟨exists_smoothSurjectiveAlgebraicCover_of_isAlgebraicStack.{u, w} B S hS, ?_⟩
  rintro ⟨𝒲, q, hq, h𝒲, hqP⟩
  exact isAlgebraicStack_of_smoothSurjectiveAlgebraicCover.{u, w} B S hS q h𝒲 hstack hdiagonal
    hq hqP

end AlgebraicGeometry.Stack

end
