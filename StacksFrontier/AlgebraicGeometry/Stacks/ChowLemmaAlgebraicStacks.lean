module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowGeneralCase
public import StacksFrontier.AlgebraicGeometry.Stacks.DescendingStacksAlongConventionalLimit
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedAtFiniteStageConvention
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedClosedImmersionIntoFinitePresentationOverIntegers

/-!
# Chow's lemma for algebraic stacks (Stacks 0CQ8)

Let `f : 𝒳 ⟶ Y` be a 1-morphism from an algebraic stack to an algebraic space, with `Y`
quasi-compact and quasi-separated and `f` separated of finite type. Then there are an algebraic
space `X` with a proper surjective 1-morphism `X ⟶ 𝒳`, an open immersion `X ⟶ X̄` and a proper
morphism `X̄ ⟶ Y` of algebraic spaces such that `X ⟶ 𝒳 ⟶ Y` is 2-isomorphic to `X ⟶ X̄ ⟶ Y`.

This is `AlgebraicGeometry.Stack.AlgebraicStacks.hasChowCover_of_statements` with the three
statements of Limits of Stacks its reduction to the Noetherian case uses discharged: Stacks 0CQ2
(`AlgebraicGeometry.Stack.AlgebraicStacks.closedImmersionIntoFinitePresentationStatement_holds`),
and Stacks 0CN4 and Stacks 0CPZ for systems satisfying the chapter's convention of Section 70.2
(`AlgebraicGeometry.Stack.AlgebraicStacks.finitePresentationStackDescendsStatement_holds` and
`AlgebraicGeometry.Stack.AlgebraicStacks.separatedAtFiniteStageStatement_holds`), the Noetherian
approximations of Stacks 07SU satisfying that convention.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.hasChowCover`: Stacks 0CQ8.

## References

* [Stacks Project, Tag 0CQ8](https://stacks.math.columbia.edu/tag/0CQ8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

/-- **Stacks 0CQ2 over `Spec ℤ`**, as `ClosedImmersionIntoFinitePresentationStatement`. -/
theorem closedImmersionIntoFinitePresentationStatement_holds (B : BigFppfSite.{u}) :
    ClosedImmersionIntoFinitePresentationStatement.{u, w} B (⊤_ Scheme.{u})
      B.contains_terminal := by
  intro Y hY 𝒳 f hft hsep hYqc hYqs
  exact exists_separated_finitePresentation_closedImmersion_overIntegers B.contains_terminal Y hY 𝒳
    f hft.1
    (isQuasiCompactStack_of_isQuasiCompactMorphism.{u, w} B (⊤_ Scheme.{u}) B.contains_terminal f
      hft.2 (isQuasiCompactStack_fibredCategory.{u, w} B (⊤_ Scheme.{u}) B.contains_terminal Y hY
        hYqc _))
    hsep hYqc hYqs

/-- **Stacks 0CPZ under the chapter's convention**, as `SeparatedAtFiniteStageStatement`. -/
theorem separatedAtFiniteStageStatement_holds (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : SeparatedAtFiniteStageStatement.{u, w} B S hS :=
  fun D hconv 𝒳₀ f₀ hqc hqs hf =>
    D.exists_isSeparated_stage_of_siteContainsBaseChangeLimits hconv 𝒳₀ f₀ hqc hqs hf

/-- **Chow's lemma for algebraic stacks (Stacks 0CQ8).** Let `f : 𝒳 ⟶ Y` be a 1-morphism from an
algebraic stack to an algebraic space over `S`, with `Y` quasi-compact and quasi-separated and `f`
separated of finite type. Then there are an algebraic space `X` with a proper surjective
1-morphism `a : X ⟶ 𝒳`, an open immersion `i : X ⟶ X̄` and a proper morphism `p : X̄ ⟶ Y` of
algebraic spaces such that `a ≫ f` is 2-isomorphic to the 1-morphism induced by `i ≫ p`. -/
@[stacks 0CQ8 "Chow's lemma for algebraic stacks: the commutative diagram is a 2-isomorphism \
`a ≫ f ≅ i ≫ p` in the 2-category of algebraic stacks over S, with X and X̄ algebraic spaces"]
theorem hasChowCover (B : BigFppfSite.{u}) {S : Scheme.{u}} {hS : B.Contains S}
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYqc : Space.IsQuasiCompactSpace B S hS Y)
    (hYqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hsep : IsSeparated B S hS f) (hft : IsFiniteType B S hS f) :
    HasChowCover.{u, w} B S hS hY f :=
  hasChowCover_of_statements B
    (closedImmersionIntoFinitePresentationStatement_holds B)
    (finitePresentationStackDescendsStatement_holds B (⊤_ Scheme.{u}) B.contains_terminal)
    (separatedAtFiniteStageStatement_holds B (⊤_ Scheme.{u}) B.contains_terminal)
    hY hYqc hYqs f hsep hft

end AlgebraicGeometry.Stack.AlgebraicStacks

end
