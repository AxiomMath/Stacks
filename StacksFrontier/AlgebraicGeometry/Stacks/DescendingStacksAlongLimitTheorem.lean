module

public import StacksFrontier.AlgebraicGeometry.Stacks.DescendingStacksAlongConventionalLimit

/-!
# Descending an algebraic stack of finite presentation along a limit

Let `(X_i)` be a directed inverse system of quasi-compact, quasi-separated algebraic spaces over
`S` with affine transition morphisms and limit `X = lim X_i`. Stacks 0CN4 says that every
algebraic stack `𝒳` of finite presentation over `X` is a base change from a finite stage: there
are an `i` and an algebraic stack `𝒳_i` of finite presentation over `X_i` with
`𝒳 ≅ 𝒳_i ×_{X_i} X` as algebraic stacks over `X`.

This file proves that statement in the situation `AlgebraicGeometry.Stack.StackDescentSystem`,
with none of the inputs that the reduction
`AlgebraicGeometry.Stack.StackDescentSystem.exists_stage_model_of_isFinitePresentation` carries.
The bound on the index that `StackDescentSystem` records makes the system small for the site
(`AlgebraicGeometry.Space.IsSiteSmall.of_lt_cof_op`), hence a system satisfying the chapter's
standing convention of Section 70.2, tag 07SD
(`AlgebraicGeometry.Space.IsSiteSmall.siteContainsBaseChangeLimits`), and under that convention
Stacks 0CN4 is
`AlgebraicGeometry.Stack.AlgebraicStacks.finitePresentationStackDescendsStatement_holds`, whose
proof runs the source's argument: the smooth groupoid presentation of finite presentation
(Stacks 04YC, 04T4, 04T5), its descent to a stage (Stacks 07SK, 0CN2, 046Q), Stacks 04TK at the
stage, the model of the quotient stack and its finite presentation (Stacks 06Q2), and the
comparison of its base change with the 2-fibre product (Stacks 044P, 044R, 046Q, 04Y1).

## Main results

* `StackDescentSystem.exists_stage_model_of_isFinitePresentation_unconditional`: Stacks 0CN4, an
  algebraic stack of finite presentation over the limit is a base change from a finite stage.

## References

* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
* [Stacks Project, Tag 0CN4](https://stacks.math.columbia.edu/tag/0CN4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack.StackDescentSystem

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    [Nonempty I]

/-- **The system of Stacks 0CN4 satisfies the chapter's convention of Section 70.2 (tag 07SD).**
The bound on the index makes it small for the site, and a system small for the site has the
limits of its base changes to affine objects inside the site. -/
theorem siteContainsBaseChangeLimits (C : StackDescentSystem B S hS hZ I) :
    Space.SiteContainsBaseChangeLimits B S hS C.diagram :=
  Space.IsSiteSmall.siteContainsBaseChangeLimits B S hS C.diagram
    (Space.IsSiteSmall.of_lt_cof_op
      ((Cardinal.mk_congr (Opposite.equivToOpposite (α := I))).trans_lt C.indexSize))

/-- **Stacks 0CN4.** Let `(X_i)` be a directed inverse system of quasi-compact, quasi-separated
algebraic spaces over `S` with affine transition morphisms, and let `X = lim X_i`. If `𝒳` is an
algebraic stack of finite presentation over `X`, then there are a stage `i` and an algebraic
stack `𝒳_i` of finite presentation over `X_i` with `𝒳 ≅ 𝒳_i ×_{X_i} X` as algebraic stacks
over `X`.

This is the statement of `StackDescentSystem.exists_stage_model_of_isFinitePresentation` with
none of its hypotheses. The system satisfies the chapter's convention
(`StackDescentSystem.siteContainsBaseChangeLimits`), and under the convention the statement is
`AlgebraicGeometry.Stack.AlgebraicStacks.finitePresentationStackDescendsStatement_holds`. -/
@[stacks 0CN4 "The directed set `I` indexes the system as a covariant diagram on the cofiltered \
category `Iᵒᵖ`, and `StackDescentSystem` bounds the cardinality of `Iᵒᵖ` and of its hom types by \
the cofinality of the cutoff of the big fppf site, which is what keeps the limit `X` inside the \
site. The isomorphism `𝒳 ≅ 𝒳_i ×_{X_i} X` over `X` is an equivalence in the 2-category of \
algebraic stacks whose forward 1-morphism followed by the projection to `X` is 2-isomorphic to \
the structure 1-morphism of `𝒳`. Every step of the source's proof is proved in the library."]
theorem exists_stage_model_of_isFinitePresentation_unconditional
    (C : StackDescentSystem B S hS hZ I)
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (f : 𝒳 ⟶ C.limitStack.{u, w})
    (hf : AlgebraicStacks.IsFinitePresentation B S hS f) :
    ∃ (i : Iᵒᵖ) (𝒳ᵢ : AlgebraicStacks.{u, w} B S hS) (fᵢ : 𝒳ᵢ ⟶ C.stageStack.{u, w} i),
      AlgebraicStacks.IsFinitePresentation B S hS fᵢ ∧
        ∃ e : Bicategory.Equivalence 𝒳
          (twoFibreProductAlgebraicStack.{u, w} B S hS fᵢ
            (C.limitStackProjection.{u, w} i)),
          Nonempty (e.hom ≫ (twoFibreProductSquareAlgebraicStacks.{u, w} B S hS fᵢ
            (C.limitStackProjection.{u, w} i)).snd ≅ f) :=
  AlgebraicStacks.finitePresentationStackDescendsStatement_holds.{u, w} B S hS C.diagram
    C.limit_isAlgebraicSpace C.stage_isAlgebraicSpace C.transition_affine C.stage_quasiCompact
    C.stage_quasiSeparated C.siteContainsBaseChangeLimits 𝒳 f hf

end AlgebraicGeometry.Stack.StackDescentSystem

end
