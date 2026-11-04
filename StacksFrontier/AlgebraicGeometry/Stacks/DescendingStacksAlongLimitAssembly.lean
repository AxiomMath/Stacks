module

public import StacksFrontier.AlgebraicGeometry.Stacks.DescendingStacksAlongLimit

/-!
# The quotient stack models and the assembly of Stacks 0CN4 from the steps of its proof

Let `(X_i)` be a directed inverse system of quasi-compact, quasi-separated algebraic spaces over
`S` with affine transition morphisms and limit `X = lim X_i`. This file collects the objects the
proof of Stacks 0CN4 is assembled from, beside those of
`StacksFrontier.AlgebraicGeometry.Stacks.DescendingStacksAlongLimit`, and the assembly itself.

## Main definitions

* `AlgebraicGeometry.Stack.Theorem04TK`: the conclusion of Stacks 04TK for every groupoid in
  algebraic spaces over `S`.
* `AlgebraicGeometry.Stack.QuotientStackModel`: a model of the quotient stack `[U/R]` of a
  groupoid over an algebraic space `Y` in the 2-category of algebraic stacks over `S`, with
  `AlgebraicGeometry.Stack.StackDescentSystem.QuotientStackModel.toModel` and `.ofModel`
  identifying it, at a stage, with
  `AlgebraicGeometry.Stack.StackDescentSystem.QuotientStackModel`.

## Main results

* `AlgebraicGeometry.Stack.hasAffineSmoothPresentation_of_isQuasiCompactMorphism`: Stacks 04YC
  for an algebraic stack quasi-compact over a quasi-compact algebraic space.
* `AlgebraicGeometry.Stack.StackDescentSystem.exists_stage_model_of_inputs`: Stacks 0CN4 from
  the conclusion of Stacks 04TK and the five steps of the source's proof, each stated as a
  proposition in `StacksFrontier.AlgebraicGeometry.Stacks.DescendingStacksAlongLimit` and proved in
  a module of its own;
  `StackDescentSystem.exists_stage_model_of_isFinitePresentation_unconditional`, in
  `DescendingStacksAlongLimitTheorem.lean`, discharges them.

## References

* [Stacks Project, Tag 04TK](https://stacks.math.columbia.edu/tag/04TK)
* [Stacks Project, Tag 04YC](https://stacks.math.columbia.edu/tag/04YC)
* [Stacks Project, Tag 0CN4](https://stacks.math.columbia.edu/tag/0CN4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The conclusion of Stacks 04TK for every groupoid in algebraic spaces over `S`**: the
quotient stack of a smooth groupoid in algebraic spaces is an algebraic stack. Quantified over
all groupoids so that it applies to the groupoid the proof of Stacks 0CN4 descends to a stage. -/
abbrev Theorem04TK : Prop :=
  ∀ (A : AlgebraicSpaces B S hS) (G : GroupoidInAlgebraicSpaces B S hS A),
    GroupoidInAlgebraicSpaces.IsSmooth B S hS G → IsAlgebraicStack.{u, w} B S hS (quotientStack G)

/-- **Stacks 04YC for an algebraic stack quasi-compact over a quasi-compact algebraic space.**
Such a stack is quasi-compact
(`AlgebraicGeometry.Stack.isQuasiCompactStack_of_isQuasiCompactMorphism`), so it has an affine
smooth surjective chart
(`AlgebraicGeometry.Stack.isQuasiCompactStack_iff_hasAffineSmoothPresentation`). -/
theorem hasAffineSmoothPresentation_of_isQuasiCompactMorphism
    (Y : AlgebraicSpaces B S hS) (hYqc : Space.IsQuasiCompactSpace B S hS Y.obj)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y.obj Y.property)
    (hf : IsQuasiCompactMorphism B S hS f) :
    HasAffineSmoothPresentation.{u, w} B S hS 𝒳 :=
  (isQuasiCompactStack_iff_hasAffineSmoothPresentation.{u, w} B S hS 𝒳).1
    (isQuasiCompactStack_of_isQuasiCompactMorphism.{u, w} B S hS f hf
      (isQuasiCompactStack_fibredCategory.{u, w} B S hS Y.obj Y.property hYqc
        (algebraicSpaceStack.{u, w} B S hS Y.obj Y.property).property))

variable {B S hS} in
/-- **A model of a quotient stack in the 2-category of algebraic stacks over `S`.** For a
groupoid `(U, R, s, t, c)` in algebraic spaces over an algebraic space `Y`, an algebraic stack over
`S` with a 1-morphism to `Y`, together with an identification over `Y` of its category with the
quotient stack `[U/R]`.

A quotient stack is not itself an object of `AlgebraicGeometry.Stack.AlgebraicStacks`: its hom
sets sit one universe higher. This is the object that stands in for it. -/
structure QuotientStackModel (Y : AlgebraicSpaces B S hS)
    (G : GroupoidInAlgebraicSpaces B S hS Y) where
  /-- The algebraic stack over `S` modelling `[U/R]`. -/
  stack : AlgebraicStacks.{u, w} B S hS
  /-- Its structure 1-morphism to `Y`. -/
  structureMorphism : stack ⟶ algebraicSpaceStack.{u, w} B S hS Y.obj Y.property
  /-- The identification with the quotient stack, over `Y`. -/
  equivOver : BasedCategory.EquivalenceOver (quotientStackToBase G)
    structureMorphism.hom.hom

namespace StackDescentSystem

variable {B S hS} {hZ : B.Contains (⊤_ Scheme.{u})}
variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (C : StackDescentSystem B S hS hZ I)

/-- A model of a quotient stack at a stage is a model over the stage, in the sense of
`AlgebraicGeometry.Stack.QuotientStackModel`. -/
def QuotientStackModel.toModel {i : Iᵒᵖ} {Gᵢ : GroupoidInAlgebraicSpaces B S hS (C.stageSpace i)}
    (M : C.QuotientStackModel.{u, w} i Gᵢ) : Stack.QuotientStackModel.{u, w} (C.stageSpace i) Gᵢ :=
  ⟨M.stack, M.structureMorphism, M.equivOver⟩

/-- A model over the stage, in the sense of `AlgebraicGeometry.Stack.QuotientStackModel`, is a
model of the quotient stack at that stage. -/
def QuotientStackModel.ofModel {i : Iᵒᵖ} {Gᵢ : GroupoidInAlgebraicSpaces B S hS (C.stageSpace i)}
    (M : Stack.QuotientStackModel.{u, w} (C.stageSpace i) Gᵢ) : C.QuotientStackModel.{u, w} i Gᵢ :=
  ⟨M.stack, M.structureMorphism, M.equivOver⟩

/-- **Stacks 0CN4 from the five steps of its proof and Stacks 04TK.** Let `(X_i)` be a directed
inverse system of quasi-compact, quasi-separated algebraic spaces over `S` with affine transition
morphisms, and let `X = lim X_i`. Given Stacks 04TK and the five steps of the source's proof —
the groupoid presentation over the base, the descent of the groupoid to a stage, the small-hom
model of the quotient stack at the stage, its finite presentation and the base-change comparison —
every algebraic stack `𝒳` of finite presentation over `X` is `𝒳_i ×_{X_i} X` for an algebraic
stack `𝒳_i` of finite presentation over some `X_i`. -/
theorem exists_stage_model_of_inputs
    (h04TK : Theorem04TK.{u, w} B S hS)
    (hPresentation : GroupoidPresentationOfAffineSmoothChart.{u, w} B S hS hZ)
    (hDescent : C.GroupoidStructureDescendsToStage)
    (hStageStackModel : C.StageStackModel.{u, w})
    (hModelFinitePresentation : C.ModelIsFinitePresentation.{u, w})
    (hModelComparison : C.ModelBaseChangeComparison.{u, w})
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (f : 𝒳 ⟶ C.limitStack.{u, w})
    (hf : AlgebraicStacks.IsFinitePresentation B S hS f) :
    ∃ (i : Iᵒᵖ) (𝒳ᵢ : AlgebraicStacks.{u, w} B S hS) (fᵢ : 𝒳ᵢ ⟶ C.stageStack.{u, w} i),
      AlgebraicStacks.IsFinitePresentation B S hS fᵢ ∧
        ∃ e : Bicategory.Equivalence 𝒳
          (twoFibreProductAlgebraicStack.{u, w} B S hS fᵢ
            (C.limitStackProjection.{u, w} i)),
          Nonempty (e.hom ≫ (twoFibreProductSquareAlgebraicStacks.{u, w} B S hS fᵢ
            (C.limitStackProjection.{u, w} i)).snd ≅ f) := by
  obtain ⟨P⟩ := hasSmoothPresentationOverBase.{u, w} B S hS hZ hPresentation
    C.limitSpace C.limit_quasiCompact C.limit_quasiSeparated 𝒳 f hf
  obtain ⟨i, Gᵢ, hGᵢsmooth, hGᵢobjects, hGᵢarrows, ⟨eDescent⟩⟩ :=
    C.smoothGroupoidDescendsToStage hDescent P.groupoid P.isSmooth
      P.objects_finitePresentation P.arrows_finitePresentation
  have hGᵢalgebraic : IsAlgebraicStack.{u, w} B S hS (quotientStack Gᵢ) :=
    h04TK _ Gᵢ hGᵢsmooth
  obtain ⟨𝒳ᵢ, fᵢ, hfᵢ, ⟨eModel⟩⟩ :=
    C.stageModelOfSmoothGroupoid hStageStackModel hModelFinitePresentation hModelComparison
      i Gᵢ hGᵢalgebraic hGᵢsmooth hGᵢobjects hGᵢarrows
  refine ⟨i, 𝒳ᵢ, fᵢ, hfᵢ,
    equivalenceOfBasedEquivalence.{u, w} B S hS ((P.equivOver.trans eDescent).trans eModel).equiv,
    ⟨isoMkAlgebraicStacks.{u, w} B S hS ((P.equivOver.trans eDescent).trans eModel).compIso⟩⟩

end StackDescentSystem

end AlgebraicGeometry.Stack

end
