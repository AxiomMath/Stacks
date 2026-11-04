module

public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedImmersionIntoFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.DescendingStacksAlongLimitPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.DescendingStacksAlongLimitStageModel
public import StacksFrontier.AlgebraicGeometry.Stacks.DescendingStacksAlongLimitModelFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.DescendingStacksAlongLimitBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationBaseChangeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.SmoothQuotientStackModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemPropertiesOfAlgebraicLimit

/-!
# The stage stack in the proof of Stacks 0CQ1

Let `Y = lim Y_i` be the limit of a Noetherian limit system over `S` and let `f : 𝒳 ⟶ Y` be a
quasi-separated 1-morphism, locally of finite type, from a quasi-compact algebraic stack. Then `𝒳`
is the quotient stack of a smooth groupoid `(U, R, s, t, c)` over `Y`, and at a stage `i` the
quotient stack `𝒳_i = [U_i/R_i]` of the stage groupoid is of finite presentation over `Y_i`, its
base change `Y ×_{Y_i} 𝒳_i` is of finite presentation over `Y`, and that base change is the
quotient stack of the base-changed groupoid.

## Main results

* `AlgebraicGeometry.Stack.exists_stageModel_of_isFiniteType`: granted Noetherian approximation of
  algebraic spaces, the stage stacks `𝒳_i` exist, are of finite presentation over `Y_i`, and their
  base changes to `Y` are the quotient stacks of the base-changed groupoid.

## References

* [Stacks Project, Tag 0CQ1](https://stacks.math.columbia.edu/tag/0CQ1)
* [Stacks Project, Tag 04TK](https://stacks.math.columbia.edu/tag/04TK)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack

open Space

section

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]

/-- **The stage stack of the proof of Stacks 0CQ1**, granted Noetherian approximation of
quasi-compact, absolutely quasi-separated algebraic spaces (`h07SU`).
Let `f : 𝒳 ⟶ Y` be locally of finite type and quasi-separated with `𝒳` quasi-compact, and let
`Y = lim Y_i` be the limit of a Noetherian limit system. Then `𝒳` is the quotient stack, over
`Y`, of a smooth groupoid `(U, R, s, t, c)` over `Y`, with `U` and `R` quasi-separated over `Y`,
with limit descriptions `Δ`; at every stage `i` past `Δ.index` the quotient stack `𝒳_i` of the
stage groupoid has a model of finite presentation over `Y_i`, its base change `Y ×_{Y_i} 𝒳_i` is
of finite presentation over `Y`, and that base change is, over `Y`, the quotient stack of the
base change of the stage groupoid to `Y`. -/
theorem exists_stageModel_of_isFiniteType
    (D : Space.NoetherianLimitSystem B S hS B.contains_terminal I)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS D.limitSpace.obj D.limitSpace.property)
    (hlft : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (h𝒳qc : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property)
    (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    (h07SU : ∀ Z : (BigFppfOver B (⊤_ Scheme.{u}) B.contains_terminal)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B (⊤_ Scheme.{u}) B.contains_terminal Z →
        Space.IsQuasiCompactSpace B (⊤_ Scheme.{u}) B.contains_terminal Z →
        Space.IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal
          Z →
          HasNoetherianApproximation B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal Z) :
    ∃ (G : GroupoidInAlgebraicSpaces B S hS D.limitSpace) (Δ : G.LimitDescent),
      Space.IsQuasiSeparated B S hS G.objectsToBase.hom ∧
      Space.IsQuasiSeparated B S hS G.arrowsToBase.hom ∧
      Nonempty (BasedCategory.EquivalenceOver f.hom.hom (quotientStackToBase G)) ∧
      ∀ (i : I) (h : Δ.index ≤ i),
        ∃ M : QuotientStackModel.{u, w} (D.stageSpace i) (Δ.stageGroupoid i h),
        AlgebraicStacks.IsFinitePresentation B S hS M.structureMorphism ∧
        AlgebraicStacks.IsFinitePresentation B S hS
          (twoFibreProductSquareAlgebraicStacks.{u, w} B S hS M.structureMorphism
            (Bicategory.InducedBicategory.mkHom
              (associatedMap B S hS (D.limitProjection i).hom).1 :
              algebraicSpaceStack.{u, w} B S hS D.limitSpace.obj D.limitSpace.property ⟶
                algebraicSpaceStack.{u, w} B S hS (D.stageSpace i).obj
                  (D.stageSpace i).property)).snd ∧
        Nonempty (BasedCategory.EquivalenceOver
          (quotientStackToBase (Δ.baseChangeGroupoid i h))
          (twoFibreProductSquareAlgebraicStacks.{u, w} B S hS M.structureMorphism
            (Bicategory.InducedBicategory.mkHom
              (associatedMap B S hS (D.limitProjection i).hom).1 :
              algebraicSpaceStack.{u, w} B S hS D.limitSpace.obj D.limitSpace.property ⟶
                algebraicSpaceStack.{u, w} B S hS (D.stageSpace i).obj
                  (D.stageSpace i).property)).snd.hom.hom) := by
  have hYqs := Space.isAbsolutelyQuasiSeparated_limitCone_pt_of_algebraicLimit D
  have hchart := (isQuasiCompactStack_iff_hasAffineSmoothPresentation.{u, w} B S hS 𝒳).1 h𝒳qc
  obtain ⟨G, hG, hUqc, hUqs, hRqc, hRqs, -, hlft', ⟨e⟩⟩ :=
    exists_smoothGroupoid_overBase_of_affineSmoothChart.{u, w} B S hS B.contains_terminal
      D.limitSpace hYqs 𝒳 f hqs hchart
  obtain ⟨hUlft, hRlft⟩ := hlft' hlft
  obtain ⟨Δ⟩ := GroupoidInAlgebraicSpaces.LimitDescent.nonempty_of_noetherianApproximation hG
    hUqs ⟨hUlft, hUqc⟩ hRqs ⟨hRlft, hRqc⟩ h07SU
  refine ⟨G, Δ, hUqs, hRqs, ⟨e⟩, fun i h => ?_⟩
  have hsm := Δ.stageGroupoid_isSmooth i h
  have halg := isAlgebraicStack_quotientStack_of_isSmooth_unconditional.{u, w} hsm
  obtain ⟨M⟩ := nonempty_quotientStackModel (Δ.stageGroupoid i h) halg
  have hU := GroupoidInAlgebraicSpaces.LimitDescent.stageGroupoid_objects_isFinitePresentation
    (Δ := Δ) (i := i) (h := h) hUqs
  have hR := GroupoidInAlgebraicSpaces.LimitDescent.stageGroupoid_arrows_isFinitePresentation
    (Δ := Δ) (i := i) (h := h) hRqs
  have hMfp : AlgebraicStacks.IsFinitePresentation B S hS M.structureMorphism :=
    ⟨M.isLocallyOfFinitePresentation_structureMorphism halg hsm hU.1,
      M.isQuasiCompactMorphism_structureMorphism halg hU.2.1,
      M.isQuasiSeparated_structureMorphism (D.noetherian i).2.1 halg hsm hU hR⟩
  exact ⟨M, hMfp, AlgebraicStacks.isFinitePresentation_baseChange B S hS M.structureMorphism _ _
    (Bicategory.isTwoFibreProduct_swap
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS _ _)) hMfp,
    nonempty_equivalenceOver_baseChange_twoFibreProduct _ _ M.stack M.structureMorphism
      M.equivOver⟩

end

end AlgebraicGeometry.Stack

end
