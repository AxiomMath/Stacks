module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosedSubspaceApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Order

/-!
# Finite-order stages of a thickening

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let
`G ⊆ X` be a thickening, so that `G` and `X` have the same points.  The ideal sheaf of `G` is
locally nil but need not be nilpotent, so `X` need not be a finite-order thickening of `G`.
This file records the data by which `G` is approximated from above by closed subspaces `H_i`
with `G ⊆ H_i ⊆ X`, each a *finite-order* thickening of `X`, whose ideal sheaves exhaust the
ideal sheaf of `G` on one affine surjective étale chart of `X`.

## Main definitions

* `AlgebraicGeometry.Space.ThickeningStageSystem`: a directed, antitone family of closed
  subspaces of `X`, each containing `G` and each a finite-order thickening of `X`, whose
  chartwise ideal sheaves on a fixed affine surjective étale chart have supremum the chartwise
  ideal sheaf of `G`.

## References

* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 07VS](https://stacks.math.columbia.edu/tag/07VS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Finite-order stages of a thickening `G ⊆ X`.** An affine object `V` of the site with a
surjective étale morphism `φ : h_V ⟶ X`, and a directed antitone family `stage` of closed
subspaces of `X`, each containing `G` and each a finite-order thickening of `X`, such that on the
chart `φ` the ideal sheaf of `G` is the supremum of the ideal sheaves of the stages. -/
structure ThickeningStageSystem (X : AlgebraicSpaces B S hS) (G : ClosedSubspaces B S hS X.1) where
  /-- The affine chart. -/
  V : BigFppfOver B S hS
  /-- The chart is an affine scheme. -/
  isAffine_V : IsAffine ((BigFppfOver.toScheme B S hS).obj V)
  /-- The chart morphism. -/
  φ : yoneda.obj V ⟶ X.1
  /-- The chart morphism is surjective. -/
  surjective : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ
  /-- The chart morphism is étale. -/
  etale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ
  /-- The index of the stages. -/
  I : Type u
  [preorder : Preorder I]
  [isDirected : IsDirected I (· ≤ ·)]
  [nonempty : Nonempty I]
  /-- The stages. -/
  stage : I → ClosedSubspaces B S hS X.1
  /-- The stages decrease along the index. -/
  antitone : ∀ ⦃i j : I⦄, i ≤ j → (stage j).1 ≤ (stage i).1
  /-- Each stage contains `G`. -/
  le_stage : ∀ i, G.1 ≤ (stage i).1
  /-- Each stage is a finite-order thickening of `X`. -/
  isFiniteOrderThickening : ∀ i, IsFiniteOrderThickening B S hS X (stage i).1
  /-- On the chart, the ideal sheaf of `G` is the supremum of the ideal sheaves of the stages. -/
  iSup_etaleChartKer :
    ⨆ i, etaleChartKer B S hS X (stage i) (chartOfSurjectiveEtale B S hS X etale) =
      etaleChartKer B S hS X G (chartOfSurjectiveEtale B S hS X etale)

attribute [instance] ThickeningStageSystem.preorder ThickeningStageSystem.isDirected
  ThickeningStageSystem.nonempty

end AlgebraicGeometry.Space

end
