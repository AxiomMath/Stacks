module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtInfinitesimalLifting
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFormallySmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.FormallySmoothOnObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.SpaceFormallySmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyComp
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityComp
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismMonotone
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjectsRelative

/-!
# A smooth 1-morphism of algebraic stacks is formally smooth on objects

A 1-morphism of algebraic stacks which is representable by algebraic spaces and smooth is
formally smooth on objects: by Stacks 06FM its base changes to algebraic spaces over objects of
the site are smooth, hence formally smooth by the implication smooth ⇒ formally smooth for
algebraic spaces, `AlgebraicGeometry.Space.formallySmooth_of_isSmooth_unconditional` (Stacks
04AM), and that is formal smoothness on objects by Stacks 06D3.

## Main results

* `AlgebraicGeometry.Stack.isFormallySmoothOnObjects_of_isSmooth_unconditional`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A 1-morphism of algebraic stacks over `S` which is representable by algebraic spaces and
passes the existential smooth-diagram test of Stacks 06FM at smoothness of morphisms of
algebraic spaces is formally smooth on objects.

By Stacks 06FM the existential test is the relative property of Stacks 03YK, so every base
change of the 1-morphism to an algebraic space over an object of the site is smooth, hence
formally smooth by Stacks 04AM; that is formal smoothness on objects by Stacks 06D3. -/
theorem isFormallySmoothOnObjects_of_isSmooth_unconditional
    {𝒜 ℬ : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (h𝒜 : IsAlgebraicStack.{u, w} B S hS 𝒜.val)
    (hℬ : IsAlgebraicStack.{u, w} B S hS ℬ.val)
    (g : 𝒜 ⟶ ℬ) (hrep : IsRepresentableByAlgebraicSpaces B S hS g.hom)
    (hg : HasPropertyOnSomeSmoothDiagram B S hS
      (fun {_ _} (q : _ ⟶ _) => Space.IsSmooth B S hS q) g) :
    IsFormallySmoothOnObjects B S hS 𝒜 ℬ g := by
  let Psm : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun {_ _} q => Space.IsSmooth B S hS q
  have _ : (spaceProperty B S hS Psm).IsStableUnderBaseChange := by
    simpa [Psm, spaceProperty] using Space.isSmooth_isStableUnderBaseChange B S hS
  have _ : (spaceProperty B S hS Psm).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) := by
    change (Space.smoothMorphismProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS)
    exact Space.smooth_isLocalAtTarget_fppf B S hS
  have hRelSmooth : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (spaceProperty B S hS Psm) g hrep :=
    (hasPropertyOnSomeSmoothDiagram_iff_relative B S hS Psm
      (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS) h𝒜 hℬ g hrep).mp hg
  refine (BigFppfOver.isFormallySmoothOnObjects_iff_isRelativelyFormallySmooth
    B S hS g hrep).mpr fun V y hy F hF hEquiv => ?_
  let Fy := (spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩
  have hqsm : Space.IsSmooth B S hS (algebraicSpaceMap B S hS V Fy).hom := by
    simpa [Fy, spaceProperty, Psm] using hRelSmooth V y hy F hF hEquiv
  exact Space.formallySmooth_of_isSmooth_unconditional Fy.property
    (isAlgebraicSpace_yoneda B S hS (Over.mk V.hom)) _ hqsm

end AlgebraicGeometry.Stack

end
