module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentIngredients
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtalePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsoluteDMEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationFlatCoverDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationFppfDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationSmallerBaseDMAndSeparated
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationSourceOverBase

/-!
# An étale presentation of a flat base change is Deligne–Mumford (Stacks 0CIY)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`. Condition (3) of Stacks 0CIY
supplies an algebraic space `W` with a surjective, flat, locally-of-finite-presentation
1-morphism `W ⟶ 𝒴`, and an algebraic space `T` with a surjective étale 1-morphism
`T ⟶ 𝒳 ×_𝒴 W` whose induced morphism `T ⟶ W` is unramified. From this data `f` is
Deligne–Mumford, which is the first conjunct of each of conditions (1) and (2) of Stacks 0CIY.

## Main results

* `AlgebraicGeometry.Stack.hasRelativeProperty_unramified_of_isRelativelyEtale`: a 1-morphism
  étale in the relative sense of Stacks 03YK is unramified in that sense.
* `AlgebraicGeometry.Stack.isFlat_of_isRelativelyEtale` and
  `AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_of_isRelativelyEtale`: a relatively
  étale 1-morphism out of an algebraic space is flat (Stacks 06PW) and locally of finite
  presentation (Stacks 06Q2 part (1)).
* `AlgebraicGeometry.Stack.isDM_of_surjectiveEtalePresentation_flatBaseChange`: the
  Deligne–Mumford condition on `f` from condition (3) of Stacks 0CIY.

## References

* [Stacks Project, Tag 050N](https://stacks.math.columbia.edu/tag/050N)
* [Stacks Project, Tag 06CR](https://stacks.math.columbia.edu/tag/06CR)
* [Stacks Project, Tag 06FC](https://stacks.math.columbia.edu/tag/06FC)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06MB](https://stacks.math.columbia.edu/tag/06MB)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 06TZ](https://stacks.math.columbia.edu/tag/06TZ)
* [Stacks Project, Tag 0CIY](https://stacks.math.columbia.edu/tag/0CIY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A 1-morphism étale in the relative sense of Stacks 03YK is unramified in that sense. -/
theorem hasRelativeProperty_unramified_of_isRelativelyEtale
    {𝒜 ℬ : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} {g : 𝒜 ⟶ ℬ}
    (hg : IsRelativelyEtale B S hS g)
    (hgrep : IsRepresentableByAlgebraicSpaces B S hS g.hom) :
    haveI : (Space.unramifiedMorphismProperty B S hS).IsStableUnderBaseChange :=
      Space.isUnramified_isStableUnderBaseChange B S hS
    haveI : (Space.unramifiedMorphismProperty B S hS).IsLocalAtTarget
        (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
      (Space.isUnramified_isLocalAtTarget_fpqc.{u, u} B S hS).of_le
        (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
    HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.unramifiedMorphismProperty B S hS)
      g hgrep := by
  obtain ⟨-, hge⟩ := hg
  exact fun U y hy F hF he => Space.isUnramified_of_isEtale B S hS (hge U y hy F hF he)

/-- A relatively étale 1-morphism out of an algebraic space is flat in the sense of
Stacks 06PW. -/
theorem isFlat_of_isRelativelyEtale {𝒜 : AlgebraicStacks.{u, w} B S hS}
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hT : IsAlgebraicSpace B S hS T)
    (t : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒜)
    (ht : IsRelativelyEtale B S hS t.hom) :
    AlgebraicStacks.IsFlat B S hS t :=
  (AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS t).2
    (hasPropertyOnSomeSmoothDiagram_of_isRelativelySmooth B S hS _ t.hom T hT
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (isRelativelySmooth_of_isRelativelyEtale B S hS t.hom ht) (Space.isFlat_id B S hS hT))

/-- A relatively étale 1-morphism out of an algebraic space is locally of finite presentation
in the sense of Stacks 06Q2, part (1). -/
theorem isLocallyOfFinitePresentation_of_isRelativelyEtale {𝒜 : AlgebraicStacks.{u, w} B S hS}
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hT : IsAlgebraicSpace B S hS T)
    (t : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒜)
    (ht : IsRelativelyEtale B S hS t.hom) :
    AlgebraicStacks.IsLocallyOfFinitePresentation B S hS t :=
  hasPropertyOnEverySmoothDiagram_of_hasPropertyOnSomeSmoothDiagram B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS) t.hom
    (hasPropertyOnSomeSmoothDiagram_of_isRelativelySmooth B S hS _ t.hom T hT
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (isRelativelySmooth_of_isRelativelyEtale B S hS t.hom ht)
      (Space.isLocallyOfFinitePresentation_id B S hS hT))

variable (hZ : B.Contains (⊤_ Scheme.{u}))

include hZ in
/-- Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, let `W` be an algebraic space
with a surjective, flat, locally-of-finite-presentation 1-morphism `c : W ⟶ 𝒴`, and let the
2-fibre product `𝒳 ×_𝒴 W` admit a surjective étale 1-morphism from an algebraic space `T`. Then
`f` is Deligne–Mumford. -/
@[stacks 0CIY "the Deligne-Mumford condition on f, which is the first conjunct of each of parts \
(1) and (2), from part (3); the unramifiedness of T -> W asserted by part (3) is not needed for \
it, and the easy direction of Stacks 06N3 that the source cites is taken in the form \
Stacks 06MB part (1), whose absolute Deligne-Mumford conclusion asks the big site to contain \
the terminal scheme"]
theorem isDM_of_surjectiveEtalePresentation_flatBaseChange
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hW : IsAlgebraicSpace B S hS W)
    (c : algebraicSpaceStack.{u, w} B S hS W hW ⟶ 𝒴)
    (hcSurj : IsSurjective B S hS c)
    (hcFlat : AlgebraicStacks.IsFlat B S hS c)
    (hcLfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS c)
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hT : IsAlgebraicSpace B S hS T)
    (t : algebraicSpaceStack.{u, w} B S hS T hT ⟶
      (twoFibreProductSquareAlgebraicStacks B S hS f c).pt)
    (htSurj : IsSurjective B S hS t)
    (htEt : IsRelativelyEtale B S hS t.hom) :
    IsDM B S hS f := by
  have hTrep : IsRepresentableByAlgebraicSpace B S hS
      (algebraicSpaceStack.{u, w} B S hS T hT).val :=
    isRepresentableByAlgebraicSpace_fibredCategory B S hS T hT
  have habs : AlgebraicStacks.IsAbsolutelyDM.{u, w} B S hS hZ
      (twoFibreProductSquareAlgebraicStacks B S hS f c).pt :=
    AlgebraicStacks.isAbsolutelyDM_of_isUnramified_flatCover B S hS hZ t hTrep htSurj
      (isFlat_of_isRelativelyEtale.{u, w} B S hS T hT t htEt)
      (isLocallyOfFinitePresentation_of_isRelativelyEtale.{u, w} B S hS T hT t htEt)
      (hasRelativeProperty_unramified_of_isRelativelyEtale B S hS htEt _)
  exact isDM_of_isDM_baseChange B S hS f c
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS W hW) hcSurj hcFlat hcLfp
    (isDM_of_isDMOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS f c).snd
      (AlgebraicStacks.isDMOver_of_isAbsolutelyDM B S hS hZ _ habs))

end AlgebraicGeometry.Stack

end
