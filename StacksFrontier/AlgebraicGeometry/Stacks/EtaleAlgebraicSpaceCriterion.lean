module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFppfLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFpqcLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenFiltrationSeparatedNeighbourhoods
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationFlatCoverDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationFppfDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationSmallerBaseDMAndSeparated
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationSourceOverBase
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack

/-!
# Étale 1-morphisms of algebraic stacks tested on arbitrary algebraic-space charts

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over a scheme `S` contained in a big fppf
site. Consider the three conditions:

1. `f` is étale, `AlgebraicGeometry.Stack.IsEtale`;
2. `f` is Deligne–Mumford and for *every* 1-morphism `V ⟶ 𝒴` with `V` an algebraic space and
   *every* étale 1-morphism `U ⟶ V ×_𝒴 𝒳` with `U` an algebraic space, the induced morphism of
   algebraic spaces `U ⟶ V` is étale;
3. there are an algebraic space `W`, a surjective, flat, locally finitely presented 1-morphism
   `W ⟶ 𝒴`, an algebraic space `T` and a surjective étale 1-morphism `T ⟶ W ×_𝒴 𝒳` such that
   `T ⟶ W` is étale.

This file shows that condition (2) implies condition (1), and that condition (3) implies that `f`
is Deligne–Mumford.

## Main definitions

* `AlgebraicGeometry.Stack.EtaleOnEveryAlgebraicSpaceDiagram`: condition (2).
* `AlgebraicGeometry.Stack.HasEtaleAlgebraicSpaceCoverAfterFppfBaseChange`: condition (3).

## Main results

* `AlgebraicGeometry.Stack.isEtale_of_etaleOnEveryAlgebraicSpaceDiagram`: condition (2) implies
  condition (1).
* `AlgebraicGeometry.Stack.isDM_of_hasEtaleAlgebraicSpaceCoverAfterFppfBaseChange`: condition (3)
  implies that `f` is Deligne–Mumford.

## Implementation notes

Condition (2) is written in the diagram vocabulary of `AlgebraicGeometry.Stack.IsEtale`, namely
`AlgebraicGeometry.Stack.diagramCone` together with `AlgebraicGeometry.Stack.IsRelativelyEtale`
on every comparison 1-morphism into every 2-fibre product of the cospan. It is
`AlgebraicGeometry.Stack.HasPropertyOnEveryEtaleSmoothDiagram` at étaleness of morphisms of
algebraic spaces with the smoothness clause on `V ⟶ 𝒴` deleted, conjoined with the
Deligne–Mumford condition.

Condition (3) is stated at the canonical 2-fibre product
`AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks` rather than quantified over all
2-fibre products of the cospan: being an existential condition, it asks for data over one
product, and all of them are equivalent.

## References

* [Stacks Project, Tag 050N](https://stacks.math.columbia.edu/tag/050N)
* [Stacks Project, Tag 06MB](https://stacks.math.columbia.edu/tag/06MB)
* [Stacks Project, Tag 06TZ](https://stacks.math.columbia.edu/tag/06TZ)
* [Stacks Project, Tag 0CIL](https://stacks.math.columbia.edu/tag/0CIL)
* [Stacks Project, Tag 0CIQ](https://stacks.math.columbia.edu/tag/0CIQ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The condition that a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is Deligne–Mumford
and that, for every 2-commutative square of algebraic spaces over `f` whose every comparison
1-morphism into a 2-fibre product of the cospan `(b, f)` is étale, the top horizontal morphism of
algebraic spaces is étale. No smoothness is asked of the right-hand vertical 1-morphism
`b : V ⟶ 𝒴`. -/
abbrev EtaleOnEveryAlgebraicSpaceDiagram
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  IsDM B S hS f ∧
    ∀ (U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (hU : IsAlgebraicSpace B S hS U)
      (hV : IsAlgebraicSpace B S hS V)
      (a : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
      (b : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴)
      (h : U ⟶ V)
      (η : (associatedMap B S hS h).1 ≫ b.hom ≅ a.hom ≫ f.hom),
      (∀ (Q : Bicategory.TwoCommSq b.hom f.hom)
        (_hQ : Bicategory.IsTwoFibreProduct Q)
        (k : Bicategory.TwoCommSq.PreHom
          (diagramCone B S hS f.hom a.hom b.hom h η) Q),
          IsRelativelyEtale B S hS k.hom) →
      Space.IsEtale B S hS
        (ObjectProperty.homMk h : (⟨U, hU⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V, hV⟩).hom

/-- A Deligne–Mumford 1-morphism of algebraic stacks whose every algebraic-space diagram with
étale comparisons has étale top horizontal morphism is étale. -/
@[stacks 0CIQ "the implication (2) => (1)"]
theorem isEtale_of_etaleOnEveryAlgebraicSpaceDiagram
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴}
    (hf : EtaleOnEveryAlgebraicSpaceDiagram B S hS f) : IsEtale B S hS f :=
  ⟨hf.1, fun U V hU hV a b h η _hb hk => hf.2 U V hU hV a b h η hk⟩

/-- The condition that there are an algebraic space `W` over `S` and a surjective, flat, locally
finitely presented 1-morphism `g : W ⟶ 𝒴`, an algebraic space `T` over `S` and a surjective étale
1-morphism `e : T ⟶ W ×_{g, 𝒴, f} 𝒳` onto the canonical 2-fibre product, and a morphism of
algebraic spaces `h : T ⟶ W` which is étale and which `e` followed by the projection to `W`
induces. Étaleness of `e` is `AlgebraicGeometry.Stack.IsRelativelyEtale`. -/
abbrev HasEtaleAlgebraicSpaceCoverAfterFppfBaseChange
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∃ (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hW : IsAlgebraicSpace B S hS W)
    (g : algebraicSpaceStack.{u, w} B S hS W hW ⟶ 𝒴)
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hT : IsAlgebraicSpace B S hS T)
    (e : algebraicSpaceStack.{u, w} B S hS T hT ⟶
      (twoFibreProductSquareAlgebraicStacks B S hS f g).pt)
    (h : T ⟶ W),
    IsSurjective B S hS g ∧
      AlgebraicStacks.IsFlat B S hS g ∧
      AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g ∧
      IsSurjective B S hS e ∧
      IsRelativelyEtale B S hS e.hom ∧
      Nonempty ((associatedMap B S hS h).1 ≅
        e.hom ≫ (twoFibreProductSquareAlgebraicStacks B S hS f g).snd.hom) ∧
      Space.IsEtale B S hS h

/-- If the big fppf site contains the terminal scheme, a 1-morphism `f` of algebraic stacks
satisfying `AlgebraicGeometry.Stack.HasEtaleAlgebraicSpaceCoverAfterFppfBaseChange` is
Deligne–Mumford. -/
@[stacks 0CIQ "the Deligne-Mumford half of the implication (3) => (1), for a site
containing the terminal scheme"]
theorem isDM_of_hasEtaleAlgebraicSpaceCoverAfterFppfBaseChange
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴}
    (hf : HasEtaleAlgebraicSpaceCoverAfterFppfBaseChange B S hS f) : IsDM B S hS f := by
  obtain ⟨W, hW, g, T, hT, e, h, hgSurj, hgFlat, hgLfp, heSurj, ⟨-, hetale⟩, -, -⟩ := hf
  have hflatBC := Space.isFlat_isStableUnderBaseChange B S hS
  have hflatLT := (Space.isFlat_isLocalAtTarget_fpqc.{u, u} B S hS).of_le
    (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  have hlfpBC := Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  have hlfpLT := Space.isLocallyOfFinitePresentation_isLocalAtTarget_fppf.{u, u} B S hS
  have hunrBC := Space.isUnramified_isStableUnderBaseChange B S hS
  have hunrLT := (Space.isUnramified_isLocalAtTarget_fpqc.{u, u} B S hS).of_le
    (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  have hTrep : IsRepresentableByAlgebraicSpace B S hS
      (algebraicSpaceStack.{u, w} B S hS T hT).val :=
    isRepresentableByAlgebraicSpace_fibredCategory B S hS T hT
  have herep := isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS f g).pt.property hTrep e.hom
  have hsome : ∀ (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
      [(spaceProperty B S hS P).IsStableUnderBaseChange]
      [(spaceProperty B S hS P).IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)],
      (∀ {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : X ⟶ Y), Space.IsEtale B S hS k → P k) →
      HasPropertyOnSomeSmoothDiagram B S hS P e.hom :=
    fun P _ _ hP => hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS P
      (twoFibreProductSquareAlgebraicStacks B S hS f g).pt.property e.hom herep
      (fun U y hy F hF hne => hP _ (hetale U y hy F hF hne))
  have heFlat : AlgebraicStacks.IsFlat B S hS e :=
    (AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram.{u, w} B S hS e).2
      (hsome (fun _ _ k => Space.IsFlat B S hS k) fun k => Space.isFlat_of_isEtale B S hS)
  have heLfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS e :=
    hasPropertyOnEverySmoothDiagram_of_hasPropertyOnSomeSmoothDiagram B S hS
      (fun _ _ k => Space.IsLocallyOfFinitePresentation B S hS k)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS) e.hom
      (hsome (fun _ _ k => Space.IsLocallyOfFinitePresentation B S hS k)
        fun k => Space.isLocallyOfFinitePresentation_of_isEtale B S hS)
  have hpt : AlgebraicStacks.IsAbsolutelyDM.{u, w} B S hS hZ
      (twoFibreProductSquareAlgebraicStacks B S hS f g).pt :=
    AlgebraicStacks.isAbsolutelyDM_of_isUnramified_flatCover.{u, w} B S hS hZ e hTrep
      heSurj heFlat heLfp
      (fun U y hy F hF hne => Space.isUnramified_of_isEtale B S hS (hetale U y hy F hF hne))
  have hsnd : IsDM B S hS (twoFibreProductSquareAlgebraicStacks B S hS f g).snd :=
    isDM_of_isDMOver B S hS _
      (AlgebraicStacks.isDMOver_of_isAbsolutelyDM.{u, w} B S hS hZ _ hpt)
  exact isDM_of_isDM_baseChange B S hS f g
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS W hW) hgSurj hgFlat hgLfp hsnd

end AlgebraicGeometry.Stack

end
