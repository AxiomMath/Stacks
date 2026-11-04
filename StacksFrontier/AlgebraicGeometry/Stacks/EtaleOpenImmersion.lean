module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalUnramified
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.CategoryTheory.TwoFibreProduct.AbstractCancelSnd
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids

/-!
# An open immersion of algebraic stacks is étale (Stacks 0CIP)

An open immersion of algebraic stacks over `S` is representable by algebraic spaces, hence
Deligne–Mumford, and its base change along any 1-morphism from an algebraic space is again an
open immersion, hence étale. That is enough to pass the universal étale-smooth diagram test of
**Stacks 0CIF** at étaleness, so the open immersion is étale in the sense of **Stacks 0CIL**.

## Main results

* `AlgebraicGeometry.Stack.isRelativelyEtale_of_isOpenImmersion`: a 1-morphism of categories
  fibred in groupoids which is an open immersion in the sense of Stacks 04XB is étale in the
  sense of Stacks 04XB.
* `AlgebraicGeometry.Stack.hasPropertyOnEveryEtaleSmoothDiagram_isEtale_of_isRelativelyEtale`:
  a 1-morphism of algebraic stacks which is étale in the sense of Stacks 04XB passes the
  universal étale-smooth diagram test at étaleness of morphisms of algebraic spaces.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isEtale_of_isRelativelyEtale`: such a 1-morphism is
  étale in the sense of Stacks 0CIL.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isEtale_of_isOpenImmersion`: an open immersion of
  algebraic stacks is étale.

## Implementation notes

The universal étale-smooth diagram test of Stacks 0CIF is verified directly on an arbitrary
diagram, through the canonical 2-fibre product and the strict comparison
`CategoryTheory.CatFiberedInGroupoids.canonicalPreHom`. This needs no étale-smooth locality of
étaleness (Stacks 0CG3), which the library does not carry.

## References

* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 03FT](https://stacks.math.columbia.edu/tag/03FT)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 050E](https://stacks.math.columbia.edu/tag/050E)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
* [Stacks Project, Tag 0CIL](https://stacks.math.columbia.edu/tag/0CIL)
* [Stacks Project, Tag 0CIP](https://stacks.math.columbia.edu/tag/0CIP)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u w

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

end Space

namespace Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A 1-morphism of categories fibred in groupoids over the big fppf site of `S` which is
representable by algebraic spaces and is an open immersion in the sense of **Stacks 04XB** is
étale in the sense of Stacks 04XB. -/
theorem isRelativelyEtale_of_isOpenImmersion
    {𝒜 ℬ : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (g : 𝒜 ⟶ ℬ)
    (hgrep : IsRepresentableByAlgebraicSpaces B S hS g.hom)
    (hg : IsOpenImmersion B S hS g) :
    IsRelativelyEtale B S hS g :=
  ⟨hgrep, fun U y hy F hF he => Space.isEtale_of_isOpenImmersion B S hS (hg U y hy F hF he)⟩

/-- **A 1-morphism of algebraic stacks étale in the sense of Stacks 04XB passes condition (1) of
Stacks 0CIF at étaleness.** For every diagram of algebraic spaces over `f : 𝒳 ⟶ 𝒴` whose every
comparison 1-morphism from its cone to a 2-fibre product of `(b, f)` is étale, the top
horizontal morphism of algebraic spaces is étale. -/
theorem hasPropertyOnEveryEtaleSmoothDiagram_isEtale_of_isRelativelyEtale
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRelativelyEtale B S hS f.hom) :
    HasPropertyOnEveryEtaleSmoothDiagram B S hS
      (fun {_ _} (g : _ ⟶ _) => Space.IsEtale B S hS g.hom :
        MorphismProperty (AlgebraicSpaces B S hS)) f := by
  obtain ⟨hfrep, -⟩ := id hf
  intro U V hU hV a b h η _hb hcompar
  set Q : Bicategory.TwoCommSq b.hom f.hom :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b.hom f.hom
  have hQ : Bicategory.IsTwoFibreProduct Q :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      b.hom f.hom
  set k : Bicategory.TwoCommSq.PreHom (diagramCone B S hS f.hom a.hom b.hom h η) Q :=
    CatFiberedInGroupoids.canonicalPreHom.{u, u, u + 1, u + 1} b.hom f.hom
      (diagramCone B S hS f.hom a.hom b.hom h η)
  have hket : IsRelativelyEtale B S hS k.hom := hcompar Q hQ k
  obtain ⟨hkrep, -⟩ := id hket
  have hQfst : IsRelativelyEtale B S hS Q.fst :=
    isRelativelyEtale_baseChange B S hS 𝒳.val 𝒴.val (fibredCategory B S hS V)
      f.hom b.hom Q hQ hf
  obtain ⟨hQfstrep, -⟩ := id hQfst
  obtain ⟨W, hW, ⟨eW⟩⟩ : IsRepresentableByAlgebraicSpace B S hS Q.pt :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
      𝒳.val 𝒴.val (fibredCategory B S hS V) f.hom b.hom Q hQ hfrep
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS V hV)
  have hkEt : Space.IsEtale B S hS
      (representingMap B S hS (fibredCategory B S hS U) Q.pt U W
        (StacksRepresentableCFG.EquivalenceOver.refl _) eW k.hom) :=
    isEtale_representingMap_of_isRelativelyEtale B S hS k.hom hkrep U W hU hW
      (StacksRepresentableCFG.EquivalenceOver.refl _) eW hket
  have hQEt : Space.IsEtale B S hS
      (representingMap B S hS Q.pt (fibredCategory B S hS V) W V eW
        (StacksRepresentableCFG.EquivalenceOver.refl _) Q.fst) :=
    isEtale_representingMap_of_isRelativelyEtale B S hS Q.fst hQfstrep W V hW hV eW
      (StacksRepresentableCFG.EquivalenceOver.refl _) hQfst
  have hkQ : k.hom ≫ Q.fst = (associatedMap B S hS h).1 := rfl
  have hsplit : h =
      representingMap B S hS (fibredCategory B S hS U) Q.pt U W
          (StacksRepresentableCFG.EquivalenceOver.refl _) eW k.hom ≫
        representingMap B S hS Q.pt (fibredCategory B S hS V) W V eW
          (StacksRepresentableCFG.EquivalenceOver.refl _) Q.fst := by
    rw [← representingMap_comp B S hS U W V (StacksRepresentableCFG.EquivalenceOver.refl _) eW
      (StacksRepresentableCFG.EquivalenceOver.refl _) k.hom Q.fst, hkQ,
      representingMap_associatedMap B S hS U V h]
  change Space.IsEtale B S hS h
  rw [hsplit]
  exact Space.isEtale_comp B S hS hkEt hQEt

namespace AlgebraicStacks

variable {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **A 1-morphism of algebraic stacks over `S` which is representable by algebraic spaces and
étale in the sense of Stacks 04XB is étale in the sense of Stacks 0CIL.** -/
theorem isEtale_of_isRelativelyEtale (f : 𝒳 ⟶ 𝒴)
    (hf : Stack.IsRelativelyEtale B S hS f.hom) :
    Stack.IsEtale B S hS f := by
  obtain ⟨hfrep, -⟩ := id hf
  exact ⟨Stack.isUnramified_relativeDiagonal_of_isRepresentableByAlgebraicSpaces B S hS f hfrep,
    Stack.hasPropertyOnEveryEtaleSmoothDiagram_isEtale_of_isRelativelyEtale B S hS f hf⟩

/-- An open immersion of algebraic stacks over `S` is étale in the sense of Stacks 0CIL. -/
@[stacks 0CIP]
theorem isEtale_of_isOpenImmersion (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicStacks.IsOpenImmersion B S hS f) :
    Stack.IsEtale B S hS f :=
  isEtale_of_isRelativelyEtale B S hS f
    (Stack.isRelativelyEtale_of_isOpenImmersion B S hS f.hom hf.1 hf.2)

end AlgebraicStacks

end Stack

end AlgebraicGeometry

end
