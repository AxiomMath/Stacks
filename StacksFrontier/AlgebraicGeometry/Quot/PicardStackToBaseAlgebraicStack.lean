module

public import StacksFrontier.AlgebraicGeometry.Quot.BaseBasedCategoryElements
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackAlgebraic
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackToBase
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackSmallModelHom
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStack

/-!
# `Picardstack_{X/B} ⟶ 𝒮_B` as a 1-morphism of algebraic stacks

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` of a big fppf site, the
standing data of Stacks 0D25, and let `Picardstack_{X/B}` be the Picard stack of Section 0372.
Its structure morphism to the test schemes over the base, `AlgebraicGeometry.Space.picardToBase`,
is a 1-morphism of categories fibred in groupoids whose hom types live in the universe `u + 1`,
one above the schemes of the site. The 2-category of algebraic stacks of Stacks 03YP is formed at
the universes of the site, so neither `Picardstack_{X/B}` nor `𝒮_B` is an object of it and the
structure morphism is not a 1-morphism of it.

Consequently a statement such as Stacks 0DPJ — `Picardstack_{X/B} ⟶ B` is smooth, smoothness
being `AlgebraicGeometry.Stack.AlgebraicStacks.IsSmooth` of Stacks 075U, which is defined only
for 1-morphisms of `AlgebraicGeometry.Stack.AlgebraicStacks` — could not be written down at all.

This file removes the obstruction with `AlgebraicGeometry.Stack.AlgebraicStacks.smallModel` of
`StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackSmallModel`, which presents an algebraic
stack with large hom types as an object of the 2-category of Stacks 03YP, and with
`AlgebraicGeometry.Stack.AlgebraicStacks.smallModelHom`, which does the same for a 1-morphism.
Both categories are brought down:

* `𝒮_B` needs no hypothesis. It is equivalent over the site to the category of elements of the
  algebraic space `B` (`AlgebraicGeometry.Space.baseBasedElementsEquivalenceOver`, the Yoneda
  lemma), which is an algebraic stack by
  `AlgebraicGeometry.Stack.isAlgebraicStack_fibredCategory`, so `𝒮_B` is one too.
* `Picardstack_{X/B}` needs its algebraicity, which is **Stacks 0D04**, taken as the
  hypothesis `h0D04` in the shape that
  `AlgebraicGeometry.Space.isAlgebraicStack_picardCFG_of_h09DS` produces from the statement of
  **Stacks 09DS**. The definitions staged on Stacks 09DS below take that `h09DS` hypothesis
  instead.

## Main definitions

* `AlgebraicGeometry.Space.baseAlgebraicStackSmallModel`: `𝒮_Y` as an object of the 2-category
  of algebraic stacks of Stacks 03YP, with hom types in the universe of the schemes.
* `AlgebraicGeometry.Space.picardAlgebraicStackOfPicardSituation`: `Picardstack_{X/B}` as an
  object of the same 2-category, given the statement of Stacks 0D04 as the binder `h0D04`.
* `AlgebraicGeometry.Space.picardToBaseAlgebraic`: the structure morphism
  `Picardstack_{X/B} ⟶ 𝒮_B` as a 1-morphism of algebraic stacks. This is the 1-morphism a
  Stacks 0DPJ binder is about.
* `AlgebraicGeometry.Space.picardAlgebraicStackOfCoherentSituation` and
  `AlgebraicGeometry.Space.picardToBaseAlgebraicOfCoherentSituation`: the same two, staged on the
  statement of Stacks 09DS rather than on Stacks 0D04.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicStack_baseCFG`: `𝒮_Y` is an algebraic stack, with no
  hypothesis.
* `AlgebraicGeometry.Space`
  `.hasPropertyOnSomeSmoothDiagram_isLocallyOfFinitePresentation_picardToBaseAlgebraic`
  : given Stacks 0DPJ as the binder `h0DPJ`, the structure morphism passes the existential
  smooth-diagram test of Stacks 06FM at local finite presentation.

## References

* [Stacks Project, Tag 0372](https://stacks.math.columbia.edu/tag/0372)
* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
* [Stacks Project, Tag 09DS](https://stacks.math.columbia.edu/tag/09DS)
* [Stacks Project, Tag 0D04](https://stacks.math.columbia.edu/tag/0D04)
* [Stacks Project, Tag 0D25](https://stacks.math.columbia.edu/tag/0D25)
* [Stacks Project, Section 0DM9](https://stacks.math.columbia.edu/tag/0DM9)
* [Stacks Project, Tag 0DPJ](https://stacks.math.columbia.edu/tag/0DPJ)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **`𝒮_Y` is an algebraic stack**, with no hypothesis: the Yoneda lemma identifies it over the
site with the category of elements of the algebraic space `Y`
(`AlgebraicGeometry.Space.baseBasedElementsEquivalenceOver`), which is an algebraic stack by
`AlgebraicGeometry.Stack.isAlgebraicStack_fibredCategory`, and algebraicity transports along an
equivalence over the site (Stacks 03YQ in independent universes). -/
theorem isAlgebraicStack_baseCFG (Y : AlgebraicSpaces B S hS) :
    Stack.IsAlgebraicStack.{u, w} B S hS (baseCFG Y).val :=
  Stack.isAlgebraicStack_of_equivalenceOver B S hS (baseBasedElementsEquivalenceOver Y).symm
    (Stack.isAlgebraicStack_fibredCategory.{u, w} B S hS Y.obj Y.2)

/-- **`𝒮_Y` as an object of the 2-category of algebraic stacks of Stacks 03YP**: the small model
of `AlgebraicGeometry.Space.baseCFG`, whose hom types lie in the universe of the schemes. -/
def baseAlgebraicStackSmallModel (Y : AlgebraicSpaces B S hS) :
    Stack.AlgebraicStacks.{u, w} B S hS :=
  Stack.AlgebraicStacks.smallModel B S hS (baseCFG Y).val (isAlgebraicStack_baseCFG.{u, w} Y)

/-- **`Picardstack_{X/B}` as an object of the 2-category of algebraic stacks of Stacks 03YP**: the
small model of `AlgebraicGeometry.Space.picardCFG`, whose hom types lie in the universe of the
schemes.

The binder `h0D04` is the statement of **Stacks 0D04**, that the Picard stack is an algebraic
stack. -/
def picardAlgebraicStackOfPicardSituation (hc : ModulePushforwardCoherence B S hS)
    (s : PicardSituation B S hS)
    (h0D04 : Stack.IsAlgebraicStack.{u, w} B S hS (picardCFG hc s).val) :
    Stack.AlgebraicStacks.{u, w} B S hS :=
  Stack.AlgebraicStacks.smallModel B S hS (picardCFG hc s).val h0D04

/-- **The structure morphism `Picardstack_{X/B} ⟶ 𝒮_B` as a 1-morphism of algebraic stacks**: the
small model of `AlgebraicGeometry.Space.picardToBase`, which forgets the invertible module.

This is the 1-morphism of Section 0DM9 that **Stacks 0DPJ** calls smooth; its smoothness in the
sense of Stacks 075U is `AlgebraicGeometry.Stack.AlgebraicStacks.IsSmooth B S hS` of this
1-morphism, which is the statement a Stacks 0DPJ binder carries. -/
def picardToBaseAlgebraic (hc : ModulePushforwardCoherence B S hS) (s : PicardSituation B S hS)
    (h0D04 : Stack.IsAlgebraicStack.{u, w} B S hS (picardCFG hc s).val) :
    picardAlgebraicStackOfPicardSituation hc s h0D04 ⟶ baseAlgebraicStackSmallModel.{u, w} s.base :=
  Stack.AlgebraicStacks.smallModelHom B S hS h0D04 (isAlgebraicStack_baseCFG.{u, w} s.base)
    (picardToBase hc s).hom

/-- **`Picardstack_{X/Y}` as an object of the 2-category of algebraic stacks of Stacks 03YP,
staged on Stacks 09DS.** Let `f : X ⟶ Y` be flat, of finite presentation (the standing data `D`
of Situation 08KB) and proper. The binder `h09DS` is the statement of **Stacks 09DS**, from which
`AlgebraicGeometry.Space.isAlgebraicStack_picardCFG_of_h09DS` supplies Stacks 0D04. -/
def picardAlgebraicStackOfCoherentSituation
    (h09DS : ∀ D' : CoherentSituation B S hS, IsSeparated B S hS D'.f.hom →
      Stack.IsAlgebraicStack.{u, w} B S hS (coherentCFG D').val)
    (D : CoherentSituation B S hS) (hflat : IsFlat B S hS D.f.hom)
    (hproper : IsProper B S hS D.f.hom) :
    Stack.AlgebraicStacks.{u, w} B S hS :=
  picardAlgebraicStackOfPicardSituation (modulePushforwardCoherence B S hS) D.toPicardSituation
    (isAlgebraicStack_picardCFG_of_h09DS h09DS D hflat hproper)

/-- **The structure morphism `Picardstack_{X/Y} ⟶ 𝒮_Y` as a 1-morphism of algebraic stacks,
staged on Stacks 09DS.** The binder `h09DS` is the statement of **Stacks 09DS**; see
`AlgebraicGeometry.Space.picardToBaseAlgebraic`. -/
def picardToBaseAlgebraicOfCoherentSituation
    (h09DS : ∀ D' : CoherentSituation B S hS, IsSeparated B S hS D'.f.hom →
      Stack.IsAlgebraicStack.{u, w} B S hS (coherentCFG D').val)
    (D : CoherentSituation B S hS) (hflat : IsFlat B S hS D.f.hom)
    (hproper : IsProper B S hS D.f.hom) :
    picardAlgebraicStackOfCoherentSituation h09DS D hflat hproper ⟶
      baseAlgebraicStackSmallModel.{u, w} D.toPicardSituation.base :=
  picardToBaseAlgebraic (modulePushforwardCoherence B S hS) D.toPicardSituation
    (isAlgebraicStack_picardCFG_of_h09DS h09DS D hflat hproper)

/-- **A smooth structure morphism of the Picard stack passes the existential smooth-diagram test
of Stacks 06FM at local finite presentation of morphisms of algebraic spaces.**

The binder `h0DPJ` is the statement of **Stacks 0DPJ** about the 1-morphism
`AlgebraicGeometry.Space.picardToBaseAlgebraic`; the conclusion follows from it by
`AlgebraicGeometry.Stack.AlgebraicStacks`
`.hasPropertyOnSomeSmoothDiagram_isLocallyOfFinitePresentation_of_isSmooth` alone. -/
theorem hasPropertyOnSomeSmoothDiagram_isLocallyOfFinitePresentation_picardToBaseAlgebraic
    (hc : ModulePushforwardCoherence B S hS) (s : PicardSituation B S hS)
    (h0D04 : Stack.IsAlgebraicStack.{u, w} B S hS (picardCFG hc s).val)
    (h0DPJ : Stack.AlgebraicStacks.IsSmooth B S hS (picardToBaseAlgebraic hc s h0D04)) :
    Stack.HasPropertyOnSomeSmoothDiagram B S hS
      (fun _ _ h => IsLocallyOfFinitePresentation B S hS h)
      (picardToBaseAlgebraic hc s h0D04).hom :=
  Stack.AlgebraicStacks.hasPropertyOnSomeSmoothDiagram_isLocallyOfFinitePresentation_of_isSmooth
    B S hS h0DPJ

end AlgebraicGeometry.Space

end
