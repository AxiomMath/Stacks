module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackSmoothOfAlgebraic
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackToBaseAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackFromSmallModel
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus

/-!
# The two readings of `Picardstack_{X/Y} ⟶ Y` as a 1-morphism of algebraic stacks

The structure morphism `Picardstack_{X/Y} ⟶ 𝒮_Y` has hom types one universe above the schemes
of the site, so it is read as a 1-morphism of the 2-category of algebraic stacks by shrinking the
hom types of its source; its target may then be taken to be either of two objects of that
2-category:

* `AlgebraicGeometry.Space.baseAlgebraicStackSmallModel`, the small model of `𝒮_Y`, which is the
  target of `AlgebraicGeometry.Space.picardToBaseAlgebraic`; or
* `AlgebraicGeometry.Space.baseAlgebraicStack`, the category of elements of the algebraic space
  `Y`, which is the target of `AlgebraicGeometry.Space.picardStructureMorphism`.

The Yoneda lemma identifies the two (`AlgebraicGeometry.Space.baseToElements`), and this
identification takes one 1-morphism to the other on the nose. Consequently smoothness of either
is smoothness of the other.

## Main definitions

* `AlgebraicGeometry.Space.baseAlgebraicStackToElements`: the Yoneda identification of the small
  model of `𝒮_Y` with the category of elements of `Y`, as a 1-morphism of algebraic stacks.

## Main results

* `AlgebraicGeometry.Space.isEquivalence_baseAlgebraicStackToElements`: it is an equivalence.
* `AlgebraicGeometry.Space.picardToBaseAlgebraic_comp_baseAlgebraicStackToElements`: the two
  readings of the structure morphism agree through it.
* `AlgebraicGeometry.Space.isSmooth_picardToBaseAlgebraic_of_isSmooth_picardStructureMorphism`:
  smoothness transfers from the second reading to the first.

## References

* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
* [Stacks Project, Section 0DM9](https://stacks.math.columbia.edu/tag/0DM9)
* [Stacks Project, Tag 0DPJ](https://stacks.math.columbia.edu/tag/0DPJ)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The Yoneda identification `AlgebraicGeometry.Space.baseToElements` of `𝒮_Y` with the
category of elements of `Y`, read as a 1-morphism of algebraic stacks out of the small model of
`𝒮_Y`. -/
def baseAlgebraicStackToElements (Y : AlgebraicSpaces B S hS) :
    baseAlgebraicStackSmallModel.{u, w} Y ⟶ baseAlgebraicStack.{u, w} Y :=
  Stack.AlgebraicStacks.fromSmallModel B S hS (isAlgebraicStack_baseCFG.{u, w} Y)
    (baseAlgebraicStack.{u, w} Y) (baseToElements Y)

/-- The Yoneda identification `baseAlgebraicStackToElements Y` is an equivalence. -/
theorem isEquivalence_baseAlgebraicStackToElements (Y : AlgebraicSpaces B S hS) :
    Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor
      (baseAlgebraicStackToElements.{u, w} Y).hom) :=
  Stack.AlgebraicStacks.isEquivalence_fromSmallModel B S hS (isAlgebraicStack_baseCFG.{u, w} Y)
    (baseAlgebraicStack.{u, w} Y) (baseToElements Y) (baseToElements_isEquivalence Y)

/-- **The two readings of the structure morphism `Picardstack_{X/Y} ⟶ Y` agree.** Composing
`AlgebraicGeometry.Space.picardToBaseAlgebraic`, whose target is the small model of `𝒮_Y`, with
the Yoneda identification gives `AlgebraicGeometry.Space.picardStructureMorphism`, whose target
is the category of elements of `Y`. -/
theorem picardToBaseAlgebraic_comp_baseAlgebraicStackToElements (D : CoherentSituation B S hS)
    (h0D04 : Stack.IsAlgebraicStack.{u, w} B S hS
      (picardCFG (modulePushforwardCoherence B S hS) D.toPicardSituation).val) :
    picardToBaseAlgebraic.{u, w} (modulePushforwardCoherence B S hS) D.toPicardSituation h0D04 ≫
        baseAlgebraicStackToElements.{u, w} D.Y =
      picardStructureMorphism D h0D04 := by
  apply Bicategory.InducedBicategory.hom_ext
  apply Bicategory.InducedBicategory.hom_ext
  apply BasedCategory.BasedFunctor.ext'
  exact congrArg (fun F => F ⋙ (baseToElements D.Y).toFunctor)
    (Stack.AlgebraicStacks.smallModelHom_toFunctor_comp_shrinkHoms_inverse B S hS h0D04
      (isAlgebraicStack_baseCFG.{u, w} D.Y)
      (picardToBase (modulePushforwardCoherence B S hS) D.toPicardSituation).hom)

/-- If the structure morphism `AlgebraicGeometry.Space.picardStructureMorphism` of the Picard
stack is smooth, then so is `AlgebraicGeometry.Space.picardToBaseAlgebraic`, its reading with
target the small model of `𝒮_Y`. -/
theorem isSmooth_picardToBaseAlgebraic_of_isSmooth_picardStructureMorphism
    (D : CoherentSituation B S hS)
    (h0D04 : Stack.IsAlgebraicStack.{u, w} B S hS
      (picardCFG (modulePushforwardCoherence B S hS) D.toPicardSituation).val)
    (h : Stack.AlgebraicStacks.IsSmooth B S hS (picardStructureMorphism D h0D04)) :
    Stack.AlgebraicStacks.IsSmooth B S hS
      (picardToBaseAlgebraic.{u, w} (modulePushforwardCoherence B S hS) D.toPicardSituation
        h0D04) :=
  Stack.AlgebraicStacks.isSmooth_of_comp_isEquivalence B S hS _
    (baseAlgebraicStackToElements.{u, w} D.Y)
    (isEquivalence_baseAlgebraicStackToElements.{u, w} D.Y)
    (by rw [picardToBaseAlgebraic_comp_baseAlgebraicStackToElements D h0D04]; exact h)

end AlgebraicGeometry.Space

end
