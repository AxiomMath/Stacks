module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackToBaseAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackFromSmallModel
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus

/-!
# `𝒮_T` for a scheme `T` of the site is the stack of `T`

`AlgebraicGeometry.Space.baseAlgebraicStackSmallModel` presents the category `𝒮_Y` of test
schemes over an algebraic space `Y` as an object of the 2-category of algebraic stacks of
**Stacks 03YP**. For `Y` the algebraic space of a scheme `T` of the site, `𝒮_T` is the slice of
the site over `T`, which is already an object of that 2-category: it is
`AlgebraicGeometry.Stack.schemeStack`.

The identification of the two is `AlgebraicGeometry.Space.baseToSlice`, the composite of the
Yoneda lemma with the identification of the elements of a representable presheaf with the slice;
this file reads it as a 1-morphism of algebraic stacks out of the small model
(`AlgebraicGeometry.Stack.AlgebraicStacks.fromSmallModel`) and records that it is an equivalence.

This is what lets a 1-morphism *to* `𝒮_T` be compared with a 1-morphism to the stack of `T`. The
structure morphism of the Picard stack of a family of curves over a scheme `T`,
`AlgebraicGeometry.Space.picardToBaseAlgebraic`, goes to `𝒮_T`; the smoothness clause of
**Stacks 0DQ0** is about 1-morphisms to `Stack.schemeStack T`, the base change along a scheme
chart of the stack of curves. Smoothness in the sense of **Stacks 075U** is invariant under an
equivalence on the left
(`AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_of_isEquivalence_comp`), so composing with the
equivalence below moves a smoothness statement from one target to the other.

No tag is registered: nothing here is a statement of the source.

## Main definitions

* `AlgebraicGeometry.Space.baseAlgebraicStackToSchemeStack`: the 1-morphism of algebraic stacks
  `𝒮_T ⟶ (Sch/T)`.

## Main results

* `AlgebraicGeometry.Space.isEquivalence_baseAlgebraicStackToSchemeStack`: it is an equivalence of
  the underlying categories.
* `AlgebraicGeometry.Space.isSmooth_comp_baseAlgebraicStackToSchemeStack` and
  `AlgebraicGeometry.Space.isSmooth_of_isSmooth_comp_baseAlgebraicStackToSchemeStack`: smoothness
  of a 1-morphism to `𝒮_T` and of its composite with the equivalence are the same thing.

## References

* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
* [Stacks Project, Tag 0DQ0](https://stacks.math.columbia.edu/tag/0DQ0)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (T : BigFppfOver B S hS)

/-- **The 1-morphism of algebraic stacks `𝒮_T ⟶ (Sch/T)`** for a scheme `T` of the site: the
identification `AlgebraicGeometry.Space.baseToSlice` of the test schemes over `T` with the slice
of the site over `T`, read out of the small model. -/
def baseAlgebraicStackToSchemeStack :
    baseAlgebraicStackSmallModel.{u, w} (schemeSpace T) ⟶ Stack.schemeStack.{u, w} B S hS T :=
  Stack.AlgebraicStacks.fromSmallModel B S hS (isAlgebraicStack_baseCFG.{u, w} (schemeSpace T))
    (Stack.schemeStack.{u, w} B S hS T) baseToSlice

/-- **The 1-morphism `𝒮_T ⟶ (Sch/T)` is an equivalence**: `AlgebraicGeometry.Space.baseToSlice`
is one, and the comparison out of a small model is one. -/
theorem isEquivalence_baseAlgebraicStackToSchemeStack :
    Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor
      (baseAlgebraicStackToSchemeStack.{u, w} B S hS T).hom) :=
  Stack.AlgebraicStacks.isEquivalence_fromSmallModel B S hS
    (isAlgebraicStack_baseCFG.{u, w} (schemeSpace T)) (Stack.schemeStack.{u, w} B S hS T)
    baseToSlice (baseToSlice_isEquivalence (T := T))

variable {𝒟 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- A 1-morphism to `𝒮_T` is smooth exactly when its composite with the equivalence
`𝒮_T ⟶ (Sch/T)` is, this direction being invariance of smoothness under a 2-isomorphism after
cancelling the equivalence on the right. -/
theorem isSmooth_comp_baseAlgebraicStackToSchemeStack
    (q : 𝒟 ⟶ baseAlgebraicStackSmallModel.{u, w} (schemeSpace T))
    (hq : Stack.AlgebraicStacks.IsSmooth B S hS q) :
    Stack.AlgebraicStacks.IsSmooth B S hS (q ≫ baseAlgebraicStackToSchemeStack.{u, w} B S hS T) :=
  Stack.AlgebraicStacks.isSmooth_comp B S hS q _ hq
    (Stack.AlgebraicStacks.isSmooth_of_isEquivalence B S hS _
      (isEquivalence_baseAlgebraicStackToSchemeStack.{u, w} B S hS T))

/-- The converse: smoothness of a 1-morphism to `(Sch/T)` which factors through `𝒮_T` gives
smoothness of the factor, by
`AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_of_comp_isEquivalence` (**Stacks 003Z**). -/
theorem isSmooth_of_isSmooth_comp_baseAlgebraicStackToSchemeStack
    (q : 𝒟 ⟶ baseAlgebraicStackSmallModel.{u, w} (schemeSpace T))
    (hq : Stack.AlgebraicStacks.IsSmooth B S hS
      (q ≫ baseAlgebraicStackToSchemeStack.{u, w} B S hS T)) :
    Stack.AlgebraicStacks.IsSmooth B S hS q :=
  Stack.AlgebraicStacks.isSmooth_of_comp_isEquivalence B S hS q _
    (isEquivalence_baseAlgebraicStackToSchemeStack.{u, w} B S hS T) hq

end AlgebraicGeometry.Space

end
