module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingMorphismObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingObjectsFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingOfFinitePresentation

/-!
# Limit preservation and local finite presentation for algebraic stacks (Stacks 0CMY)

For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over a scheme `S`, **Stacks 0CMY** says that the
following are equivalent:

1. `f` is limit preserving (Stacks 0CMR);
2. `f` is limit preserving on objects (Stacks 06CU);
3. `f` is locally of finite presentation (Stacks 06Q2).

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isLimitPreserving_tfae`: limit preservation, limit
  preservation on objects and local finite presentation are equivalent.

## Implementation notes

Names written without a namespace below live in `AlgebraicGeometry.Stack.AlgebraicStacks`.

* (1) ⟹ (2) is Stacks 0CMS,
  `AlgebraicGeometry.Stack.isLimitPreservingOnObjects_of_isLimitPreserving`.
* (2) ⟹ (3) is `isLocallyOfFinitePresentation_of_isLimitPreservingOnObjects`: the base change of
  `f` to a smooth atlas of `𝒴`, composed with a smooth atlas of the fibre product, is limit
  preserving on objects by Stacks 06CV and Stacks 06CW, hence locally of finite presentation by
  Stacks 06CX.
* (3) ⟹ (1): limit preservation on objects of `f` is
  `isLimitPreservingOnObjects_of_isLocallyOfFinitePresentation`, the descent of an object over an
  affine inverse limit along an atlas (Stacks 0CMX). The relative diagonal of `f` is locally of
  finite presentation by Stacks 0CMG, so it and its own diagonal are limit preserving on objects
  by Stacks 06CX, and `isLimitPreserving_of_isLimitPreservingOnObjects` turns these three facts
  into limit preservation of `f` through Stacks 0CMW.

Index categories are taken in the universe of the schemes, the size at which Stacks 06CX is
available.

## References

* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
* [Stacks Project, Tag 0CMR](https://stacks.math.columbia.edu/tag/0CMR)
* [Stacks Project, Tag 0CMS](https://stacks.math.columbia.edu/tag/0CMS)
* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
* [Stacks Project, Tag 0CMX](https://stacks.math.columbia.edu/tag/0CMX)
* [Stacks Project, Tag 0CMY](https://stacks.math.columbia.edu/tag/0CMY)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` the following are equivalent:

1. `f` is limit preserving in the sense of Stacks 0CMR;
2. `f` is limit preserving on objects in the sense of Stacks 06CU;
3. `f` is locally of finite presentation in the sense of Stacks 06Q2.

Index categories are taken in the universe of the schemes. -/
@[stacks 0CMY "limit preserving, limit preserving on objects and locally of finite presentation \
  are equivalent for a 1-morphism of algebraic stacks"]
theorem isLimitPreserving_tfae {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    List.TFAE [Stack.IsLimitPreserving.{u, u, u, u + 1, u} B S hS f.hom,
      BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS 𝒳.val 𝒴.val f.hom,
      IsLocallyOfFinitePresentation B S hS f] := by
  tfae_have 1 → 2 := Stack.isLimitPreservingOnObjects_of_isLimitPreserving B S hS f.hom
  tfae_have 2 → 3 := isLocallyOfFinitePresentation_of_isLimitPreservingOnObjects B S hS f
  tfae_have 3 → 1 := fun hf =>
    isLimitPreserving_of_isLimitPreservingOnObjects B S hS f
      (isLimitPreservingOnObjects_of_isLocallyOfFinitePresentation B S hS f hf)
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf)
  tfae_finish

end AlgebraicGeometry.Stack.AlgebraicStacks

end
