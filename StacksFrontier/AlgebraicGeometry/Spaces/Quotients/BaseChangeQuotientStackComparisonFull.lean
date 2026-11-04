module

public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.BaseChangeQuotientStackComparison
public import StacksFrontier.CategoryTheory.Sites.Stackification.ExtensionFullyFaithful

/-!
# Fullness of the Stacks 0DTG comparison, reduced to its presentation

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site, let `φ : U ⟶ X` be an `R`-invariant morphism of algebraic spaces
over `B`, let `g : X' ⟶ X` be a morphism of algebraic spaces over `B` and let
`(U', R', s', t', c')` be the base change of Stacks 048G. The comparison 1-morphism
`c : [U'/R'] ⟶ [U/R] ×_{𝒮_X} 𝒮_{X'}` of
`AlgebraicGeometry.Stack.baseChangeQuotientStackComparison` is the extension along the
stackification `𝒫' ⟶ [U'/R']` of its restriction to the pointwise groupoid fibration `𝒫'` of
`(U', R')`, so Stacks 04WQ reduces its **fullness** to one statement about `𝒫'`: that the
restriction is *locally fully faithful*, i.e. induces locally bijective maps of morphism
presheaves between objects of the fibres of `𝒫'`.

## Main results

* `AlgebraicGeometry.Stack.full_baseChangeQuotientStackComparison_of_morPresheafMap`: the
  comparison 1-morphism of Stacks 0DTG is full as soon as its restriction to the pointwise
  groupoid fibration of `(U', R')` is locally fully faithful.

## Implementation notes

The hypothesis mentions only objects of the fibres of the *presentation*, never an object of the
quotient stack: the reduction to presented objects, which the source carries out by passing to an
fppf covering of the test object, is supplied by
`CategoryTheory.Functor.Stackification.full_of_extension` out of the two clauses of Stacks 02ZN
exhibiting `[U'/R']` as the stackification of `𝒫'`
(`AlgebraicGeometry.Stack.isLocallyBijective_toQuotientStack` and
`AlgebraicGeometry.Stack.essImage_toQuotientStack`) together with the two morphism-sheaf
conditions, which are `AlgebraicGeometry.Stack.isStack_quotientStack` and
`AlgebraicGeometry.Stack.isMorSheaf_baseChangeTwoFibreProduct`.

This file is a reduction and not a proof; the hypothesis is discharged in
`StacksFrontier/AlgebraicGeometry/Spaces/Quotients/BaseChangeQuotientStackComparisonFibreFull.lean`
by `AlgebraicGeometry.Stack.isLocallyBijective_morPresheafMap_comparison`, which gets it from
something stronger than local bijectivity: the restriction of the comparison 1-morphism to the
presentation is **fully faithful**, because `R' = X' ×_X R` lifts an arrow of the evaluated
groupoid `G(T)` to one of the evaluated groupoid of the base change as soon as the two
`T`-points of `X'` involved agree, which a vertical morphism of the 2-fibre product forces.

## References

* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 0436](https://stacks.math.columbia.edu/tag/0436)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 048G](https://stacks.math.columbia.edu/tag/048G)
* [Stacks Project, Tag 04WQ](https://stacks.math.columbia.edu/tag/04WQ)
* [Stacks Project, Tag 0DTG](https://stacks.math.columbia.edu/tag/0DTG)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

section BaseChange

variable (G : GroupoidInAlgebraicSpaces C S hS B) {X X' : AlgebraicSpaces C S hS}
  (XtoB : X ⟶ B) (X'toB : X' ⟶ B) (g : X' ⟶ X) (hg : g ≫ XtoB = X'toB)
  (φ : G.objects ⟶ X) (hφB : φ ≫ XtoB = G.objectsToBase)
  (hφ : Space.IsInvariant (Space.groupoidPreRelation G) φ.hom)

/-- **The comparison 1-morphism of Stacks 0DTG is full as soon as its restriction to the pointwise
groupoid fibration of `(U', R')` is locally fully faithful.**

The restriction in question is the stackification map `𝒫' ⟶ [U'/R']` followed by the comparison
1-morphism, and the hypothesis is that it induces locally injective and locally surjective maps of
morphism presheaves between any two objects of any fibre of `𝒫'`. Stacks 04WQ, in the form
`CategoryTheory.Functor.Stackification.full_of_extension`, then gives fullness of the comparison
1-morphism between arbitrary objects of `[U'/R']`.

With `AlgebraicGeometry.Stack.faithful_comparison` and
`AlgebraicGeometry.Stack.locallyEssSurjOnFibers_baseChangeQuotientStackComparison` this is the
last hypothesis of
`AlgebraicGeometry.Stack.isTwoFibreProduct_baseChangeQuotientStackSquare`. -/
theorem full_baseChangeQuotientStackComparison_of_morPresheafMap
    (hFmor :
      have := isFibered_baseChangeTwoFibreProduct G XtoB g φ hφB hφ
      ∀ (T : BigFppfOver C S hS)
        (x y : (quotientPrestack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).p.Fiber T),
        Presheaf.IsLocallyInjective ((BigFppfOver.topology C S hS).over T)
            (((isFibredOneMorphism_toQuotientStack
                  (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).comp
                (isFibredOneMorphism_baseChangeQuotientStackComparison.{u, w}
                  G XtoB X'toB g hg φ hφB hφ)).morPresheafMap x y) ∧
          Presheaf.IsLocallySurjective ((BigFppfOver.topology C S hS).over T)
            (((isFibredOneMorphism_toQuotientStack
                  (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).comp
                (isFibredOneMorphism_baseChangeQuotientStackComparison.{u, w}
                  G XtoB X'toB g hg φ hφB hφ)).morPresheafMap x y)) :
    (baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ).Full := by
  have hfib := isFibered_baseChangeTwoFibreProduct G XtoB g φ hφB hφ
  exact Functor.Stackification.full_of_extension
    (isFibredOneMorphism_toQuotientStack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ))
    (isFibredOneMorphism_baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ)
    (BigFppfOver.topology C S hS)
    (isLocallyBijective_toQuotientStack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ))
    (essImage_toQuotientStack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)) hFmor
    (fun T x y =>
      (isStack_quotientStack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).isMorSheaf T x y)
    (fun T x y => isMorSheaf_baseChangeTwoFibreProduct G XtoB g φ hφB hφ T x y)

end BaseChange

end AlgebraicGeometry.Stack

end
