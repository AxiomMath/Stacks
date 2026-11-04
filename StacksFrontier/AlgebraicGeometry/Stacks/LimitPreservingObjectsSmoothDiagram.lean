module

public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingObjectsFinitePresentation

/-!
# Limit preservation on objects gives local finite presentation, for any 1-morphism

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf site of a
scheme `S`. If `f` is limit preserving on objects (Stacks 06CU), then it passes the universal
smooth-diagram test of Stacks 06FM at local finite presentation of morphisms of algebraic spaces,
which is the definition of local finite presentation of Stacks 06Q2, part (1).

This is the second paragraph of the proof of Stacks 0CMY, the implication (2) ⟹ (3), and the
argument uses neither that `𝒳` nor that `𝒴` is an algebraic stack: in a smooth diagram
`U ⟶ 𝒳 ×_𝒴 V ⟶ V` over `f`, the comparison `U ⟶ 𝒳 ×_𝒴 V` is smooth, hence limit preserving on
objects (Stacks 06CX), the projection `𝒳 ×_𝒴 V ⟶ V` is limit preserving on objects as a base
change of `f` (Stacks 06CV), so the composite `U ⟶ V` is (Stacks 06CW), and a morphism of
algebraic spaces which is limit preserving on objects is locally of finite presentation
(Stacks 06CX). So it is stated here for an arbitrary 1-morphism of categories fibred in groupoids;
its reading for 1-morphisms of algebraic stacks is
`isLocallyOfFinitePresentation_of_isLimitPreservingOnObjects`, in the namespace
`AlgebraicGeometry.Stack.AlgebraicStacks`.

The unconditional form matters for a category fibred in groupoids not yet known to be an
algebraic stack, such as the Picard stack of Stacks 0DMB before Stacks 0D04.

## Main results

* `AlgebraicGeometry.Stack.hasPropertyOnEverySmoothDiagram_of_isLimitPreservingOnObjects`.

## References

* [Stacks Project, Tag 0CMY](https://stacks.math.columbia.edu/tag/0CMY)
* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 06CX](https://stacks.math.columbia.edu/tag/06CX)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CMY, the implication (2) ⟹ (3), for any 1-morphism of categories fibred in
groupoids.** A 1-morphism `f : 𝒳 ⟶ 𝒴` of categories fibred in groupoids over the big fppf site
of `S` which is limit preserving on objects (Stacks 06CU) passes the universal smooth-diagram test
of Stacks 06FM at local finite presentation of morphisms of algebraic spaces: the condition which
for a 1-morphism of algebraic stacks is local finite presentation (Stacks 06Q2, part (1)). -/
theorem hasPropertyOnEverySmoothDiagram_of_isLimitPreservingOnObjects
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (hf : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS 𝒳 𝒴 f) :
    HasPropertyOnEverySmoothDiagram B S hS
      (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h) f := by
  intro U V hU hV a b h η ha hb hcomparison
  let Q := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b f
  let hQ := CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} b f
  let k : Bicategory.TwoCommSq.PreHom (diagramCone B S hS f a b h η) Q :=
    CatFiberedInGroupoids.preHomTwoFibreProductSquare.{u, u, u + 1, u + 1} b f _
  have hk := isLimitPreservingOnObjects_of_isRelativelySmooth B S hS k.hom
    (hcomparison Q hQ k)
  have hp := BigFppfOver.isLimitPreservingOnObjects_twoFibreProductSquareFst B S hS f b hf
  have hcomp := BigFppfOver.isLimitPreservingOnObjects_comp B S hS _ _ _ k.hom Q.fst hk hp
  exact isLocallyOfFinitePresentation_of_associatedMap B S hS hU hV h
    (BigFppfOver.isLimitPreservingOnObjects_of_iso B S hS k.isoFst.symm hcomp)

end AlgebraicGeometry.Stack

end
