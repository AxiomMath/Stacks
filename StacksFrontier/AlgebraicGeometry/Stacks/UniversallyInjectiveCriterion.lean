module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Stacks.UnderlyingTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversalTopologicalProperties

/-!
# Universally injective representable 1-morphisms of algebraic stacks (Stacks 0CI1)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` representable by algebraic spaces.
**Stacks 0CI1** says that `f` is universally injective — the relative property of Tag 04XB at
universal injectivity of morphisms of algebraic spaces — exactly when, for every algebraic stack
`𝒵` over `𝒴`, the map `|𝒵 ×_𝒴 𝒳| → |𝒵|` on the points of Tag 04XG is injective. The right-hand
side is the absolute notion of Tag 0CI2, which quantifies over every 2-fibre product of the
cospan rather than only over the canonical one of Tag 04T2.

## Main results

* `AlgebraicGeometry.Stack.representable_universallyInjective_iff`: **Stacks 0CI1**.

## Implementation notes

This is the injective instance of
`AlgebraicGeometry.Stack.relative_iff_forall_pointsMap_fst`, which carries the whole argument for
an abstract property of maps on point spaces; injectivity satisfies its two closure conditions by
`AlgebraicGeometry.Stack.isConjInvariant_injectiveProperty` and
`AlgebraicGeometry.Stack.isDescendable_injectiveProperty`. Passing between the canonical 2-fibre
product and an arbitrary one is `AlgebraicGeometry.Stack.pointMapProperty_fst_congr`, read
through the square underlying a 2-fibre product of algebraic stacks.

The relative side is written out in the unrolled form of Tag 04XB, as
`AlgebraicGeometry.Stack.UniversallyClosed` is.

## References

* [Stacks Project, Tag 03MV](https://stacks.math.columbia.edu/tag/03MV)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 0CI1](https://stacks.math.columbia.edu/tag/0CI1)
* [Stacks Project, Tag 0CI2](https://stacks.math.columbia.edu/tag/0CI2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CI1.** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` representable by
algebraic spaces is universally injective in the relative sense of Tag 04XB — every algebraic
space representing a base change of `f` along a scheme-valued point of `𝒴` has universally
injective structural morphism — exactly when, for every algebraic stack `𝒵` over `𝒴` and every
2-fibre product of the cospan, the map `|𝒵 ×_𝒴 𝒳| → |𝒵|` is injective. -/
@[stacks 0CI1]
theorem representable_universallyInjective_iff
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) :
    (∀ (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.val.obj)
        (_hy : y ⋙ 𝒴.val.val.p = Over.map U.hom)
        (T : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hT : IsAlgebraicSpace B U.left.1 U.left.2 T),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p y
            (CatFiberedInGroupoids.homFunctor f.hom))
          (presheafOfCategories (T ⋙ typeToCat)).p) →
        Space.UniversallyInjective B S hS
          (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨T, hT⟩)).hom) ↔
      UniversallyInjective B S hS f := by
  have := respectsIso_pointMapProperty B S hS injectiveProperty.{u}
    isConjInvariant_injectiveProperty
  have hrel := relative_iff_forall_pointsMap_fst B S hS injectiveProperty.{u}
    isConjInvariant_injectiveProperty isDescendable_injectiveProperty f hf
  constructor
  · intro H 𝒵 g P hP
    refine pointMapProperty_fst_congr B S hS injectiveProperty.{u}
      isConjInvariant_injectiveProperty
      (twoFibreProductSquareAlgebraicStacks B S hS g f).underlying P.underlying
      (isTwoFibreProduct_underlying_algebraicStacks B S hS _
        (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g f))
      (isTwoFibreProduct_underlying_algebraicStacks B S hS P hP) ?_
    refine hrel.mp ?_ 𝒵 g
    intro U y hy T hT he
    exact (universally_iff_forall_space_baseChange B S hS _ _).mpr (H U y hy T hT he)
  · intro H U y hy T hT he
    exact (universally_iff_forall_space_baseChange B S hS
      (pointMapProperty B S hS injectiveProperty.{u}) _).mp
      (hrel.mpr (fun 𝒵 g => H 𝒵 g (twoFibreProductSquareAlgebraicStacks B S hS g f)
        (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g f)) U y hy T hT he)

end AlgebraicGeometry.Stack

end
