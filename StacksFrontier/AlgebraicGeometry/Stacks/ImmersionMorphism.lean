module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeProperty

/-!
# Immersions and locally separated representable 1-morphisms of stacks

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf site of
`S` which is representable by algebraic spaces. Following Stacks 04XB, `f` *is an immersion*,
respectively *is locally separated*, when every algebraic space representing the base change of
`f` along a scheme-valued point of `𝒴` has structural morphism an immersion, respectively
locally separated, read as a morphism of algebraic spaces over `S`.

A scheme-valued point of `𝒴` is a functor from the big fppf site of a scheme `U` over `S` to the
total category of `𝒴` lying over `CategoryTheory.Over.map U.hom`; quantifying over *all*
algebraic spaces representing the base change makes the condition independent of the choice made
in Stacks 0402. An algebraic space over `U` is read over `S` through
`AlgebraicGeometry.spacesOverSmallerBaseFunctor`, and its structural morphism through
`AlgebraicGeometry.algebraicSpaceMap`.

## Main definitions

* `AlgebraicGeometry.Stack.IsImmersion`
* `AlgebraicGeometry.Stack.IsLocallySeparated`

## Main results

* `AlgebraicGeometry.Stack.isImmersion_iff_hasRelativeProperty`: the first predicate is the
  relative property `AlgebraicGeometry.Stack.HasRelativeProperty` at
  `AlgebraicGeometry.Space.immersionProperty`, as soon as that property is local at the target
  for the fppf precoverage.

## References

* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 04YU](https://stacks.math.columbia.edu/tag/04YU)
* [Stacks Project, Tag 0CL0](https://stacks.math.columbia.edu/tag/0CL0)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}

/-- A 1-morphism of categories fibred in groupoids over the big fppf site of `S` which is
representable by algebraic spaces *is an immersion* when every algebraic space representing its
base change along a scheme-valued point of the target has immersion structural morphism, read as
a morphism of algebraic spaces over `S`. -/
abbrev IsImmersion (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.IsImmersion B S hS
        (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom

/-- A 1-morphism of categories fibred in groupoids over the big fppf site of `S` which is
representable by algebraic spaces *is locally separated* when every algebraic space representing
its base change along a scheme-valued point of the target has locally separated structural
morphism, read as a morphism of algebraic spaces over `S`. -/
abbrev IsLocallySeparated (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.IsLocallySeparated B S hS
        (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom

/-- If `AlgebraicGeometry.Space.immersionProperty` is local at the target for the fppf
precoverage, then `AlgebraicGeometry.Stack.IsImmersion` is the relative property
`AlgebraicGeometry.Stack.HasRelativeProperty` at `AlgebraicGeometry.Space.immersionProperty`. -/
theorem isImmersion_iff_hasRelativeProperty
    [(Space.immersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, v} B S hS)]
    (f : 𝒳 ⟶ 𝒴) (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom) :
    IsImmersion B S hS f ↔
      HasRelativeProperty B S hS (Space.immersionProperty B S hS) f hf :=
  Iff.rfl

end AlgebraicGeometry.Stack

end
