module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Order
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack

/-!
# First-order thickenings of algebraic stacks (Stacks 0BPQ)

An algebraic stack `𝒳'` over `S` is a *first-order thickening* of a closed substack `𝒳 ⊂ 𝒳'`
when the closed immersion `𝒳 ⟶ 𝒳'` is a first-order thickening of algebraic spaces
(**Stacks 05ZK**, part (2)) after base change to every scheme-valued point of `𝒳'`.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.IsFirstOrderThickening`: **Stacks 0BPQ**.

## Implementation notes

The specified 1-morphism is required to be a closed immersion of algebraic stacks (**Stacks
04YL**, part (2)), which is where "closed substack" (**Stacks 04YM**) enters; representability by
algebraic spaces is part of that condition, so the base changes below are represented.

The square-zero condition is then imposed, in the manner of the relative property of **Stacks
03YK**, on each algebraic space `F` representing the base change of `𝒳 ⟶ 𝒳'` along a
scheme-valued point `U ⟶ 𝒳'`: the structural morphism of `F` over the representable algebraic
space of `U` is a closed immersion, and its *image subfunctor* is required to be a first-order
thickening of that representable algebraic space in the sense of Stacks 05ZK, part (2). Phrasing
the condition through `CategoryTheory.Subfunctor.range` rather than through `F` itself is what
makes it independent of which algebraic space was chosen to represent the base change: two
representatives have the same image subfunctor, while `F` is determined only up to isomorphism
over `U`.

Stacks 05ZK, part (2) is `AlgebraicGeometry.Space.IsFirstOrderThickening` of
`StacksDraft.AlgebraicGeometry.Spaces.ThickeningOrder`; it is stated there through the chartwise
defining ideal of Stacks 03MB, so the condition here is the vanishing of the square of that ideal
on every object of the small étale site of the representable algebraic space of `U`.

The passage from an algebraic space over `U` to one over `S`, and the structural morphism it
acquires, are `AlgebraicGeometry.spacesOverSmallerBaseFunctor` (**Stacks 04SG**) and
`AlgebraicGeometry.algebraicSpaceMap`, exactly as in `AlgebraicGeometry.Stack.HasRelativeProperty`
(**Stacks 03YK**); the test is written out longhand rather than through that definition because
the property being tested here is a property of a *subfunctor of the target*, not a
`CategoryTheory.MorphismProperty`.

## References

* [Stacks Project, Tag 0BPQ](https://stacks.math.columbia.edu/tag/0BPQ)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
-/

@[expose] public section

open CategoryTheory
open Stacks.Thickenings

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒳' : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 0BPQ.** A closed immersion `i : 𝒳 ⟶ 𝒳'` of algebraic stacks over `S` exhibits `𝒳'`
as a *first-order thickening* of `𝒳` when, for every scheme-valued point `U ⟶ 𝒳'` and every
algebraic space `F` representing the base change of `i` along it, the image of the structural
morphism of `F` is a first-order thickening of the representable algebraic space of `U` in the
sense of Stacks 05ZK, part (2) — that is, the ideal cutting it out is square-zero on every object
of the small étale site. -/
@[stacks 0BPQ]
abbrev IsFirstOrderThickening (i : 𝒳 ⟶ 𝒳') : Prop :=
  IsClosedImmersion B S hS i ∧
    ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳'.val.val.obj)
      (_hy : y ⋙ 𝒳'.val.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p 𝒳'.val.val.p y
          (CatFiberedInGroupoids.homFunctor i.hom))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.IsFirstOrderThickening B S hS
        ⟨yoneda.obj (Over.mk U.hom), isAlgebraicSpace_yoneda B S hS (Over.mk U.hom)⟩
        (Subfunctor.range
          (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
