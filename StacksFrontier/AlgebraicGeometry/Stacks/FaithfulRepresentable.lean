module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.MorphismRepresentableBySpaces.Criterion
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise

/-!
# Faithfulness and representability by algebraic spaces

Let `S` be a scheme contained in a big fppf site and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
categories fibred in groupoids over `S`. Consider the conditions:

1. for every scheme `U` over `S` the functor `f_U : 𝒳_U ⥤ 𝒴_U` on fibres is faithful,
2. the functor `f` is faithful, and
3. `f` is representable by algebraic spaces.

The equivalence of (1) and (2) is
`CategoryTheory.Functor.IsFiberedInGroupoids.faithful_iff_forall_fiber`. This file proves the
implication (3) ⟹ (2): condition (1) is the first conjunct of the criterion
`AlgebraicGeometry.isRepresentableByAlgebraicSpaces_iff_associatedMap`.

## Main results

* `AlgebraicGeometry.Stack.faithful_homFunctor_of_isRepresentableByAlgebraicSpaces`:
  the implication (3) ⟹ (2), for a 1-morphism of categories fibred in groupoids.
* `AlgebraicGeometry.Stack.AlgebraicStacks.faithful_homFunctor_of_isRepresentableByAlgebraicSpaces`
  is the same implication for a 1-morphism of algebraic stacks.

## Implementation notes

The criterion `AlgebraicGeometry.isRepresentableByAlgebraicSpaces_iff_associatedMap` states
condition (1) with `CategoryTheory.Stacks.RepresentableMorphism.inducedFiberFunctor`, while
`CategoryTheory.Functor.IsFiberedInGroupoids.faithful_iff_forall_fiber` states it with
`CategoryTheory.Functor.Fiber.mapOfComp`; both are `CategoryTheory.Functor.Fiber.inducedFunctor`
applied to `fiberInclusion ⋙ F`, so the two conditions are definitionally equal. The criterion is
applied at the choice of pullbacks `CategoryTheory.Functor.chosenPullbacks`.

## References

* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
* [Stacks Project, Tag 02ZY](https://stacks.math.columbia.edu/tag/02ZY)
* [Stacks Project, Tag 04SZ](https://stacks.math.columbia.edu/tag/04SZ)
* [Stacks Project, Tag 04Y5](https://stacks.math.columbia.edu/tag/04Y5)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

add_to_stacks 04Y5 "the equivalence of parts (1) and (2)"
  CategoryTheory.Functor.IsFiberedInGroupoids.faithful_iff_forall_fiber

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A 1-morphism of categories fibred in groupoids over the big fppf site of `S` which is
representable by algebraic spaces has faithful underlying functor. -/
@[stacks 04Y5 "the implication (3) ⟹ (2)"]
theorem faithful_homFunctor_of_isRepresentableByAlgebraicSpaces
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom) :
    (CatFiberedInGroupoids.homFunctor f).Faithful := by
  have : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  exact (Functor.IsFiberedInGroupoids.faithful_iff_forall_fiber 𝒳.val.p 𝒴.val.p
    𝒳.isFiberedInGroupoids 𝒴.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor f)
    (CatFiberedInGroupoids.homFunctor_comp_p f)).mpr fun U =>
      ((AlgebraicGeometry.isRepresentableByAlgebraicSpaces_iff_associatedMap B S hS f
        𝒴.val.p.chosenPullbacks).mp hf).1 U

namespace AlgebraicStacks

/-- A 1-morphism of algebraic stacks over `S` which is representable by algebraic spaces has
faithful underlying functor. -/
@[stacks 04Y5 "the implication (3) ⟹ (2) for algebraic stacks"]
theorem faithful_homFunctor_of_isRepresentableByAlgebraicSpaces
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) :
    (CatFiberedInGroupoids.homFunctor f.hom).Faithful :=
  Stack.faithful_homFunctor_of_isRepresentableByAlgebraicSpaces B S hS f.hom hf

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
