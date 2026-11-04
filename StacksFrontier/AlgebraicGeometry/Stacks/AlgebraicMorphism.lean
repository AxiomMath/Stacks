module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.CategoryTheory.TwoFibreProductOver

/-!
# Algebraic morphisms of stacks in groupoids (Stacks 06CF)

Let `B` be a big fppf site, `S` a scheme it contains, and let `𝒳` and `𝒴` be stacks in
groupoids over the big fppf site of `S`. A 1-morphism `f : 𝒳 ⟶ 𝒴` is *algebraic* when its
2-fibre product with every scheme-valued point of `𝒴` is an algebraic stack.

## Main definitions

* `AlgebraicGeometry.Stack.IsAlgebraicMorphism`: **Stacks 06CF**.

## Implementation notes

A scheme-valued point of `𝒴` over an object `U` of the big fppf site is a functor from the
big fppf site of `U` to the underlying category of `𝒴` that is compatible with the map of
sites to the site of `S`, and the base change is the explicit 2-fibre product
`CategoryTheory.TwoFibreProductOver` over the site of `S`. The condition is an abbreviation,
so downstream results can use its universal quantifier directly.

The source and target stacks carry independent object, morphism and descent universes, and
the 1-morphism is expressed as a `BasedFunctor`, so `𝒳` and `𝒴` need not live in the same
universe of bundled stacks; for stacks in groupoids every based functor is a 1-morphism, so
this is no weaker than quantifying over 1-morphisms of a single bundled 2-category.

## References

* [Stacks Project, Tag 06CF](https://stacks.math.columbia.edu/tag/06CF)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Stack

/-- A morphism of stacks is algebraic if every base change along a
scheme-valued point of its target is an algebraic stack. -/
@[stacks 06CF]
abbrev IsAlgebraicMorphism.{u, wX, wY, w, vX, uX, vY, uY}
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : StackInGroupoids.{wX, u, vX, u + 1, uX}
      (BigFppfOver B S hS)
      (BigFppfOver.topology B S hS)}
    {𝒴 : StackInGroupoids.{wY, u, vY, u + 1, uY}
      (BigFppfOver B S hS)
      (BigFppfOver.topology B S hS)}
    (f : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory) : Prop :=
  ∀ (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.toBasedCategory.obj)
    (_hy : y ⋙ 𝒴.toBasedCategory.p = Over.map U.hom),
    IsAlgebraicStack.{u, w} B S hS
      (BasedCategory.ofFunctor
        (TwoFibreProductOver.structureFunctor (Over.map U.hom)
          𝒳.toBasedCategory.p 𝒴.toBasedCategory.p y f.toFunctor))

end AlgebraicGeometry.Stack

end
