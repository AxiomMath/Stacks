module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackSmallModel
public import StacksFrontier.Deformation.Artin.FormalObject.DiagonalBaseChangeEffective

/-!
# Effectivity of formal objects of an algebraic stack with large hom types

`Deformation.Artin.essSurj_approximationFunctor_algebraicStacks` (the essential surjectivity half of
Stacks 07X8) is stated for an object of the 2-category of algebraic stacks of Stacks 03YP, whose
total category has its morphisms in the universe of the schemes. Here the same conclusion is drawn
for an arbitrary based category over the big fppf site which is an algebraic stack, with its
morphisms in any universe: it is equivalent over the site to its small model
(`AlgebraicGeometry.Stack.AlgebraicStacks.smallModel`), and effectivity of formal objects
transports along an equivalence over the site
(`Deformation.Artin.essSurj_approximationFunctor_of_equivalenceOver`).

## Main results

* `Deformation.Artin.essSurj_approximationFunctor_of_isAlgebraicStack`: the approximation functor
  of Stacks 07X6 of an algebraic stack is essentially surjective.
* `Deformation.Artin.FormalObject.isEffective_of_isAlgebraicStack_of_isFiberedInGroupoids`:
  every formal object of an algebraic stack is effective.

## References

* [Stacks Project, Tag 07X8](https://stacks.math.columbia.edu/tag/07X8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u w v

namespace Deformation.Artin

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Every formal object of an algebraic stack is effective** (the essential surjectivity half of
Stacks 07X8), for an algebraic stack given as a based category over the big fppf site whose
morphisms live in an arbitrary universe. -/
theorem essSurj_approximationFunctor_of_isAlgebraicStack
    (𝒳 : BasedCategory.{v, u + 1} (BigFppfOver B S hS))
    (h𝒳 : Stack.IsAlgebraicStack.{u, w} B S hS 𝒳) (hp : 𝒳.p.IsFiberedInGroupoids) :
    (approximationFunctor B S hS 𝒳.p hp).EssSurj :=
  essSurj_approximationFunctor_of_equivalenceOver
    (Stack.AlgebraicStacks.smallModelEquivalenceOver B S hS 𝒳 h𝒳).symm _ hp
    (essSurj_approximationFunctor_algebraicStacks
      (Stack.AlgebraicStacks.smallModel B S hS 𝒳 h𝒳))

/-- **Every formal object of an algebraic stack is effective** (Stacks 07X8, essential
surjectivity), in the vocabulary of effective formal objects of Stacks 07X7. -/
theorem FormalObject.isEffective_of_isAlgebraicStack_of_isFiberedInGroupoids
    (𝒳 : BasedCategory.{v, u + 1} (BigFppfOver B S hS))
    (h𝒳 : Stack.IsAlgebraicStack.{u, w} B S hS 𝒳) (hp : 𝒳.p.IsFiberedInGroupoids)
    (ξ : FormalObject B S hS 𝒳.p) : FormalObject.IsEffective B S hS 𝒳.p hp ξ :=
  (essSurj_approximationFunctor_of_isAlgebraicStack B S hS 𝒳 h𝒳 hp).mem_essImage ξ

end Deformation.Artin

end
