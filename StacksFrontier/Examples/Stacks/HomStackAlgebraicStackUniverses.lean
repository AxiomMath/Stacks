module

public import StacksFrontier.Deformation.Artin.FormalObject.ApproximationEssSurj
public import StacksFrontier.Examples.Stacks.HomStackSeparatedTargetCriterion

/-!
# The non-algebraic Hom-stack example with Stacks 07X8 discharged

The deductions of Stacks 0AFC in `StacksFrontier.Examples.Stacks.NonAlgebraicHomStack` take
Stacks 07X8 as a hypothesis `h07X8`, because their categories over the site have arbitrary
universes. Stacks 07X8 is proved in this library,
`Deformation.Artin.isEquivalence_approximationFunctor_algebraicStacks`, for the objects of the
2-category `AlgebraicGeometry.Stack.AlgebraicStacks` of Stacks 03YP, whose total categories have
the universes `{u, u + 1}`. This file states the same results at those universes, where `h07X8`
is discharged. The separated-target criterion of Stacks 0AFD, with Stacks 07X8 discharged, is in
`StacksFrontier.Examples.Stacks.HomStackSeparatedTargetCriterionUnconditional`.

## Main results

* `Stacks.Examples.NonAlgebraicHomStack.not_isAlgebraicStack_of_not_essSurj`: a category fibred
  in groupoids whose comparison functor of Stacks 07X6 is not essentially surjective is not an
  algebraic stack.
* `Stacks.Examples.NonAlgebraicHomStack.not_isAlgebraicStack_of_not_isEffective` and
  `Stacks.Examples.NonAlgebraicHomStack.not_isAlgebraicStack_powerSeriesBase_of_not_isEffective`:
  the same with a formal object that is not effective (Stacks 07X7).

The Hom-stack `Mor_S(X, [S/A])` of Stacks 0AFC is `AlgebraicGeometry.Stack.homStack`, and
Stacks 0AFB and Stacks 0AFC for it are in `StacksFrontier.Examples.Stacks.NonAlgebraicHomStack.Main`.

## References

* [Stacks Project, Tag 0AFC](https://stacks.math.columbia.edu/tag/0AFC)
* [Stacks Project, Tag 07X8](https://stacks.math.columbia.edu/tag/07X8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w

namespace Stacks.Examples.NonAlgebraicHomStack

/-! ### Stacks 0AFC -/

/-- The deduction of Stacks 0AFC from Stacks 0AFB, with Stacks 07X8 discharged. A category `𝒳`
fibred in groupoids over the big fppf site of `S`, with the universes of the 2-category
`AlgebraicGeometry.Stack.AlgebraicStacks` of Stacks 03YP, whose comparison functor of Stacks 07X6
is not essentially surjective, is not an algebraic stack: by Stacks 07X8,
`Deformation.Artin.isEquivalence_approximationFunctor_algebraicStacks`, the comparison functor
of an algebraic stack is an equivalence.

For the source's `𝒳 = Mor_S(X, [S/A])`, Stacks 0AFC is
`Stacks.Examples.NonAlgebraicHomStack.Situation.not_isAlgebraicStack_homStackClassifyingStack`. -/
public theorem not_isAlgebraicStack_of_not_essSurj
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CategoryTheory.BasedCategory.{u, u + 1} (AlgebraicGeometry.BigFppfOver B S hS))
    (hp : 𝒳.p.IsFiberedInGroupoids)
    (hnotEssSurj : ¬ (Deformation.Artin.approximationFunctor B S hS 𝒳.p hp).EssSurj) :
    ¬ AlgebraicGeometry.Stack.IsAlgebraicStack.{u, w} B S hS 𝒳 :=
  fun h𝒳 => hnotEssSurj
    (Deformation.Artin.isEquivalence_approximationFunctor_algebraicStacks
      (⟨CatFiberedInGroupoids.mk 𝒳 hp, h𝒳⟩ :
        AlgebraicGeometry.Stack.AlgebraicStacks.{u, w} B S hS)).essSurj

/-- The deduction of Stacks 0AFC in the vocabulary of effective formal objects, with Stacks 07X8
discharged. A category fibred in groupoids over the big fppf site of `S`, with the universes of
the 2-category of algebraic stacks, which has a formal object that is not effective in the sense
of Stacks 07X7, is not an algebraic stack. See the module documentation. -/
public theorem not_isAlgebraicStack_of_not_isEffective
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CategoryTheory.BasedCategory.{u, u + 1} (AlgebraicGeometry.BigFppfOver B S hS))
    (hp : 𝒳.p.IsFiberedInGroupoids)
    (hnotEffective : ∃ ξ : Deformation.Artin.FormalObject B S hS 𝒳.p,
      ¬ Deformation.Artin.FormalObject.IsEffective B S hS 𝒳.p hp ξ) :
    ¬ AlgebraicGeometry.Stack.IsAlgebraicStack.{u, w} B S hS 𝒳 := by
  obtain ⟨ξ, hξ⟩ := hnotEffective
  refine not_isAlgebraicStack_of_not_essSurj B S hS 𝒳 hp fun hess => ?_
  exact hξ (CategoryTheory.Functor.EssSurj.mem_essImage _ ξ)

/-- The deduction of Stacks 0AFC over the section's base `S = Spec k⟦t⟧`, with Stacks 07X8
discharged: a category fibred in groupoids over the big fppf site over `S`, with the universes
of the 2-category of algebraic stacks, which has a formal object that is not effective is not an
algebraic stack. See the module documentation. -/
public theorem not_isAlgebraicStack_powerSeriesBase_of_not_isEffective
    {k : Type u} [Field k] (B : AlgebraicGeometry.BigFppfSite.{u})
    (hS : B.Contains (base k))
    (𝒳 : CategoryTheory.BasedCategory.{u, u + 1}
      (AlgebraicGeometry.BigFppfOver B (base k) hS))
    (hp : 𝒳.p.IsFiberedInGroupoids)
    (hnotEffective : ∃ ξ : Deformation.Artin.FormalObject B (base k) hS 𝒳.p,
      ¬ Deformation.Artin.FormalObject.IsEffective B (base k) hS 𝒳.p hp ξ) :
    ¬ AlgebraicGeometry.Stack.IsAlgebraicStack.{u, w} B (base k) hS 𝒳 :=
  not_isAlgebraicStack_of_not_isEffective B (base k) hS 𝒳 hp hnotEffective

end Stacks.Examples.NonAlgebraicHomStack

end
