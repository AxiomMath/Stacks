module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack

/-!
# Finite presentation implies finite type for 1-morphisms of algebraic stacks (Stacks 06Q5)

A 1-morphism of algebraic stacks over `S` that is of finite presentation is of finite type. The
corresponding statement for the local notions is
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isFiniteType_of_isFinitePresentation`: a 1-morphism of
  algebraic stacks of finite presentation is of finite type.

## References

* [Stacks Project, Tag 06FS](https://stacks.math.columbia.edu/tag/06FS)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
* [Stacks Project, Tag 06Q5](https://stacks.math.columbia.edu/tag/06Q5)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A 1-morphism of algebraic stacks over `S` of finite presentation is of finite type. -/
@[stacks 06Q5 "finite presentation implies finite type"]
theorem isFiniteType_of_isFinitePresentation
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsFinitePresentation B S hS f) :
    IsFiniteType B S hS f :=
  ⟨isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf.1, hf.2.1⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
