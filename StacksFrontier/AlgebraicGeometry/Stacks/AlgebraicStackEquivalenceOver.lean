module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackSmallModel

/-!
# Every algebraic stack is equivalent to an object of the 2-category of algebraic stacks

An algebraic stack over the big fppf site of `S` whose objects lie in `Type (u + 1)` may have hom
types in any universe. Its small model `AlgebraicGeometry.Stack.AlgebraicStacks.smallModel` is an
object of the 2-category `AlgebraicGeometry.Stack.AlgebraicStacks` of Stacks 03YP and is
equivalent to it over the site, so every such algebraic stack is equivalent over the site to an
object of that 2-category.

## Main results

* `AlgebraicGeometry.Stack.exists_algebraicStacks_equivalenceOver`: every algebraic stack with
  objects in `Type (u + 1)` is equivalent over the site to an object of
  `AlgebraicGeometry.Stack.AlgebraicStacks`.

## References

* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 03YQ](https://stacks.math.columbia.edu/tag/03YQ)
-/

@[expose] public section

namespace AlgebraicGeometry.Stack

universe u w v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Every algebraic stack with objects in `Type (u + 1)` is equivalent over the site to an
object of the 2-category of algebraic stacks of Stacks 03YP**, whatever the universe of its
morphisms: its small model is one. -/
theorem exists_algebraicStacks_equivalenceOver
    {𝒳 : CategoryTheory.BasedCategory.{v, u + 1} (BigFppfOver B S hS)}
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳) :
    ∃ 𝒴 : AlgebraicStacks.{u, w} B S hS,
      Nonempty (StacksRepresentableCFG.EquivalenceOver 𝒳.p 𝒴.val.val.p) :=
  ⟨AlgebraicStacks.smallModel B S hS 𝒳 h𝒳,
    ⟨AlgebraicStacks.smallModelEquivalenceOver B S hS 𝒳 h𝒳⟩⟩

end AlgebraicGeometry.Stack

end
