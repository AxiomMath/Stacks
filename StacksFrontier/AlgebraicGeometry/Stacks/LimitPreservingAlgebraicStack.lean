module

public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingOfObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingRelativeDescentFiniteType

/-!
# Limit preservation of a 1-morphism of algebraic stacks from limit preservation on objects

A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` which is locally of finite type and limit
preserving on objects (Stacks 06CU) is limit preserving (Stacks 0CMR): its two diagonals are limit
preserving on objects, being representable by algebraic spaces and locally of finite
presentation, so
`AlgebraicGeometry.Stack.isLimitPreserving_of_isLimitPreservingOnObjects_diagonals` applies.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isLimitPreserving_of_isLimitPreservingOnObjects`.

## References

* [Stacks Project, Tag 0CMG](https://stacks.math.columbia.edu/tag/0CMG)
* [Stacks Project, Tag 0CMR](https://stacks.math.columbia.edu/tag/0CMR)
* [Stacks Project, Tag 0CMY](https://stacks.math.columbia.edu/tag/0CMY)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A 1-morphism of algebraic stacks locally of finite type and limit preserving on objects is
limit preserving.** This is the formal part of the implication (3) ⟹ (1) of Stacks 0CMY: the
relative diagonal and the second diagonal are limit preserving on objects by Stacks 04XS,
Stacks 0CMG and Stacks 06CX, and limit preservation on objects of `f` and of its two diagonals
gives limit preservation of `f` by Stacks 0CMW. -/
theorem isLimitPreserving_of_isLimitPreservingOnObjects
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hobj : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS 𝒳.val 𝒴.val f.hom)
    (hf : IsLocallyOfFiniteType B S hS f) :
    Stack.IsLimitPreserving.{u, u, u, u + 1, u} B S hS f.hom :=
  Stack.isLimitPreserving_of_isLimitPreservingOnObjects_diagonals.{u, u, u} B S hS f.hom hobj
    (isLimitPreservingOnObjects_relativeDiagonal B S hS f hf)
    (isLimitPreservingOnObjects_relativeDiagonal_relativeDiagonal B S hS f hf)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
