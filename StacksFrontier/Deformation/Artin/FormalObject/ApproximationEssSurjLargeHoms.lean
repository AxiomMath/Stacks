module

public import StacksFrontier.Deformation.Artin.FormalObject.ApproximationEssSurj
public import StacksFrontier.Deformation.Artin.FormalObject.EquivalenceOver
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackSmallModel

/-!
# Formal objects of an algebraic stack with large hom types are effective

`Deformation.Artin.FormalObject.isEffective_of_isAlgebraicStack` (Stacks 07X8) is stated for the
objects of the 2-category of algebraic stacks of Stacks 03YP, whose total categories have hom
types in the universe of the schemes. An algebraic stack whose total category has larger hom
types, such as the stack `p'_{fp, flat, proper}` of Stacks 0D1D, is equivalent over the site to
its small model (`AlgebraicGeometry.Stack.AlgebraicStacks.smallModel`), and effectiveness of
formal objects is transported along that equivalence.

## Main results

* `Deformation.Artin.FormalObject.isEffective_of_isAlgebraicStack_largeHoms`: every formal object
  of an algebraic stack is effective, whatever the universe of the morphisms of its total
  category.

## References

* [Stacks Project, Tag 07X8](https://stacks.math.columbia.edu/tag/07X8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u w v

namespace Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Every formal object of an algebraic stack is effective** (the essential surjectivity half
of Stacks 07X8), for an algebraic stack whose total category has hom types in any universe `v`:
the formal object is transported to the small model of the stack, where it is effective by
`Deformation.Artin.FormalObject.isEffective_of_isAlgebraicStack`, and back. -/
theorem FormalObject.isEffective_of_isAlgebraicStack_largeHoms
    (𝒳 : BasedCategory.{v, u + 1} (BigFppfOver B S hS))
    (h : Stack.IsAlgebraicStack.{u, w} B S hS 𝒳) (ξ : FormalObject B S hS 𝒳.p) :
    FormalObject.IsEffective B S hS 𝒳.p h.1 ξ := by
  let 𝒴 := Stack.AlgebraicStacks.smallModel B S hS 𝒳 h
  let E : StacksRepresentableCFG.EquivalenceOver 𝒳.p 𝒴.val.val.p :=
    Stack.AlgebraicStacks.smallModelEquivalenceOver B S hS 𝒳 h
  have h𝒴 := (FormalObject.isEffective_of_isAlgebraicStack 𝒴 (ξ.mapOver E.hom)).1
  exact isEffective_of_isEffective_mapOver h.1 𝒴.val.property E ξ h𝒴

end Deformation.Artin

end
