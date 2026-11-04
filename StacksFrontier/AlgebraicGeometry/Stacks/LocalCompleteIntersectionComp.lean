module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.Locality
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalCompleteIntersectionComposition

/-!
# Composition of local complete intersection 1-morphisms of algebraic stacks, with nothing assumed

**Stacks 0CJ4** says that a composition of local complete intersection 1-morphisms of algebraic
stacks over `S` is a local complete intersection 1-morphism: if `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` are
Koszul, so is `f ≫ g`.

`StacksFrontier.AlgebraicGeometry.Stacks.LocalCompleteIntersectionComposition` proves this from one
hypothesis beyond the source's: that the Koszul property of morphisms of algebraic spaces over
`S` is smooth local on the source-and-target. That hypothesis is discharged here by
`AlgebraicGeometry.Space.isLocalCompleteIntersection_isSmoothLocalOnSourceAndTarget`, which feeds
syntomic locality on the source (**Stacks 0CHN**) and on the target (the syntomic case of
**Stacks 0CHM**) of the Koszul property of morphisms of algebraic spaces through the criterion
**Stacks 06FB**; it carries no hypothesis, so the statement below is the source's.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.IsLocalCompleteIntersection.comp`: **Stacks 0CJ4**.

## References

* [Stacks Project, Tag 06C8](https://stacks.math.columbia.edu/tag/06C8)
* [Stacks Project, Tag 06FB](https://stacks.math.columbia.edu/tag/06FB)
* [Stacks Project, Tag 06FP](https://stacks.math.columbia.edu/tag/06FP)
* [Stacks Project, Tag 0CHM](https://stacks.math.columbia.edu/tag/0CHM)
* [Stacks Project, Tag 0CHN](https://stacks.math.columbia.edu/tag/0CHN)
* [Stacks Project, Tag 0CJ3](https://stacks.math.columbia.edu/tag/0CJ3)
* [Stacks Project, Tag 0CJ4](https://stacks.math.columbia.edu/tag/0CJ4)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0CJ4.** The composition of local complete intersection 1-morphisms of algebraic
stacks over `S` is a local complete intersection 1-morphism: if `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` are
Koszul, so is `f ≫ g`.

This is the general composition remark **Stacks 06FP** at the Koszul property of morphisms of
algebraic spaces, which is stable under composition by **Stacks 06C8**, as in
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocalCompleteIntersection_comp`; the smooth locality
on the source-and-target that argument consumes is
`AlgebraicGeometry.Space.isLocalCompleteIntersection_isSmoothLocalOnSourceAndTarget`. -/
@[stacks 0CJ4]
theorem IsLocalCompleteIntersection.comp
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴} {g : 𝒴 ⟶ 𝒵}
    (hf : IsLocalCompleteIntersection B S hS f)
    (hg : IsLocalCompleteIntersection B S hS g) :
    IsLocalCompleteIntersection B S hS (f ≫ g) :=
  isLocalCompleteIntersection_comp B S hS
    (Space.isLocalCompleteIntersection_isSmoothLocalOnSourceAndTarget B S hS) f g hf hg

end AlgebraicGeometry.Stack.AlgebraicStacks

end
