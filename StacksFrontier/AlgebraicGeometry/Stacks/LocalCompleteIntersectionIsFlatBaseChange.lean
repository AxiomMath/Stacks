module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.Locality
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalCompleteIntersectionFlatBaseChange

/-!
# Flat base change of a local complete intersection 1-morphism of algebraic stacks (Stacks 0CJ5)

**Stacks 0CJ5** says that a flat base change of a local complete intersection 1-morphism of
algebraic stacks over `S` is a local complete intersection 1-morphism.

The source's hint is to argue as in the base-change remark **Stacks 06FQ**, only for a flat
1-morphism `𝒴' ⟶ 𝒴`, using flat base change of the Koszul property of morphisms of algebraic
spaces, **Stacks 06C7**. That argument is
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocalCompleteIntersection_baseChange` of
`StacksFrontier.AlgebraicGeometry.Stacks.LocalCompleteIntersectionFlatBaseChange`, stated there
under the further assumption that the Koszul property of morphisms of algebraic spaces is smooth
local on the source-and-target (**Stacks 06FC** at that property). That assumption is a theorem of
this library, `AlgebraicGeometry.Space.isLocalCompleteIntersection_isSmoothLocalOnSourceAndTarget`
(from **Stacks 0CHN** and the syntomic case of **Stacks 0CHM** through the criterion
**Stacks 06FB**), and it is discharged here.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocalCompleteIntersection_baseChange_of_isFlat`:
  **Stacks 0CJ5**.

## References

* [Stacks Project, Tag 06C7](https://stacks.math.columbia.edu/tag/06C7)
* [Stacks Project, Tag 06FC](https://stacks.math.columbia.edu/tag/06FC)
* [Stacks Project, Tag 06FQ](https://stacks.math.columbia.edu/tag/06FQ)
* [Stacks Project, Tag 0CHM](https://stacks.math.columbia.edu/tag/0CHM)
* [Stacks Project, Tag 0CHN](https://stacks.math.columbia.edu/tag/0CHN)
* [Stacks Project, Tag 0CJ5](https://stacks.math.columbia.edu/tag/0CJ5)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CJ5.** A flat base change of a local complete intersection 1-morphism of algebraic
stacks over `S` is a local complete intersection 1-morphism: if `Q` is a 2-fibre product of the
cospan `(g, f)` of algebraic stacks, `g` is flat and `f` is Koszul, then the projection
`Q.fst` to the source of `g` is Koszul.

This is the flat base-change argument
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocalCompleteIntersection_baseChange`, with the smooth
source-and-target locality of the Koszul property of morphisms of algebraic spaces (Stacks 06FC
at that property) supplied by
`AlgebraicGeometry.Space.isLocalCompleteIntersection_isSmoothLocalOnSourceAndTarget`. The
statement has exactly the source's data: the cospan leg `g` is flat in the sense of Stacks 06PW
(`IsFlat`), `f` is a local complete intersection 1-morphism in the sense of Stacks 0CJ3
(`IsLocalCompleteIntersection`), and `Q` is any 2-fibre product of the cospan. -/
@[stacks 0CJ5 "registered form: flat base change of a local complete intersection 1-morphism of \
algebraic stacks, along any 2-fibre product of the cospan"]
theorem isLocalCompleteIntersection_baseChange_of_isFlat
    {𝒳 𝒴 𝒴' : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴) (hg : IsFlat B S hS g)
    (Q : Bicategory.TwoCommSq g f)
    (hQ : Bicategory.IsTwoFibreProduct Q)
    (hf : IsLocalCompleteIntersection B S hS f) :
    IsLocalCompleteIntersection B S hS Q.fst :=
  isLocalCompleteIntersection_baseChange B S hS
    (Space.isLocalCompleteIntersection_isSmoothLocalOnSourceAndTarget B S hS) f g hg Q hQ hf

end AlgebraicGeometry.Stack.AlgebraicStacks

end
