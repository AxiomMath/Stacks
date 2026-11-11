module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.Composition
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalCompleteIntersectionMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismComp

/-!
# Composition of local complete intersection 1-morphisms of algebraic stacks: the argument

**Stacks 0CJ4** says that a composition of local complete intersection 1-morphisms of algebraic
stacks over `S` is a local complete intersection 1-morphism: if `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` are
Koszul, so is `f ≫ g`.

The source proves it by citing the general composition remark **Stacks 06FP** at the Koszul
property of morphisms of algebraic spaces, whose own stability under composition is **Stacks
06C8**. This file runs that argument, with
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_comp` for the former and
`AlgebraicGeometry.Space.isLocalCompleteIntersection_comp` for the latter, parametrised by the
smooth locality on the source-and-target of the Koszul property of morphisms of algebraic spaces
that the argument consumes. That locality is
`AlgebraicGeometry.Space.isLocalCompleteIntersection_isSmoothLocalOnSourceAndTarget`, and
**Stacks 0CJ4** itself, with exactly the source's hypotheses, is
`AlgebraicGeometry.Stack.AlgebraicStacks.IsLocalCompleteIntersection.comp` in
`StacksFrontier.AlgebraicGeometry.Stacks.LocalCompleteIntersectionComp`.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocalCompleteIntersection_comp`: the composition
  argument of Stacks 0CJ4, for a given smooth locality on the source-and-target of the Koszul
  property of morphisms of algebraic spaces.

## Implementation notes

Stacks 0CJ3 defines the Koszul property of a 1-morphism of algebraic stacks by the *universal*
smooth-diagram criterion of **Stacks 06FM**, while Stacks 06FP concludes about the *existential*
one, so the two hypotheses and the conclusion are all moved across the equivalence of conditions
(1) and (2) of Stacks 06FM. This is exactly what the sibling
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocalCompleteIntersection_baseChange`
(**Stacks 0CJ5**) does for the base-change remark.

The general composition remark is instantiated in its *universal-form* shape,
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_comp`, rather than in the diagram-building
shape `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_comp_of_precomp`. The latter asks
less of the property — only precomposition-stability, composition-stability and base change on
algebraic spaces — but it does not ask less *here*: its conclusion is again the existential
criterion, so smooth locality on the source-and-target would still be needed to return to Stacks
0CJ3, and the Koszul property of morphisms of algebraic spaces is stable only under flat base
change, not the arbitrary base change that form wants. Nothing would be gained, so the form
matching the source's citation is used.

The argument `hlocal` is the smooth locality on the source-and-target of the Koszul property of
morphisms of *algebraic spaces* over `S` (**Stacks 06FC** at that property), which is what
crosses the equivalence of conditions (1) and (2) of Stacks 06FM, in both directions. The library
proves it as `AlgebraicGeometry.Space.isLocalCompleteIntersection_isSmoothLocalOnSourceAndTarget`,
from syntomic locality on the source (**Stacks 0CHN**) and on the target (the syntomic case of
**Stacks 0CHM**) through the criterion **Stacks 06FB**; it is kept as an argument here only so
that this file does not import that development.

Stacks 06C8 itself, `AlgebraicGeometry.Space.isLocalCompleteIntersection_comp`, carries no
hypothesis beyond its source's: the étale source locality of the Koszul property of morphisms of
*schemes* it needs, **Stacks 069P** restricted to étale coverings, is
`AlgebraicGeometry.isLocalCompleteIntersectionMorphism_isLocalAtSource_etale`.

## References

* [Stacks Project, Tag 06C8](https://stacks.math.columbia.edu/tag/06C8)
* [Stacks Project, Tag 06FB](https://stacks.math.columbia.edu/tag/06FB)
* [Stacks Project, Tag 06FC](https://stacks.math.columbia.edu/tag/06FC)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FP](https://stacks.math.columbia.edu/tag/06FP)
* [Stacks Project, Tag 069P](https://stacks.math.columbia.edu/tag/069P)
* [Stacks Project, Tag 0CJ3](https://stacks.math.columbia.edu/tag/0CJ3)
* [Stacks Project, Tag 0CJ4](https://stacks.math.columbia.edu/tag/0CJ4)
* [Stacks Project, Tag 0CJ5](https://stacks.math.columbia.edu/tag/0CJ5)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The composition argument of **Stacks 0CJ4**: given that the Koszul property of morphisms of
algebraic spaces is smooth local on the source-and-target (`hlocal`, **Stacks 06FC** at that
property), a composition of local complete intersection 1-morphisms of algebraic stacks over `S`
is a local complete intersection 1-morphism.

This is the general composition remark **Stacks 06FP**,
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_comp`, at the Koszul property of
morphisms of algebraic spaces, which is stable under composition by **Stacks 06C8**. Stacks 0CJ3
is the universal smooth-diagram criterion of **Stacks 06FM** where that remark speaks about the
existential one, so the hypotheses and the conclusion are moved across the equivalence of
conditions (1) and (2) of Stacks 06FM, which `hlocal` provides.

The library proves `hlocal` as
`AlgebraicGeometry.Space.isLocalCompleteIntersection_isSmoothLocalOnSourceAndTarget`; Stacks 0CJ4
with exactly the source's hypotheses is
`AlgebraicGeometry.Stack.AlgebraicStacks.IsLocalCompleteIntersection.comp`. -/
theorem isLocalCompleteIntersection_comp
    (hlocal : Space.IsSmoothLocalOnSourceAndTarget B S hS
      (fun _ _ k => Space.IsLocalCompleteIntersection B S hS k))
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : IsLocalCompleteIntersection B S hS f)
    (hg : IsLocalCompleteIntersection B S hS g) :
    IsLocalCompleteIntersection B S hS (f ≫ g) := by
  have key := @Stack.hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
    (fun _ _ k => Space.IsLocalCompleteIntersection B S hS k) hlocal
  exact (key 𝒳.property 𝒵.property (f ≫ g).hom).2
    (Stack.hasPropertyOnSomeSmoothDiagram_comp.{u, w} B S hS
      (fun _ _ k => Space.IsLocalCompleteIntersection B S hS k) hlocal
      (fun hU hV hW p q hp hq =>
        Space.isLocalCompleteIntersection_comp B S hS hU hV hW p q hp hq)
      𝒳.property 𝒴.property 𝒵.property f.hom g.hom
      ((key 𝒳.property 𝒴.property f.hom).1 hf) ((key 𝒴.property 𝒵.property g.hom).1 hg))

end AlgebraicGeometry.Stack.AlgebraicStacks

end
