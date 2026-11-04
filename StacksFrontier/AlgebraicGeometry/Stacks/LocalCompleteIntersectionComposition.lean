module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.Composition
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalCompleteIntersectionMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismComp

/-!
# Composition of local complete intersection 1-morphisms of algebraic stacks (Stacks 0CJ4)

**Stacks 0CJ4** says that a composition of local complete intersection 1-morphisms of algebraic
stacks over `S` is a local complete intersection 1-morphism: if `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` are
Koszul, so is `f ≫ g`.

The source proves it by citing the general composition remark **Stacks 06FP** at the Koszul
property of morphisms of algebraic spaces, whose own stability under composition is **Stacks
06C8**. That is the route taken here, with
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_comp` for the former and
`AlgebraicGeometry.Space.isLocalCompleteIntersection_comp` for the latter.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocalCompleteIntersection_comp`: **Stacks 0CJ4**.

## Implementation notes

Stacks 0CJ3 defines the Koszul property of a 1-morphism of algebraic stacks by the *universal*
smooth-diagram criterion of **Stacks 06FM**, while Stacks 06FP concludes about the *existential*
one, so the two hypotheses and the conclusion are all moved across the equivalence of conditions
(1) and (2) of Stacks 06FM. This is exactly what the sibling
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocalCompleteIntersection_baseChange`
(**Stacks 0CJ5**) does for the base-change remark, and the two carried hypotheses below are the
same two it carries, for the same reasons.

The general composition remark is instantiated in its *universal-form* shape,
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_comp`, rather than in the diagram-building
shape `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_comp_of_precomp`. The latter asks
less of the property — only precomposition-stability, composition-stability and base change on
algebraic spaces — but it does not ask less *here*: its conclusion is again the existential
criterion, so smooth locality on the source-and-target would still be needed to return to Stacks
0CJ3, and the Koszul property of morphisms of algebraic spaces is not known to be stable under
arbitrary base change, which that form wants. Nothing would be gained, so the form matching the
source's citation is used.

## Carried hypothesis

The statement below carries one hypothesis beyond the source's, the same one carried by Stacks
0CJ5 in `StacksFrontier/AlgebraicGeometry/Stacks/LocalCompleteIntersectionFlatBaseChange.lean`.

It is `hlocal`, that the Koszul property of morphisms of *algebraic spaces* over `S` is
smooth local on the source-and-target, which is **Stacks 06FC** at that property. It is what
crosses the equivalence of conditions (1) and (2) of Stacks 06FM, in both directions, and it is
not available: the criterion `AlgebraicGeometry.Space.isSmoothLocalOnSourceAndTarget`
(**Stacks 06FB**) asks for locality at the source and at the target for the smooth topology, and
the transfer of those from schemes to algebraic spaces is missing for the syntomic and fpqc
topologies — the same two gaps, **Stacks 06F0** and **Stacks 0428**, that
`AlgebraicGeometry.Space.isSyntomic_isSmoothLocalOnSourceAndTarget` carries; see the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/LocalOnSourceAndTarget/Syntomic.lean`.

Nothing else is assumed. In particular Stacks 06C8 itself,
`AlgebraicGeometry.Space.isLocalCompleteIntersection_comp`, now carries no hypothesis beyond its
source's: the étale source locality of the Koszul property of morphisms of *schemes* it needs,
**Stacks 069P** restricted to étale coverings, is
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

/-- **Stacks 0CJ4.** A composition of local complete intersection 1-morphisms of algebraic stacks
over `S` is a local complete intersection 1-morphism: if `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` are Koszul,
so is `f ≫ g`.

This is the general composition remark **Stacks 06FP**,
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_comp`, at the Koszul property of
morphisms of algebraic spaces, which is stable under composition by **Stacks 06C8**. Stacks 0CJ3
is the universal smooth-diagram criterion of **Stacks 06FM** where that remark speaks about the
existential one, so the hypotheses and the conclusion are moved across the equivalence of
conditions (1) and (2) of Stacks 06FM.

One hypothesis beyond the source's is carried: `hlocal`, that the Koszul property of morphisms of
algebraic spaces is smooth local on the source-and-target (**Stacks 06FC** at that property),
which is what crosses that equivalence. It is not available in this library; see the
carried-hypothesis note in the module docstring. -/
@[stacks 0CJ4 "the composition argument in full, carrying one hypothesis this library does not \
prove: `hlocal`, Stacks 06FC at the Koszul property of morphisms of algebraic spaces"]
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
