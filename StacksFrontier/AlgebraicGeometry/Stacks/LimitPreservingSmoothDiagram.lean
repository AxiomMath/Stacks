module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.LimitPreservingOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureMorphism

/-!
# Relative limit preservation on a smooth diagram of a finitely presented 1-morphism

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over a scheme `S` which is locally of finite
presentation in the sense of Stacks 06Q2. Then `f` admits a smooth diagram

```
U ---h---> V
|          |
a          b
v          v
𝒳 ---f---> 𝒴
```

of algebraic spaces over `S`, with `a` smooth and surjective on objects and `b` smooth, whose top
horizontal morphism `h` is *relatively limit preserving* in the sense of Stacks 049J: for every
section of `V` the presheaf of its lifts along `h` turns a cofiltered inverse limit of affine
schemes into a filtered colimit of sets.

Specialised to the structure morphism of Stacks 050D this is the first step of the proof of
Stacks 0CMX: an algebraic stack whose morphism to the base is locally of finite presentation has
a smooth surjective presentation by an algebraic space which is relatively limit preserving over
the base.

## Main results

* `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_relativelyLimitPreserving`: a locally
  finitely presented 1-morphism of algebraic stacks has a smooth diagram whose morphism of
  algebraic spaces is relatively limit preserving.
* `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_relativelyLimitPreserving_structure`:
  the same for the structure morphism of an algebraic stack to its base.

## Implementation notes

Stacks 06Q2 part (1) is the *universal* smooth-diagram test of Stacks 06FM, and the diagram
produced here is the *existential* one, so the passage between them is
`AlgebraicGeometry.Stack.hasPropertyOnEverySmoothDiagram_iff_some` at local finite presentation of
morphisms of algebraic spaces, which is smooth local on the source-and-target by Stacks 06FC
(`AlgebraicGeometry.Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation`). Local
finite presentation of the resulting morphism of algebraic spaces is then upgraded to relative
limit preservation by **Stacks 04AK**, which is proved as
`AlgebraicGeometry.relativelyLimitPreserving_of_isLocallyOfFinitePresentation`; that is the whole
of the algebraic-spaces input to Stacks 0CMX.

*Why no Stacks 0CMX attribute is placed here.* Stacks 0CMX concludes that the algebraic stack
`𝒳` is limit preserving in the sense of Artin's Axioms, Definition 07XL, which this repository
carries as `Deformation.Artin.IsLimitPreserving`: the comparison functor
`colim 𝒳_{Tᵢ} ⥤ 𝒳_T` is an equivalence for every cofiltered inverse system of affine schemes over
`S` with limit `T`. That conclusion does **not** follow from the diagram produced here. The
source's proof continues by presenting `𝒳` as the quotient stack `[U/R]` of the smooth groupoid in
algebraic spaces attached to the presentation (Stacks 04T5, part (2), which this repository
carries as
`AlgebraicGeometry.Stack.SelfIntersection.exists_equivalenceOver_canonicalMap_of_isSmooth`), and
then verifies the comparison for `[U/R]` directly from the descent-datum description of its fibre
categories (Stacks 044X), refining an fppf covering of the limit to a standard one (Stacks 049N)
and descending it, together with the local sections and transition arrows, to a finite stage. The
two declarations that step needs are absent from this repository. The first is limit preservation
of a quotient stack,

```
theorem AlgebraicGeometry.Stack.isLimitPreserving_quotientStackCFG
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
    (hobjects : RelativelyLimitPreserving.{u, u, u, u} C S hS G.objectsToBase.hom)
    (harrows : RelativelyLimitPreserving.{u, u, u, u} C S hS G.arrowsToBase.hom) :
    Deformation.Artin.IsLimitPreserving C S hS (quotientStackCFG C S hS G)
```

The second declaration that step needs — the transport of Definition 07XL along an equivalence of
categories fibred in groupoids over the site, which is what carries the conclusion back from
`[U/R]` to `𝒳` — is **no longer** absent: it is
`AlgebraicGeometry.Stack.isLimitPreserving_of_equivalenceOver` of
`StacksFrontier/AlgebraicGeometry/Stacks/LimitPreservingEquivalence.lean`, together with its `iff`
form, which is the shape this step wants because
`AlgebraicGeometry.Stack.SelfIntersection.exists_equivalenceOver_canonicalMap_of_isSmooth` hands
out an equivalence in the direction `[U/R] ⟶ 𝒳`. So of the two steps only limit preservation of
the quotient stack remains, and the obstruction there is specific: `quotientStack G` is not a
concrete category of descent data but an abstract stackification, reachable only through the
Stacks 044X presenting-descent-datum API, and bridging that to Stacks 049N needs the refinement of
an arbitrary fppf covering sieve of an affine object to a finite standard covering, a
base-change-of-a-limit-cone lemma in the big affine fppf site, and filtered descent of the cocycle
equations for sections of the arrow space. None of those three is in the repository.

Accordingly the Stacks 0CMX attribute in this file sits on
`hasPropertyOnSomeSmoothDiagram_relativelyLimitPreserving_structure` with a clause string
restricting it to the smooth-diagram reduction, and nothing here carries the tag unqualified. No
declaration in this module asserts anything about `Deformation.Artin.IsLimitPreserving` for `𝒳`;
that conclusion is the tag's, and it is not proved.

## References

* [Stacks Project, Tag 049J](https://stacks.math.columbia.edu/tag/049J)
* [Stacks Project, Tag 04AK](https://stacks.math.columbia.edu/tag/04AK)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
* [Stacks Project, Tag 0CMX](https://stacks.math.columbia.edu/tag/0CMX)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A locally finitely presented 1-morphism of algebraic stacks has a smooth diagram whose
morphism of algebraic spaces is relatively limit preserving.** If `f : 𝒳 ⟶ 𝒴` is locally of
finite presentation in the sense of Stacks 06Q2, there is a 2-commutative square of algebraic
spaces over `f` whose two vertical 1-morphisms are smooth, whose left vertical 1-morphism is
surjective on objects, and whose top horizontal morphism is relatively limit preserving in the
sense of Stacks 049J.

Stacks 06Q2 part (1) is the universal smooth-diagram test of Stacks 06FM, so the existential
diagram comes from the equivalence of the two conditions, and local finite presentation of its
top horizontal morphism becomes relative limit preservation by **Stacks 04AK**. -/
theorem hasPropertyOnSomeSmoothDiagram_relativelyLimitPreserving
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : Stack.AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f) :
    HasPropertyOnSomeSmoothDiagram B S hS
      (fun _ _ h => RelativelyLimitPreserving.{u, u, u, u} B S hS h) f.hom := by
  obtain ⟨U, V, hU, hV, a, b, h, hη, ha, hasurj, hb, hPh⟩ :=
    (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
      (fun _ _ k => Space.IsLocallyOfFinitePresentation B S hS k)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
      𝒳.property 𝒴.property f.hom).1 hf
  exact ⟨U, V, hU, hV, a, b, h, hη, ha, hasurj, hb,
    relativelyLimitPreserving_of_isLocallyOfFinitePresentation B S hS hU hV hPh⟩

/-- **An algebraic stack locally of finite presentation over its base has a relatively limit
preserving smooth presentation.** This is
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_relativelyLimitPreserving` at the
structure morphism of Stacks 050D, and it is the algebraic-spaces input to the proof of
Stacks 0CMX: the presenting algebraic space of `𝒳` is relatively limit preserving over the
algebraic stack represented by `S`.

The attribute's clause string is deliberately narrow. This statement does **not** give the
conclusion of Stacks 0CMX, which is limit preservation of `𝒳` in the sense of Definition 07XL;
what it carries is the tag's first step, and it is the step that consumes the tag's hypothesis —
`Stack.AlgebraicStacks.IsLocallyOfFinitePresentation` on the structure morphism of Stacks 050D is
used, not merely stated. Anyone reading the tag as discharged by this declaration would be
misreading it: the conclusion here is about a smooth presentation by an algebraic space, in the
vocabulary of Stacks 049J, and the remaining step — limit preservation of the quotient stack — is
named with its three missing bridges in the implementation notes of this module. -/
@[stacks 0CMX "only the smooth-diagram reduction; the conclusion is not 07XL"]
theorem hasPropertyOnSomeSmoothDiagram_relativelyLimitPreserving_structure
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : Stack.AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
      (structureMorphism B S hS 𝒳)) :
    HasPropertyOnSomeSmoothDiagram B S hS
      (fun _ _ h => RelativelyLimitPreserving.{u, u, u, u} B S hS h)
      (structureMorphism B S hS 𝒳).hom :=
  hasPropertyOnSomeSmoothDiagram_relativelyLimitPreserving B S hS
    (structureMorphism B S hS 𝒳) h𝒳

end AlgebraicGeometry.Stack

end
