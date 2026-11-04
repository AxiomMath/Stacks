module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismSurjectiveDiagram
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjectsRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedDiagonalCriterion

/-!
# Étale 1-morphisms of algebraic stacks are the flat unramified ones (Stacks 0CJ1)

Stacks 0CJ1 asserts, for a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S`, the equivalence of

1. `f` is étale (**Stacks 0CIL**);
2. `f` is locally of finite presentation (**Stacks 06Q2**, part (1)), flat (**Stacks 06PW**) and
   unramified (**Stacks 0CIT**);
3. `f` is locally of finite presentation, flat, and its relative diagonal is étale.

This file proves the implications (1) ⇒ (2) and (2) ⇒ (1), each a separate declaration; (1) ⇒ (2)
carries the existence of a suitable diagram as a hypothesis. The full equivalence of Stacks 0CJ1
is `AlgebraicGeometry.Stack.AlgebraicStacks.isEtale_tfae`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks`
  `.isEtale_of_isLocallyOfFinitePresentation_of_isFlat_of_isUnramified`: **(2) ⇒ (1)**, with no
  extra hypothesis.
* `AlgebraicGeometry.Stack.AlgebraicStacks`
  `.isLocallyOfFinitePresentation_isFlat_isUnramified_of_isEtale`: **(1) ⇒ (2)**, carrying
  `AlgebraicGeometry.Stack.HasSurjectiveEtaleSmoothDiagram` as a hypothesis.
* `AlgebraicGeometry.Stack.isRelativelySmooth_of_etaleSmoothDiagram`: on a diagram of algebraic
  spaces over `f` with smooth right-hand vertical 1-morphism and étale comparison to the 2-fibre
  product, the left-hand vertical 1-morphism is smooth.

## Implementation notes

The four notions involved are built from *two different* diagram tests, and that is what decides
which implications are free and which are not.

`AlgebraicGeometry.Stack.IsEtale` (0CIL) and `AlgebraicGeometry.Stack.IsUnramified` (0CIT) are
the Deligne–Mumford condition together with the **universal étale-smooth** diagram test
`AlgebraicGeometry.Stack.HasPropertyOnEveryEtaleSmoothDiagram` — condition (1) of
**Stacks 0CIF** — at étaleness, resp. unramifiedness, of morphisms of algebraic spaces.
`AlgebraicGeometry.Stack.AlgebraicStacks.IsLocallyOfFinitePresentation` (06Q2) is the
**universal smooth** test `AlgebraicGeometry.Stack.HasPropertyOnEverySmoothDiagram` — condition
(1) of **Stacks 06FM** — and `AlgebraicGeometry.Stack.AlgebraicStacks.IsFlat` (06PW) is the
**existential smooth** test, condition (2) of Stacks 06FM, written out longhand; the two smooth
tests are identified by `AlgebraicGeometry.Stack.hasPropertyOnEverySmoothDiagram_iff_some`, the
equivalence of parts (1) and (2) of Stacks 06FM.

No implication is true by definition. Étaleness of a *morphism of algebraic spaces* is not
defined as flat plus unramified plus locally of finite presentation in this library — it is
Stacks 03FR, and the comparison is **Stacks 06CR** and **Stacks 06LU**,
`AlgebraicGeometry.Space.isUnramified_of_isEtale` and
`AlgebraicGeometry.Space.isEtale_of_isFlat_of_isUnramified`, which carry real content. On the
stack side the three conditions are moreover tested on three different families of diagrams, so
even the unfolded propositions do not match.

**(2) ⇒ (1)** needs no hypothesis. Given a diagram the universal étale-smooth test hands us, its
left-hand vertical 1-morphism is smooth by
`AlgebraicGeometry.Stack.isRelativelySmooth_of_etaleSmoothDiagram` and its comparisons are smooth
by `AlgebraicGeometry.Stack.isRelativelySmooth_of_isRelativelyEtale`, so it is also a diagram the
universal *smooth* test applies to; local finite presentation is read off it directly, flatness
after passing from the existential smooth test to the universal one, and unramifiedness is the
hypothesis on that very diagram. Stacks 06LU then gives étaleness of the top horizontal
morphism, and Deligne–Mumfordness comes from unramifiedness.

**(1) ⇒ (2)** needs one input: the universal étale-smooth test has to be turned
into the existential one, which by
`AlgebraicGeometry.Stack`
`.hasPropertyOnSomeEtaleSmoothDiagram_of_hasPropertyOnEveryEtaleSmoothDiagram`
is exactly the *existence* of one diagram over `f` with smooth right-hand vertical 1-morphism,
surjective left-hand vertical 1-morphism and étale comparisons —
`AlgebraicGeometry.Stack.HasSurjectiveEtaleSmoothDiagram`, taken here as a hypothesis. For a
Deligne–Mumford `f` that existence is **Stacks 0CIA**, resting on the structure theorem
**Stacks 06N3** (`AlgebraicGeometry.Stack.hasSurjectiveEtaleSmoothDiagram_of_isDM_of_forward` at
`AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM`), and that is how
`AlgebraicGeometry.Stack.AlgebraicStacks.isEtale_tfae` discharges it. Given the diagram,
its top morphism is étale, hence flat (**Stacks 0467**) and locally of finite presentation
(**Stacks 0468**), and the diagram is a smooth one in the sense of Stacks 06FM:
its left leg is smooth as above and surjective on objects because it is surjective on points
(`AlgebraicGeometry.Stack.pointsMap_surjective_iff_isRelativelySurjective` and
`AlgebraicGeometry.Stack.isSurjectiveOnObjects_iff_isRelativelySurjective`). Unramifiedness is
**Stacks 0CIW**, `AlgebraicGeometry.Stack.isUnramified_of_isEtale`, which needs nothing.

**(2) ⇔ (3)** is not proved in this file; it is part of
`AlgebraicGeometry.Stack.AlgebraicStacks.isEtale_tfae`, cited above.

`AlgebraicGeometry.Stack.isRelativelySmooth_of_etaleSmoothDiagram` is smoothness of a composite
(**Stacks 045B**) applied to the comparison 1-morphism and to the second projection of the
canonical 2-fibre product square. The point is that the canonical
comparison `CategoryTheory.CatFiberedInGroupoids.canonicalPreHom` composed with that projection
is the diagram's left leg *on the nose*
(`CategoryTheory.CatFiberedInGroupoids.canonicalPreHom_comp_snd` is `rfl`), so no transport along
a 2-isomorphism is needed.

## References

* [Stacks Project, Tag 0467](https://stacks.math.columbia.edu/tag/0467)
* [Stacks Project, Tag 0468](https://stacks.math.columbia.edu/tag/0468)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 06CR](https://stacks.math.columbia.edu/tag/06CR)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06LU](https://stacks.math.columbia.edu/tag/06LU)
* [Stacks Project, Tag 06PW](https://stacks.math.columbia.edu/tag/06PW)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
* [Stacks Project, Tag 06Q5](https://stacks.math.columbia.edu/tag/06Q5)
* [Stacks Project, Tag 0CIA](https://stacks.math.columbia.edu/tag/0CIA)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
* [Stacks Project, Tag 0CIL](https://stacks.math.columbia.edu/tag/0CIL)
* [Stacks Project, Tag 0CIT](https://stacks.math.columbia.edu/tag/0CIT)
* [Stacks Project, Tag 0CIW](https://stacks.math.columbia.edu/tag/0CIW)
* [Stacks Project, Tag 0CJ0](https://stacks.math.columbia.edu/tag/0CJ0)
* [Stacks Project, Tag 0CJ1](https://stacks.math.columbia.edu/tag/0CJ1)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The left leg of an étale-smooth diagram is smooth.** Let

```
U ---h---> V
|          |
a          b
v          v
𝒳 ---f---> 𝒴
```

2-commute, with `U`, `V` algebraic spaces over `S`, `b` smooth and every comparison 1-morphism
from the diagram's cone to a 2-fibre product of `(b, f)` étale. Then `a` is smooth.

The canonical comparison into the canonical 2-fibre product square composed with that square's
second projection *is* `a`, by `CategoryTheory.CatFiberedInGroupoids.canonicalPreHom_comp_snd`;
the comparison is smooth because it is étale, the projection is smooth because `b` is, and
smoothness is stable under composition. -/
theorem isRelativelySmooth_of_etaleSmoothDiagram
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) (hV : IsAlgebraicSpace B S hS V)
    (a : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (b : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴)
    (h : U ⟶ V)
    (η : (associatedMap B S hS h).1 ≫ b.hom ≅ a.hom ≫ f.hom)
    (hb : IsRelativelySmooth B S hS b.hom)
    (hk : ∀ (Q : Bicategory.TwoCommSq b.hom f.hom)
      (_hQ : Bicategory.IsTwoFibreProduct Q)
      (k : Bicategory.TwoCommSq.PreHom (diagramCone B S hS f.hom a.hom b.hom h η) Q),
        IsRelativelyEtale B S hS k.hom) :
    IsRelativelySmooth B S hS a.hom :=
  isRelativelySmooth_comp B S hS _ _
    (isRelativelySmooth_of_isRelativelyEtale B S hS _
      (hk (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b.hom f.hom)
        (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
          b.hom f.hom)
        (CatFiberedInGroupoids.canonicalPreHom.{u, u, u + 1, u + 1} b.hom f.hom
          (diagramCone B S hS f.hom a.hom b.hom h η))))
    (isRelativelySmooth_twoFibreProductSnd B S hS b.hom f.hom hb)

namespace AlgebraicStacks

/-- The existential smooth-diagram test of Stacks 06FM holds at any property that étale
morphisms of algebraic spaces over `S` have, for an étale 1-morphism of algebraic stacks
admitting a diagram as in `AlgebraicGeometry.Stack.HasSurjectiveEtaleSmoothDiagram`.

The given diagram passes the universal étale-smooth test, so its top morphism is étale and has
the property; its right leg is smooth by hypothesis, its left leg is smooth by
`AlgebraicGeometry.Stack.isRelativelySmooth_of_etaleSmoothDiagram` and surjective on objects
because it is surjective on points. -/
theorem hasPropertyOnSomeSmoothDiagram_of_isEtale
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hex : Stack.HasSurjectiveEtaleSmoothDiagram.{u, w} B S hS f)
    (hf : Stack.IsEtale B S hS f)
    (hP : ∀ {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS V →
      ∀ g : U ⟶ V, Space.IsEtale B S hS g → P g) :
    Stack.HasPropertyOnSomeSmoothDiagram B S hS P f.hom := by
  obtain ⟨U, V, hU, hV, a, b, h, η, hasurj, hb, hk⟩ := hex
  have hasm : Stack.IsRelativelySmooth B S hS a.hom :=
    Stack.isRelativelySmooth_of_etaleSmoothDiagram B S hS f hU hV a b h η hb hk
  refine ⟨U, V, hU, hV, a.hom, b.hom, h, ⟨η⟩, hasm, ?_, hb,
    hP hV h (hf.2 U V hU hV a b h η hb hk)⟩
  exact (Stack.isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u + 1}
      B S hS a.hom hasm.1).mpr
    ((Stack.pointsMap_surjective_iff_isRelativelySurjective.{u, w, u + 1}
      B S hS a hasm.1).mp hasurj)

/-- **Stacks 0CJ1, (1) ⇒ (2).** An étale 1-morphism of algebraic stacks over `S` admitting a
diagram as in `AlgebraicGeometry.Stack.HasSurjectiveEtaleSmoothDiagram` — what Stacks 0CIA
provides for a Deligne–Mumford 1-morphism — is locally of finite presentation, flat and
unramified.

Unramifiedness is Stacks 0CIW and needs no diagram. For the other two the diagram turns the
universal étale-smooth test into the existential smooth test of Stacks 06FM, whose top morphism
is étale, hence locally of finite presentation by Stacks 0468 and flat by Stacks 0467; the
universal smooth test that local finite presentation is stated by is then recovered from the
existential one by Stacks 06FM, while flatness is the existential test on the nose. -/
theorem isLocallyOfFinitePresentation_isFlat_isUnramified_of_isEtale
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hex : Stack.HasSurjectiveEtaleSmoothDiagram.{u, w} B S hS f)
    (hf : Stack.IsEtale B S hS f) :
    IsLocallyOfFinitePresentation B S hS f ∧ IsFlat B S hS f ∧
      Stack.IsUnramified B S hS f := by
  refine ⟨?_, ?_, Stack.isUnramified_of_isEtale B S hS hf⟩
  · exact (Stack.hasPropertyOnEverySmoothDiagram_iff_some B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
      𝒳.property 𝒴.property f.hom).mpr
      (hasPropertyOnSomeSmoothDiagram_of_isEtale B S hS _ f hex hf
        (fun hV g hg => Space.isLocallyOfFinitePresentation_of_isEtale B S hS hg))
  · exact (isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS f).2
      (hasPropertyOnSomeSmoothDiagram_of_isEtale B S hS _ f hex hf
        (fun hV g hg => Space.isFlat_of_isEtale B S hS hg))

/-- **Stacks 0CJ1, (2) ⇒ (1).** A 1-morphism of algebraic stacks over `S` which is locally of
finite presentation, flat and unramified is étale. No diagram has to be supplied.

Deligne–Mumfordness is part of unramifiedness. For the universal étale-smooth test, take a
diagram it offers: its right leg is smooth, its left leg is smooth by
`AlgebraicGeometry.Stack.isRelativelySmooth_of_etaleSmoothDiagram` and its comparisons are smooth
because they are étale, so the universal *smooth* test of Stacks 06FM applies to it as well. That
gives local finite presentation of its top morphism directly, and flatness after Stacks 06FM
turns the existential test of Stacks 06PW into the universal one; unramifiedness is the
hypothesis at that diagram. Stacks 06LU concludes. -/
@[stacks 0CJ1 "part (2) implies part (1)"]
theorem isEtale_of_isLocallyOfFinitePresentation_of_isFlat_of_isUnramified
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hlfp : IsLocallyOfFinitePresentation B S hS f) (hflat : IsFlat B S hS f)
    (hunr : Stack.IsUnramified B S hS f) :
    Stack.IsEtale B S hS f := by
  have hflatEvery : Stack.HasPropertyOnEverySmoothDiagram B S hS
      (fun _ _ q => Space.IsFlat B S hS q) f.hom :=
    (Stack.hasPropertyOnEverySmoothDiagram_iff_some B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_flat B S hS)
      𝒳.property 𝒴.property f.hom).mpr
      ((isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS f).1 hflat)
  refine ⟨hunr.1, fun U V hU hV a b h η hb hk => ?_⟩
  have hasm : Stack.IsRelativelySmooth B S hS a.hom :=
    Stack.isRelativelySmooth_of_etaleSmoothDiagram B S hS f hU hV a b h η hb hk
  have hksm : ∀ (Q : Bicategory.TwoCommSq b.hom f.hom)
      (_hQ : Bicategory.IsTwoFibreProduct Q)
      (k : Bicategory.TwoCommSq.PreHom (Stack.diagramCone B S hS f.hom a.hom b.hom h η) Q),
        Stack.IsRelativelySmooth B S hS k.hom :=
    fun Q hQ k => Stack.isRelativelySmooth_of_isRelativelyEtale B S hS _ (hk Q hQ k)
  exact Space.isEtale_of_isFlat_of_isUnramified B S hS hU hV h
    (hlfp U V hU hV a.hom b.hom h η hasm hb hksm)
    (hflatEvery U V hU hV a.hom b.hom h η hasm hb hksm)
    (hunr.2 U V hU hV a b h η hb hk)

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
