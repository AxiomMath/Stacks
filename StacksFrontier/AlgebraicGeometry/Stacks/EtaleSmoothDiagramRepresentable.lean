module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSourceAndTarget.EtaleSmoothExamples
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartTargetDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismRelativeConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismSurjectiveDiagram

/-!
# The étale-smooth diagram of a 1-morphism representable by algebraic spaces

`AlgebraicGeometry.Stack.HasSurjectiveEtaleSmoothDiagram` — the diagram data of condition (2)
of **Stacks 0CIF** with the clause about the property dropped — is *unconditional* for a
1-morphism of algebraic stacks which is representable by algebraic spaces. The diagram is the
one `AlgebraicGeometry.Stack.hasPropertyOnSomeEtaleSmoothDiagram_of_hasRelativeProperty` already
builds out of a presentation of the target and the base change of the 1-morphism along it; at
the property `⊤` that lemma's hypothesis is vacuous, so what it delivers is exactly the diagram.

The consequence is that for a representable 1-morphism the *universal* étale-smooth diagram test
of condition (1) of Stacks 0CIF — the substantive clause of **Stacks 0CIT** (unramifiedness) and
of **Stacks 0CIL** (étaleness) for 1-morphisms of algebraic stacks — agrees with the relative
property of **Stacks 03YK**, in *both* directions. Only one direction was available before: the
other ran through
`Stack.hasPropertyOnSomeEtaleSmoothDiagram_of_hasPropertyOnEveryEtaleSmoothDiagram`,
which wants a diagram, and the only producer of one took an étale presentation of the source as
a hypothesis — **Stacks 0CIA**, which rests on the structure theorem **Stacks 06N3**. That
dependency is *not* needed when the source is representable by an algebraic space, and the
apparent circularity it created is what this file removes.

## Main results

* `AlgebraicGeometry.Stack.hasSurjectiveEtaleSmoothDiagram_of_isRepresentableByAlgebraicSpaces`:
  a 1-morphism representable by algebraic spaces admits a surjective étale-smooth diagram.
* `AlgebraicGeometry.Stack.hasPropertyOnEveryEtaleSmoothDiagram_iff_relative`: for such a
  1-morphism and an étale-smooth local property, the universal étale-smooth diagram test is the
  relative property of Stacks 03YK.
* `AlgebraicGeometry.Stack.hasRelativeProperty_unramified_of_isUnramified` and
  `AlgebraicGeometry.Stack.isUnramified_of_hasRelativeProperty_unramified`: that equivalence
  read at unramifiedness, which is the comparison **Stacks 06N2** needs.

## Implementation notes

No `@[stacks]` attribute. The statements are the implications of Stacks 0CIF restricted to a
representable 1-morphism, and Stacks 0CIF's keys assert them for a Deligne–Mumford one, with the
diagram produced by Stacks 0CIA rather than assumed; so none of these is a covering set for a
key of that tag. The `iff` below is a strictly weaker statement than the one
`AlgebraicGeometry.Stack.hasPropertyOnSomeEtaleSmoothDiagram_iff_relative` already carries the
`"representable morphism"` key for — it replaces the existential diagram test by the universal
one — and is included because the universal test is the one the notions of Stacks 0CIT and
Stacks 0CIL are defined by.

The property `⊤` is used only as a vehicle for the diagram: `HasRelativeProperty` at `⊤` holds
of every 1-morphism, and `HasPropertyOnSomeEtaleSmoothDiagram` at `⊤` is
`HasSurjectiveEtaleSmoothDiagram` together with a clause which is `True`.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 0CG3](https://stacks.math.columbia.edu/tag/0CG3)
* [Stacks Project, Tag 0CIA](https://stacks.math.columbia.edu/tag/0CIA)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
* [Stacks Project, Tag 0CIT](https://stacks.math.columbia.edu/tag/0CIT)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A 1-morphism of algebraic stacks representable by algebraic spaces admits a surjective
étale-smooth diagram.** This is
`AlgebraicGeometry.Stack.HasSurjectiveEtaleSmoothDiagram`, the diagram data of condition (2) of
**Stacks 0CIF**, with no hypothesis beyond representability.

The diagram is the one
`AlgebraicGeometry.Stack.hasPropertyOnSomeEtaleSmoothDiagram_of_hasRelativeProperty` builds from
a smooth presentation of the target: at the property `⊤` the relative-property hypothesis of
that lemma is vacuous, and its conclusion is this diagram together with a clause which is
`True`. In particular no étale presentation of the *source* — **Stacks 0CIA** — is involved. -/
theorem hasSurjectiveEtaleSmoothDiagram_of_isRepresentableByAlgebraicSpaces
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) :
    HasSurjectiveEtaleSmoothDiagram B S hS f := by
  obtain ⟨U, V, hU, hV, a, b, h, η, hasu, hbsm, hcompar, -⟩ :=
    hasPropertyOnSomeEtaleSmoothDiagram_of_hasRelativeProperty.{u, u, w} B S hS
      (⊤ : MorphismProperty (AlgebraicSpaces B S hS)) f hf (fun _ _ _ _ _ _ => trivial)
  exact ⟨U, V, hU, hV, a, b, h, η, hasu, hbsm, hcompar⟩

/-- **For a 1-morphism representable by algebraic spaces the universal étale-smooth diagram test
is the relative property of Stacks 03YK.** For a property `P` of morphisms of algebraic spaces
which is étale-smooth local on source and target, stable under base change and fppf local on the
target, a 1-morphism `f` of algebraic stacks representable by algebraic spaces has `P` on every
étale-smooth diagram if and only if it has `P` relatively. Both implications of the first and
third assertions of **Stacks 0CIF** are available for such a 1-morphism: the backward one through
`AlgebraicGeometry.Stack.hasPropertyOnSomeEtaleSmoothDiagram_of_hasRelativeProperty` followed by
`Stack.hasPropertyOnEveryEtaleSmoothDiagram_of_hasPropertyOnSomeEtaleSmoothDiagram`,
the forward one through
`Stack.hasPropertyOnSomeEtaleSmoothDiagram_of_hasPropertyOnEveryEtaleSmoothDiagram`
— whose diagram is supplied by
`AlgebraicGeometry.Stack.hasSurjectiveEtaleSmoothDiagram_of_isRepresentableByAlgebraicSpaces` —
followed by `AlgebraicGeometry.Stack.hasRelativeProperty_of_hasPropertyOnSomeEtaleSmoothDiagram`.
-/
theorem hasPropertyOnEveryEtaleSmoothDiagram_iff_relative
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (hP : Space.IsEtaleSmoothLocalOnSourceAndTarget B S hS P)
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, v} B S hS)]
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) :
    HasPropertyOnEveryEtaleSmoothDiagram B S hS P f ↔
      HasRelativeProperty.{u, u, u + 1, v} B S hS P f.hom hf :=
  ⟨fun h => hasRelativeProperty_of_hasPropertyOnSomeEtaleSmoothDiagram.{u, v, w} B S hS P hP f hf
      (hasPropertyOnSomeEtaleSmoothDiagram_of_hasPropertyOnEveryEtaleSmoothDiagram B S hS P f
        (hasSurjectiveEtaleSmoothDiagram_of_isRepresentableByAlgebraicSpaces B S hS f hf) h),
    fun h => hasPropertyOnEveryEtaleSmoothDiagram_of_hasPropertyOnSomeEtaleSmoothDiagram
      B S hS P hP f
      (hasPropertyOnSomeEtaleSmoothDiagram_of_hasRelativeProperty.{u, v, w} B S hS P f hf h)⟩

/-- For a representable 1-morphism, the universal étale-smooth diagram test for unramifiedness
is the relative property. -/
private theorem hasPropertyOnEveryEtaleSmoothDiagram_unramified_iff_relative
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) :
    HasPropertyOnEveryEtaleSmoothDiagram B S hS (Space.unramifiedMorphismProperty B S hS) f ↔
      RelativeProperty B S hS (Space.unramifiedMorphismProperty B S hS) f.hom := by
  have : (Space.unramifiedMorphismProperty B S hS).IsStableUnderBaseChange :=
    Space.isUnramified_isStableUnderBaseChange B S hS
  have : (Space.unramifiedMorphismProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    (Space.isUnramified_isLocalAtTarget_fpqc.{u, u} B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  exact hasPropertyOnEveryEtaleSmoothDiagram_iff_relative.{u, u, w} B S hS
    (Space.unramifiedMorphismProperty B S hS)
    (Space.isUnramified_isEtaleSmoothLocalOnSourceAndTarget B S hS) f hf

/-- **An unramified 1-morphism in the sense of Stacks 0CIT which is representable by algebraic
spaces is relatively unramified**, in the sense of **Stacks 04XB** at
`AlgebraicGeometry.Space.unramifiedMorphismProperty`.

This is the direction of the comparison that was unavailable: it runs through the existential
étale-smooth diagram test, whose diagram
`AlgebraicGeometry.Stack.hasSurjectiveEtaleSmoothDiagram_of_isRepresentableByAlgebraicSpaces`
supplies for a representable 1-morphism. Unramifiedness is étale-smooth local on the
source-and-target by **Stacks 0CG3**. -/
theorem hasRelativeProperty_unramified_of_isUnramified
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (h : IsUnramified B S hS f) :
    RelativeProperty B S hS (Space.unramifiedMorphismProperty B S hS) f.hom := by
  exact (hasPropertyOnEveryEtaleSmoothDiagram_unramified_iff_relative B S hS f hf).1 h.2

/-- **A relatively unramified 1-morphism which is Deligne–Mumford and representable by algebraic
spaces is unramified in the sense of Stacks 0CIT.** The converse of
`AlgebraicGeometry.Stack.hasRelativeProperty_unramified_of_isUnramified`; this direction was
already available, through the existential étale-smooth diagram test. -/
theorem isUnramified_of_hasRelativeProperty_unramified
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hDM : IsDM B S hS f)
    (h : RelativeProperty B S hS (Space.unramifiedMorphismProperty B S hS) f.hom) :
    IsUnramified B S hS f := by
  exact ⟨hDM, (hasPropertyOnEveryEtaleSmoothDiagram_unramified_iff_relative B S hS f hf).2 h⟩

end AlgebraicGeometry.Stack

end
