module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaProductsToDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeProperty

/-!
# Relative properties of scheme-valued points (Stacks, Section 03YJ)

Section 03YJ of the chapter on algebraic stacks introduces the relative properties of
**Stacks 03YK** and closes with the following running text, after Lemma 045G:

> In the situation of the lemma, for any 1-morphism `x : (Sch/U)_fppf → 𝒳` as in the lemma, it
> makes sense to say that `x` has property `𝒫`, for any property as in Definition 03YK. In
> particular this holds for `𝒫 =` "surjective", `𝒫 =` "smooth", and `𝒫 =` "étale", see Descent
> on Spaces, Lemmas 041Q, 0429, and 042B.

This module formalizes that text in three pieces.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_schemePoint`: when the diagonal of
  `𝒳` is representable by algebraic spaces, every 1-morphism `x : (Sch/U)_fppf → 𝒳` from the
  category represented by a scheme is representable by algebraic spaces. This is what makes
  "`x` has `𝒫`" meaningful.
* `AlgebraicGeometry.Stack.SchemePointHasRelativeProperty`: the proposition "`x` has `𝒫`", for
  `𝒳` with diagonal representable by algebraic spaces and `𝒫` as in Definition 03YK.
* `AlgebraicGeometry.Stack.surjective_smooth_etale_relativePropertyHypotheses`: surjectivity,
  smoothness and étaleness of morphisms of algebraic spaces each satisfy both hypotheses of
  Definition 03YK, that is, each is stable under base change and local on the base for the fppf
  topology.

## Implementation notes

"In the situation of the lemma" means that `𝒳` satisfies the equivalent conditions of Lemma
045G. The hypothesis used here is condition (1), that the diagonal is representable by algebraic
spaces, which is the form in which the definition of an algebraic stack states it. Condition (3)
follows by composing the two equivalences
`AlgebraicGeometry.Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf` (parts (1)
and (2)) and `AlgebraicGeometry.Stack.isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes`
(parts (2) and (3)).

The six facts behind the last result are all available as instances: base-change stability is
**Stacks 03MH** for surjectivity
(`AlgebraicGeometry.Space.surjectiveMorphismProperty_isStableUnderBaseChange`), **Stacks 03ZE**
for smoothness and **Stacks 03FU** for étaleness; locality on the base for the fppf topology is
the fppf reading of **Stacks 041Q**, **Stacks 0429** and **Stacks 042B**. The statement collects
them, which is the claim of the running text.

## References

* [Stacks Project, Tag 03YJ](https://stacks.math.columbia.edu/tag/03YJ)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 041Q](https://stacks.math.columbia.edu/tag/041Q)
* [Stacks Project, Tag 0429](https://stacks.math.columbia.edu/tag/0429)
* [Stacks Project, Tag 042B](https://stacks.math.columbia.edu/tag/042B)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks, Section 03YJ.** If the diagonal of a category fibred in groupoids `𝒳` over the
big fppf site of `S` is representable by algebraic spaces, then every 1-morphism
`x : (Sch/U)_fppf → 𝒳` from the category represented by a scheme `U` over `S` is representable
by algebraic spaces. This is condition (3) of Stacks 045G obtained from condition (1). -/
@[stacks 03YJ "in the situation of Lemma 045G, every 1-morphism x : (Sch/U)_fppf -> X is \
representable by algebraic spaces, so that saying x has P makes sense"]
theorem isRepresentableByAlgebraicSpaces_schemePoint
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : HasRepresentableDiagonal B S hS 𝒳) {U : BigFppfOver B S hS}
    (x : schemeFibredCategory B S hS U ⟶ 𝒳) :
    IsRepresentableByAlgebraicSpaces B S hS x.hom :=
  (isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS 𝒳).mp
    ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳).mp h𝒳) U x.hom

/-- **Stacks, Section 03YJ.** Let `𝒳` be a category fibred in groupoids over the big fppf site
of `S` whose diagonal is representable by algebraic spaces, and let `𝒫` be a property of
morphisms of algebraic spaces as in Definition 03YK. A 1-morphism `x : (Sch/U)_fppf → 𝒳` from
the category represented by a scheme `U` over `S` *has `𝒫`* when it has `𝒫` in the sense of
Stacks 03YK; it is representable by algebraic spaces by
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_schemePoint`. -/
@[stacks 03YJ "for X as in Lemma 045G and P as in Definition 03YK, the property that a \
1-morphism x : (Sch/U)_fppf -> X has P"]
abbrev SchemePointHasRelativeProperty
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : HasRepresentableDiagonal B S hS 𝒳) {U : BigFppfOver B S hS}
    (x : schemeFibredCategory B S hS U ⟶ 𝒳) : Prop :=
  HasRelativeProperty B S hS P x (isRepresentableByAlgebraicSpaces_schemePoint B S hS 𝒳 h𝒳 x)

/-- **Stacks, Section 03YJ.** Surjectivity, smoothness and étaleness of morphisms of algebraic
spaces over `S` are each properties as in Definition 03YK: each is stable under base change and
local on the base for the fppf topology (Stacks 041Q, 0429 and 042B). -/
@[stacks 03YJ "surjective, smooth and etale are properties as in Definition 03YK"]
theorem surjective_smooth_etale_relativePropertyHypotheses :
    ((Space.surjectiveMorphismProperty B S hS).IsStableUnderBaseChange ∧
        (Space.surjectiveMorphismProperty B S hS).IsLocalAtTarget
          (Space.Topology.fppf.precoverage.{u, v} B S hS)) ∧
      ((Space.smoothMorphismProperty B S hS).IsStableUnderBaseChange ∧
        (Space.smoothMorphismProperty B S hS).IsLocalAtTarget
          (Space.Topology.fppf.precoverage.{u, v} B S hS)) ∧
      ((Space.etaleMorphisms B S hS).IsStableUnderBaseChange ∧
        (Space.etaleMorphisms B S hS).IsLocalAtTarget
          (Space.Topology.fppf.precoverage.{u, v} B S hS)) :=
  ⟨⟨inferInstance, inferInstance⟩, ⟨inferInstance, inferInstance⟩,
    ⟨inferInstance, inferInstance⟩⟩

end AlgebraicGeometry.Stack

end
