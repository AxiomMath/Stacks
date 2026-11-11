module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSourceAndTarget.EtaleSmoothExamples
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismBaseChangeStable
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismComp

/-!
# Permanence of unramifiedness for 1-morphisms of algebraic stacks (Stacks 0CIU, 0CIV)

**Stacks 0CIU** asserts that a composite of unramified 1-morphisms of algebraic stacks over `S`
is unramified, and **Stacks 0CIV** that an unramified 1-morphism stays unramified after a base
change. Unramifiedness of a 1-morphism of algebraic stacks is
`AlgebraicGeometry.Stack.IsUnramified` (**Stacks 0CIT**): the Deligne–Mumford condition of
**Stacks 04YW** together with the universal étale-smooth diagram test of **Stacks 0CIF** taken at
`AlgebraicGeometry.Space.IsUnramified`, unramifiedness of morphisms of algebraic spaces
(**Stacks 03ZH**, part (1)).

Both results are the source's: they are the general transfer theorems **Stacks 0CIH** and
**Stacks 0CII** — permanence of the property of Deligne–Mumford 1-morphisms that **Stacks 0CIG**
induces from an étale-smooth local property of morphisms of algebraic spaces — read at
unramifiedness, whose étale-smooth locality on the source-and-target is the unramified entry of
**Stacks 0CG3** and whose stability under composition and under base change are **Stacks 03ZI**
and **Stacks 03ZJ**.

## Main results

* `AlgebraicGeometry.Stack.isUnramified_comp`: composition of unramified 1-morphisms, over the
  arguments `hT` and `hForward`; **Stacks 0CIU** with both discharged is
  `AlgebraicGeometry.Stack.AlgebraicStacks.isUnramified_comp`, in
  `StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedMorphismComp`.
* `AlgebraicGeometry.Stack.isUnramified_baseChange`: base change of an unramified 1-morphism
  along the canonical 2-fibre product square, the shape **Stacks 0CIV** takes in Stacks 0CII.

## Implementation notes

`AlgebraicGeometry.Stack.IsUnramified` is, as a term, the conjunction
`AlgebraicGeometry.Stack.HasEtaleSmoothLocalProperty` forms at
`AlgebraicGeometry.Space.unramifiedMorphismProperty`, so no translation between the two notions
is needed and each theorem below is a direct instance of the corresponding transfer theorem.
That property is the packaged form of Stacks 03ZH, part (1), in
`StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartTargetDescent`, which this file imports; the two
statements, the two étale-smooth locality hypotheses and the two permanence inputs all refer to
that one term.

Both transfer theorems take the implication (1) ⇒ (2) of **Stacks 06N3** as an argument
`hForward : AlgebraicGeometry.Stack.ExistsEtalePresentationOfIsAbsolutelyDM`, together with the
containment `hT` of the terminal scheme it is stated over; it enters only through
**Stacks 0CIA**, which supplies the surjective étale presentations of the 2-fibre products the
source's arguments choose. The theorems below keep that argument. The library proves it, as
`AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM` in
`StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationExistence`, so each theorem below
holds outright once that term is supplied.

`AlgebraicGeometry.Stack.isUnramified_baseChange` is stated for the canonical 2-fibre product
square `AlgebraicGeometry.Stack.AlgebraicStacks.twoFibreProductSquare`, which is the shape
Stacks 0CII is stated at; its second projection is the base change of `f` along `g`. Stacks 0CIV
itself, for an arbitrary 2-fibre product square and with no further argument, is
`AlgebraicGeometry.Stack.isUnramified_baseChange_of_isUnramifiedOnEveryEtaleDiagram` and
`AlgebraicGeometry.Stack.isUnramified_snd_of_isTwoFibreProduct`, in
`StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedBaseChange`.

Inside `AlgebraicGeometry.Stack` the bare `IsUnramified` is the stack notion of Stacks 0CIT, so
the algebraic-space notion of Stacks 03ZH is written out qualified.

## References

* [Stacks Project, Tag 03ZH](https://stacks.math.columbia.edu/tag/03ZH)
* [Stacks Project, Tag 03ZI](https://stacks.math.columbia.edu/tag/03ZI)
* [Stacks Project, Tag 03ZJ](https://stacks.math.columbia.edu/tag/03ZJ)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 0CFZ](https://stacks.math.columbia.edu/tag/0CFZ)
* [Stacks Project, Tag 0CG3](https://stacks.math.columbia.edu/tag/0CG3)
* [Stacks Project, Tag 0CIA](https://stacks.math.columbia.edu/tag/0CIA)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
* [Stacks Project, Tag 0CIG](https://stacks.math.columbia.edu/tag/0CIG)
* [Stacks Project, Tag 0CIH](https://stacks.math.columbia.edu/tag/0CIH)
* [Stacks Project, Tag 0CII](https://stacks.math.columbia.edu/tag/0CII)
* [Stacks Project, Tag 0CIT](https://stacks.math.columbia.edu/tag/0CIT)
* [Stacks Project, Tag 0CIU](https://stacks.math.columbia.edu/tag/0CIU)
* [Stacks Project, Tag 0CIV](https://stacks.math.columbia.edu/tag/0CIV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A composite of unramified 1-morphisms of algebraic stacks over `S` is unramified, given the
containment `hT` of the terminal scheme in the site and the implication (1) ⇒ (2) of
**Stacks 06N3** as `hForward`. Both are discharged in
`AlgebraicGeometry.Stack.AlgebraicStacks.isUnramified_comp` (**Stacks 0CIU**), by
`AlgebraicGeometry.BigFppfSite.contains_terminal` and
`AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM`.

This is **Stacks 0CIH** at unramifiedness of morphisms of algebraic spaces: that property is
étale-smooth local on the source-and-target by the unramified entry of **Stacks 0CG3** and stable
under composition by **Stacks 03ZI**, and unramifiedness of a 1-morphism of algebraic stacks is
exactly the property of Deligne–Mumford 1-morphisms that **Stacks 0CIG** induces from it. -/
theorem isUnramified_comp
    (hT : B.Contains (⊤_ Scheme.{u}))
    (hForward : ExistsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS hT)
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : IsUnramified B S hS f) (hg : IsUnramified B S hS g) :
    IsUnramified B S hS (f ≫ g) :=
  hasEtaleSmoothLocalProperty_comp.{u, w} B S hS (Space.unramifiedMorphismProperty B S hS)
    (Space.isUnramified_isEtaleSmoothLocalOnSourceAndTarget B S hS)
    (fun p q hp hq => (Space.isUnramified_isStableUnderComposition B S hS).comp_mem p q hp hq)
    hT hForward f g hf hg

/-- The base change of an unramified 1-morphism of algebraic stacks over `S` along an arbitrary
1-morphism is unramified: for `f : 𝒳 ⟶ 𝒴` unramified and `g : 𝒵 ⟶ 𝒴` arbitrary, the second
projection of the canonical 2-fibre product square of `(f, g)` — the base change of `f` over
`𝒵` — is unramified.

This is **Stacks 0CII** at unramifiedness of morphisms of algebraic spaces: that property is
étale-smooth local on the source-and-target by the unramified entry of **Stacks 0CG3** and stable
under base change by **Stacks 03ZJ**, and unramifiedness of a 1-morphism of algebraic stacks is
exactly the property of Deligne–Mumford 1-morphisms that **Stacks 0CIG** induces from it. The
argument `hForward` is the implication (1) ⇒ (2) of **Stacks 06N3**, which Stacks 0CII takes as
an argument and the library proves as
`AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM`.

**Stacks 0CIV** itself, for an arbitrary 2-fibre product square, is
`AlgebraicGeometry.Stack.isUnramified_baseChange_of_isUnramifiedOnEveryEtaleDiagram`. -/
theorem isUnramified_baseChange
    (hT : B.Contains (⊤_ Scheme.{u}))
    (_hForward : ExistsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS hT)
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (hf : IsUnramified B S hS f) :
    IsUnramified B S hS (AlgebraicStacks.twoFibreProductSquare B S hS f g).snd :=
  letI : (Space.unramifiedMorphismProperty B S hS).IsStableUnderBaseChange :=
    Space.isUnramified_isStableUnderBaseChange B S hS
  hasEtaleSmoothLocalProperty_baseChange.{u, w} B S hS (Space.unramifiedMorphismProperty B S hS)
    (Space.isUnramified_isEtaleSmoothLocalOnSourceAndTarget B S hS) f g hf

end AlgebraicGeometry.Stack

end
