module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFpqcLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleFlatUnramifiedCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismComp
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.Substack

/-!
# Restricting a flat, locally finitely presented 1-morphism to an open substack

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` which is flat (**Stacks 06PW**) and
locally of finite presentation (**Stacks 06Q2**, part (1)), and let `W` be an open substack of
`𝒳`. The restriction of `f` to `W` is again flat and locally of finite presentation, so by
**Stacks 0CJ1** it is étale as soon as it is unramified. That last implication is **Stacks 06LU**
— flat plus locally of finite presentation plus unramified gives étale — in the form in which the
proofs of **Stacks 06ME** and **Stacks 06N2** use it, namely for a 1-morphism of algebraic stacks
rather than for a morphism of algebraic spaces.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_of_isOpenImmersion`: an open immersion of
  algebraic stacks over `S` is flat. This is the flat companion of **Stacks 06Q7**
  (`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_of_isOpenImmersion`)
  and is proved the same way.
* `AlgebraicGeometry.Stack.isFlat_fullSubcategoryInclusion_comp` and
  `AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_fullSubcategoryInclusion_comp`: the
  restriction of a flat, resp. locally finitely presented, 1-morphism to an open substack of its
  source is again flat, resp. locally of finite presentation.
* `AlgebraicGeometry.Stack.isEtale_fullSubcategoryInclusion_comp_of_isUnramified`: the
  restriction of a flat, locally finitely presented 1-morphism to an open substack is étale as
  soon as it is unramified.

## Implementation notes

Flatness of an open immersion is not in the library, while local finite presentation of one is
(**Stacks 06Q7**). The two have the same proof: an open immersion is representable by algebraic
spaces and every algebraic space representing a base change of it along a scheme-valued point of
the target has open immersion structural morphism, hence flat structural morphism by
`AlgebraicGeometry.Space.isFlat_of_isEtale` and
`AlgebraicGeometry.Space.isEtale_of_isOpenImmersion`; that is the relative property of
**Stacks 03YK** at flatness, which `AlgebraicGeometry.Stack`
`.hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty` turns into the existential
smooth-diagram test of **Stacks 06FM** that **Stacks 06PW** inlines.

The three hypotheses that bridge carries on flatness of morphisms of algebraic spaces are
`AlgebraicGeometry.Space.isSmoothLocalOnSourceAndTarget_flat` (**Stacks 06FC** at flatness),
`AlgebraicGeometry.Space.isFlat_isStableUnderBaseChange` (**Stacks 03MO**) and locality at the
target for the fppf precoverage, which is `AlgebraicGeometry.Space.isFlat_isLocalAtTarget_fpqc`
transported along `AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage`.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06LU](https://stacks.math.columbia.edu/tag/06LU)
* [Stacks Project, Tag 06PW](https://stacks.math.columbia.edu/tag/06PW)
* [Stacks Project, Tag 06Q7](https://stacks.math.columbia.edu/tag/06Q7)
* [Stacks Project, Tag 0CJ1](https://stacks.math.columbia.edu/tag/0CJ1)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace AlgebraicStacks

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **An open immersion of algebraic stacks over `S` is flat.**

By **Stacks 04YL** the 1-morphism is representable by algebraic spaces and every algebraic space
representing a base change of it along a scheme-valued point of the target has open immersion
structural morphism, hence étale and so flat structural morphism. That is the relative property
of **Stacks 03YK** at flatness of morphisms of algebraic spaces, which **Stacks 06FM** equates
with the existential smooth-diagram test that **Stacks 06PW** inlines.

This is the flat companion of **Stacks 06Q7**,
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_of_isOpenImmersion`. -/
theorem isFlat_of_isOpenImmersion (f : 𝒳 ⟶ 𝒴) (hf : IsOpenImmersion B S hS f) :
    IsFlat B S hS f := by
  let flatP : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun _ _ h => Space.IsFlat B S hS h
  let : (spaceProperty B S hS flatP).IsStableUnderBaseChange :=
    Space.isFlat_isStableUnderBaseChange B S hS
  let : (spaceProperty B S hS flatP).IsLocalAtTarget
      (Space.Topology.fpqc.precoverage.{u, u} B S hS) :=
    Space.isFlat_isLocalAtTarget_fpqc B S hS
  let : (spaceProperty B S hS flatP).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le
      (L := Space.Topology.fpqc.precoverage.{u, u} B S hS)
      (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  exact (isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS f).2
    (Stack.hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS flatP
      𝒴.property f.hom hf.1
      fun U y hy F hF hrep =>
        Space.isFlat_of_isEtale B S hS
          (Space.isEtale_of_isOpenImmersion B S hS (hf.2 U y hy F hF hrep)))

end AlgebraicStacks

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **The restriction of a flat 1-morphism to an open substack of its source is flat.** The
inclusion of an open substack is an open immersion, hence flat, and flatness is stable under
composition (**Stacks 06PX**). -/
theorem isFlat_fullSubcategoryInclusion_comp (f : 𝒳 ⟶ 𝒴) (W : OpenSubstack 𝒳)
    (hf : AlgebraicStacks.IsFlat B S hS f) :
    AlgebraicStacks.IsFlat B S hS
      (fullSubcategoryInclusion 𝒳 W.property W.isAlgebraic ≫ f) :=
  AlgebraicStacks.isFlat_comp B S hS _ f
    (AlgebraicStacks.isFlat_of_isOpenImmersion B S hS _ W.isOpenImmersion) hf

/-- **The restriction of a locally finitely presented 1-morphism to an open substack of its
source is locally of finite presentation.** The inclusion of an open substack is an open
immersion, hence locally of finite presentation by **Stacks 06Q7**, and local finite presentation
is stable under composition (**Stacks 06Q3**). -/
theorem isLocallyOfFinitePresentation_fullSubcategoryInclusion_comp (f : 𝒳 ⟶ 𝒴)
    (W : OpenSubstack 𝒳) (hf : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f) :
    AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
      (fullSubcategoryInclusion 𝒳 W.property W.isAlgebraic ≫ f) :=
  AlgebraicStacks.isLocallyOfFinitePresentation_comp B S hS _ f
    (AlgebraicStacks.isLocallyOfFinitePresentation_of_isOpenImmersion B S hS _
      W.isOpenImmersion) hf

/-- **Stacks 06LU for a 1-morphism of algebraic stacks, restricted to an open substack.** Let
`f : 𝒳 ⟶ 𝒴` be flat and locally of finite presentation and let `W` be an open substack of `𝒳`.
If the restriction of `f` to `W` is unramified (**Stacks 0CIT**) then it is étale
(**Stacks 0CIL**).

The restriction is flat and locally of finite presentation because the inclusion of an open
substack is, and **Stacks 0CJ1** turns flat, locally of finite presentation and unramified into
étale. This is the step the proofs of **Stacks 06ME** and **Stacks 06N2** take at the fibre over
a field-valued point. -/
theorem isEtale_fullSubcategoryInclusion_comp_of_isUnramified (f : 𝒳 ⟶ 𝒴) (W : OpenSubstack 𝒳)
    (hflat : AlgebraicStacks.IsFlat B S hS f)
    (hfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (hunr : IsUnramified B S hS (fullSubcategoryInclusion 𝒳 W.property W.isAlgebraic ≫ f)) :
    IsEtale B S hS (fullSubcategoryInclusion 𝒳 W.property W.isAlgebraic ≫ f) :=
  AlgebraicStacks.isEtale_of_isLocallyOfFinitePresentation_of_isFlat_of_isUnramified B S hS _
    (isLocallyOfFinitePresentation_fullSubcategoryInclusion_comp B S hS f W hfp)
    (isFlat_fullSubcategoryInclusion_comp B S hS f W hflat) hunr

end AlgebraicGeometry.Stack

end
