module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSource.Fppf
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FinitenessFpqcLocality
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryRelative

/-!
# Finiteness properties of immersions of algebraic stacks (Stacks 06FV, 06Q7)

An immersion of algebraic stacks over `S` is locally of finite type, and an open immersion is
locally of finite presentation.

Both notions of immersion are, by **Stacks 04YL**, the relative property of **Stacks 03YK** at
the corresponding property of morphisms of algebraic spaces: every algebraic space representing
a base change of the 1-morphism along a scheme-valued point of the target has structural morphism
of that kind. The two finiteness notions are, by **Stacks 06FS** and **Stacks 06Q2**, the
universal smooth-diagram test of **Stacks 06FM**. So in both cases the implication is the
corresponding implication for morphisms of algebraic spaces — **Stacks 06ED** and
**Stacks 06CN** — carried from the relative property to the universal test by
`AlgebraicGeometry.Stack.hasPropertyOnEverySmoothDiagram_of_hasRelativeProperty`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_of_isImmersion`:
  **Stacks 06FV**.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_of_isOpenImmersion`:
  **Stacks 06Q7**.

## Implementation notes

The source proves Stacks 06FV by combining Remark **Stacks 06PS** — an implication between
properties of morphisms of algebraic spaces induces the implication between the properties of
1-morphisms of algebraic stacks they define — with Stacks 06ED. That remark is
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_mono`, and it is an implication between
the *existential* smooth-diagram tests, whereas in this library the immersion conditions are
the relative property and local finite type is the *universal* test. The three conditions agree
by Stacks 06FM, which is what the bridge above supplies; the argument is the source's, with the
passage between the conditions made explicit.

Both applications need the three hypotheses that bridge carries on the tested property of
morphisms of algebraic spaces:

* smooth locality on the source-and-target (**Stacks 06FC**), which for these two properties is
  `AlgebraicGeometry.Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType` and
  `AlgebraicGeometry.Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation`;
* stability under base change, **Stacks 03XH** and **Stacks 03XR**, which are theorems rather
  than instances in this library and so are supplied by a local `let`;
* locality at the target for the fppf precoverage, which is the fpqc one transported along
  `AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage` by
  `CategoryTheory.MorphismProperty.IsLocalAtTarget.of_le`, also supplied by a local `let`: of
  these properties only the smooth one has its fppf locality as a global instance.

Being *of* finite type and *of* finite presentation — part (3) of Stacks 06FS and part (2) of
Stacks 06Q2 — also require quasi-compactness, and an immersion need not be quasi-compact, so the
statements here concern the local notions only.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 06CN](https://stacks.math.columbia.edu/tag/06CN)
* [Stacks Project, Tag 06ED](https://stacks.math.columbia.edu/tag/06ED)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FS](https://stacks.math.columbia.edu/tag/06FS)
* [Stacks Project, Tag 06FV](https://stacks.math.columbia.edu/tag/06FV)
* [Stacks Project, Tag 06PS](https://stacks.math.columbia.edu/tag/06PS)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
* [Stacks Project, Tag 06Q7](https://stacks.math.columbia.edu/tag/06Q7)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 06FV.** An immersion of algebraic stacks over `S` is locally of finite type.

By Stacks 04YL the 1-morphism is representable by algebraic spaces and every algebraic space
representing a base change of it along a scheme-valued point of the target has immersion
structural morphism, hence by Stacks 06ED has structural morphism locally of finite type. That
is the relative property of Stacks 03YK at local finite type of morphisms of algebraic spaces,
which Stacks 06FM equates with the universal smooth-diagram test defining local finite type of
the 1-morphism. -/
@[stacks 06FV]
theorem isLocallyOfFiniteType_of_isImmersion
    (f : 𝒳 ⟶ 𝒴) (hf : IsImmersion B S hS f) :
    IsLocallyOfFiniteType B S hS f := by
  let : MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (g : F ⟶ G) =>
        Space.IsLocallyOfFiniteType B S hS g.hom) :=
    Space.isLocallyOfFiniteType_isStableUnderBaseChange B S hS
  let : MorphismProperty.IsLocalAtTarget
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (g : F ⟶ G) =>
        Space.IsLocallyOfFiniteType B S hS g.hom)
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  exact Stack.hasPropertyOnEverySmoothDiagram_of_hasRelativeProperty.{u, u, w} B S hS
    (fun _ _ g => Space.IsLocallyOfFiniteType B S hS g)
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
    𝒳.property 𝒴.property f.hom hf.1
    fun U y hy F hF hrep =>
      Space.isLocallyOfFiniteType_of_isImmersion B S hS _ (hf.2 U y hy F hF hrep)

/-- **Stacks 06Q7.** An open immersion of algebraic stacks over `S` is locally of finite
presentation.

By Stacks 04YL the 1-morphism is representable by algebraic spaces and every algebraic space
representing a base change of it along a scheme-valued point of the target has open immersion
structural morphism, hence by Stacks 06CN has structural morphism locally of finite
presentation. That is the relative property of Stacks 03YK at local finite presentation of
morphisms of algebraic spaces, which Stacks 06FM equates with the universal smooth-diagram test
defining local finite presentation of the 1-morphism. -/
@[stacks 06Q7]
theorem isLocallyOfFinitePresentation_of_isOpenImmersion
    (f : 𝒳 ⟶ 𝒴) (hf : IsOpenImmersion B S hS f) :
    IsLocallyOfFinitePresentation B S hS f := by
  let : MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (g : F ⟶ G) =>
        Space.IsLocallyOfFinitePresentation B S hS g.hom) :=
    Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  let : MorphismProperty.IsLocalAtTarget
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (g : F ⟶ G) =>
        Space.IsLocallyOfFinitePresentation B S hS g.hom)
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  exact Stack.hasPropertyOnEverySmoothDiagram_of_hasRelativeProperty.{u, u, w} B S hS
    (fun _ _ g => Space.IsLocallyOfFinitePresentation B S hS g)
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
    𝒳.property 𝒴.property f.hom hf.1
    fun U y hy F hF hrep =>
      Space.isLocallyOfFinitePresentation_of_isOpenImmersion B S hS (hf.2 U y hy F hF hrep)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
