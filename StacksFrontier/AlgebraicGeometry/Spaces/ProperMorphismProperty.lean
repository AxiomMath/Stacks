module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Fpqc.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartTargetDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FinitenessFpqcLocality

/-!
# Properness as a morphism property of algebraic spaces

`AlgebraicGeometry.Space.IsProper` (**Stacks 03ZM**) is a predicate on a morphism of fppf
sheaves. The relative properties of **Stacks 03YK** and their permanence results — Stacks 045B
for composition, Stacks 045C for base change — are stated instead for a
`CategoryTheory.MorphismProperty` on the category `AlgebraicGeometry.AlgebraicSpaces` of
algebraic spaces over `S`, so that stability and locality are carried as instances. This module
names that property, records its two stability instances, and proves the descent statement that
the composition result consumes.

The descent statement is **not** locality at the target for the fpqc precoverage, which for
properness is Stacks 0422 and is not available: its separatedness half is Stacks 0421, whose
input Stacks 0420 rests on Stacks 041Z. What Stacks 045B
actually uses is strictly weaker: descent along *one surjective étale scheme chart* of the
target. For each of the three conjuncts of properness that is available unconditionally —
separatedness by `AlgebraicGeometry.Space.isSeparated_of_etaleChart`, which is étale descent of
closed immersions and needs no fpqc statement at all, and being of finite type and universally
closed by their fpqc locality, Stacks 041U and Stacks 041O, transported to the fppf precoverage.
So the chart descent holds with no hypothesis, and properness is spelled out here rather than
assembled at each use site.

## Main definitions

* `AlgebraicGeometry.Space.properProperty`: properness as a `MorphismProperty` on the
  category of algebraic spaces over `S`.

## Main results

* `AlgebraicGeometry.Space.properMorphismProperty_isStableUnderBaseChange`: **Stacks 04WP** at
  the packaged spelling.
* `AlgebraicGeometry.Space.properMorphismProperty_of_pullbackSnd_atlas`: properness may be
  tested on the base change of a morphism to a surjective étale scheme chart of its target.
  This is the descent hypothesis that
  `AlgebraicGeometry.Stack.prop_comp_of_atlasDescent` consumes, at properness.

## Implementation notes

The three conjuncts are discharged in the two different ways the library makes available, and
the passage between them is
`AlgebraicGeometry.Space.prop_pullbackSnd_homMk_iff`. Being of finite type and universal
closedness are tested through `AlgebraicGeometry.Space.prop_iff_pullbackSnd_atlas`, which speaks
about the chosen pullback in the category of algebraic spaces and wants locality at the *fppf*
precoverage; it is supplied from the fpqc instance by
`CategoryTheory.MorphismProperty.IsLocalAtTarget.of_le` at
`AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage`, which is the explicit transport
the implementation notes of `StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison` ask for
rather than a global instance. Separatedness has no locality instance at any precoverage, and is
instead tested through `AlgebraicGeometry.Space.isSeparated_of_etaleChart`, which speaks about
the presheaf-level pullback; `prop_pullbackSnd_homMk_iff` at properness converts the hypothesis
once and all three conjuncts are then read off it.

## References

* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 041O](https://stacks.math.columbia.edu/tag/041O)
* [Stacks Project, Tag 041U](https://stacks.math.columbia.edu/tag/041U)
* [Stacks Project, Tag 0422](https://stacks.math.columbia.edu/tag/0422)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 04WP](https://stacks.math.columbia.edu/tag/04WP)
* [Stacks Project, Tag 04XY](https://stacks.math.columbia.edu/tag/04XY)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 04WP** at the packaged spelling: properness, as a morphism property of algebraic
spaces over `S`, is stable under base change. -/
instance properMorphismProperty_isStableUnderBaseChange :
    (properProperty B S hS).IsStableUnderBaseChange :=
  isProper_isStableUnderBaseChange B S hS

/-- **Properness of morphisms of algebraic spaces over `S` may be tested on the base change to a
surjective étale scheme chart of the target.** This is the descent hypothesis that
`AlgebraicGeometry.Stack.prop_comp_of_atlasDescent` consumes, at properness.

Properness is separatedness together with being of finite type and universally closed
(Stacks 03ZM). Separatedness descends along a surjective étale scheme chart by
`AlgebraicGeometry.Space.isSeparated_of_etaleChart`; being of finite type and being universally
closed are local on the base for the fpqc topology — Stacks 041U and Stacks 041O — hence for the
fppf topology, so they descend by
`AlgebraicGeometry.Space.prop_iff_pullbackSnd_atlas`. In particular no fpqc locality statement
for properness itself, i.e. no Stacks 0422 and no Stacks 0APL, is needed. -/
theorem properMorphismProperty_of_pullbackSnd_atlas {X Y : AlgebraicSpaces B S hS} (k : X ⟶ Y)
    {T : BigFppfOver B S hS} {a : yoneda.obj T ⟶ Y.obj}
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (h : properProperty B S hS (Limits.pullback.snd k (ObjectProperty.homMk a :
      (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶ Y))) :
    properProperty B S hS k := by
  have key (P : MorphismProperty (AlgebraicSpaces B S hS))
      [P.IsLocalAtTarget (Topology.fpqc.precoverage.{u, u} B S hS)]
      (hP : P (Limits.pullback.snd k (ObjectProperty.homMk a :
        (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶ Y))) :
      P k := by
    have : P.IsLocalAtTarget (Topology.fppf.precoverage.{u, u} B S hS) :=
      .of_le (fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
    exact (prop_iff_pullbackSnd_atlas.{u, u} B S hS P k hsurj hetale).2 hP
  have hpre := (prop_pullbackSnd_homMk_iff B S hS (properProperty B S hS) k a).1 h
  exact ⟨isSeparated_of_etaleChart B S hS X.property hsurj hetale hpre.1,
    key (fun ⦃X' Y' : AlgebraicSpaces B S hS⦄ (f : X' ⟶ Y') => IsFiniteType B S hS f.hom) h.2.1,
    key (universallyClosedProperty B S hS) h.2.2⟩

end AlgebraicGeometry.Space

end
