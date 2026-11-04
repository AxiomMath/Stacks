module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Smoothness as a morphism property of algebraic spaces

`AlgebraicGeometry.Space.IsSmooth` (Stacks 03ZC, part (1)) is a predicate on a morphism of
fppf sheaves. Several results about algebraic stacks instead need smoothness packaged as a
`CategoryTheory.MorphismProperty` on the category `AlgebraicGeometry.AlgebraicSpaces` of
algebraic spaces over `S`, so that the `MorphismProperty` classes — stability under base
change, locality at the target — can be carried as instances. This module names that property
and records the instance that is available.

Stability under base change is Stacks 03ZE, already proved unconditionally as
`AlgebraicGeometry.Space.isSmooth_isStableUnderBaseChange`; stability under composition is
Stacks 03ZD, and is the instance of Stacks 0AML at the smooth property, smoothness of schemes
being étale local on the source and target (Stacks 04R3) and stable under composition. Both
are restated here at the packaged spelling, which is what instance search needs.

Locality at the target for the fpqc precoverage is Stacks 0429 and is *not* proved here.

## Main definitions

* `AlgebraicGeometry.Space.smoothMorphismProperty`: smoothness as a `MorphismProperty` on the
  category of algebraic spaces over `S`.

## Main results

* `AlgebraicGeometry.Space.instIsStableUnderBaseChangeSmoothMorphismProperty`: **Stacks 03ZE**
  at the packaged spelling, as an instance.
* `AlgebraicGeometry.Space.isSmooth_comp`: **Stacks 03ZD**.
* `AlgebraicGeometry.Space.instIsStableUnderCompositionSmoothMorphismProperty`: **Stacks
  03ZD** at the packaged spelling, as an instance.

## References

* [Stacks Project, Tag 03ZC](https://stacks.math.columbia.edu/tag/03ZC)
* [Stacks Project, Tag 03ZD](https://stacks.math.columbia.edu/tag/03ZD)
* [Stacks Project, Tag 03ZE](https://stacks.math.columbia.edu/tag/03ZE)
* [Stacks Project, Tag 0429](https://stacks.math.columbia.edu/tag/0429)
* [Stacks Project, Tag 0AML](https://stacks.math.columbia.edu/tag/0AML)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Smoothness (Stacks 03ZC, part (1)) as a property of morphisms in the category of algebraic
spaces over `S`. -/
abbrev smoothMorphismProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ f => IsSmooth B S hS f.hom

/-- **Stacks 03ZE** at the packaged spelling: smoothness, as a morphism property of algebraic
spaces over `S`, is stable under base change. -/
instance instIsStableUnderBaseChangeSmoothMorphismProperty :
    (smoothMorphismProperty B S hS).IsStableUnderBaseChange :=
  isSmooth_isStableUnderBaseChange B S hS

/-- **Stacks 03ZD.** The composite of two smooth morphisms of algebraic spaces over `S` is
smooth: this is Stacks 0AML applied to the smooth property of morphisms of schemes, which is
étale local on the source and target and stable under composition. -/
@[stacks 03ZD, ega "IV 17.3.3" "more general", ega "IV 6.8.3" "more general"]
theorem isSmooth_comp {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsSmooth B S hS f) (hg : IsSmooth B S hS g) :
    IsSmooth B S hS (f ≫ g) :=
  holdsOnEveryEtaleChart_comp B S hS
    (@AlgebraicGeometry.Smooth.{u} : MorphismProperty Scheme.{u})
    Smooth.isEtaleLocalOnSourceAndTarget hX hY hZ f g hf hg

/-- **Stacks 03ZD** at the packaged spelling: smoothness, as a morphism property of algebraic
spaces over `S`, is stable under composition. -/
@[ega "IV 6.8.3" "more general"]
instance instIsStableUnderCompositionSmoothMorphismProperty :
    (smoothMorphismProperty B S hS).IsStableUnderComposition :=
  holdsOnEveryEtaleChart_isStableUnderComposition B S hS
    (@AlgebraicGeometry.Smooth.{u} : MorphismProperty Scheme.{u})
    Smooth.isEtaleLocalOnSourceAndTarget

end AlgebraicGeometry.Space

end
