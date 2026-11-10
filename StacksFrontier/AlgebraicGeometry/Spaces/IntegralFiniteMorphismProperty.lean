module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Fpqc.Integral
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFpqcLocalAtTarget
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Permanence of integrality and finiteness as morphism properties of algebraic spaces

`AlgebraicGeometry.Space.integralMorphismProperty` and
`AlgebraicGeometry.Space.finiteMorphismProperty` package integrality and finiteness of a
morphism of algebraic spaces over `S` (Stacks 03ZP) as properties of morphisms in the category
of algebraic spaces over `S`. This file completes the three permanence instances that a relative
property of Stacks 03YK is introduced under — stability under base change, locality on the
target for the fppf precoverage, and stability under composition — from the statements of
Stacks 03ZS, Stacks 0425, Stacks 0426 and Stacks 03ZR.

## Main results

* `AlgebraicGeometry.Space.integralMorphismProperty_isLocalAtTarget_fppf` and
  `AlgebraicGeometry.Space.integralMorphismProperty_isStableUnderComposition`: Stacks 0425 at
  the fppf precoverage, and Stacks 03ZR, at the packaged spelling of integrality.
* `AlgebraicGeometry.Space.finiteMorphismProperty_isStableUnderBaseChange` and
  `AlgebraicGeometry.Space.finiteMorphismProperty_isStableUnderComposition`: Stacks 03ZS and
  Stacks 03ZR at the packaged spelling of finiteness.

## Implementation notes

The two properties already carry one instance each: integrality is stable under base change by
`AlgebraicGeometry.Space.integralMorphismProperty_isStableUnderBaseChange` and finiteness is
local on the target for the fppf precoverage by
`AlgebraicGeometry.Space.isFinite_isLocalAtTarget_fppf`. The four instances below are the
remaining ones, and each is the corresponding tagged statement read at the packaged spelling: the
fppf locality of integrality from its fpqc locality (Stacks 0425) through
`AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage`, exactly as
`AlgebraicGeometry.Space.isFinite_isLocalAtTarget_fppf` does for finiteness; base change of
finiteness from `AlgebraicGeometry.Space.isFinite_of_isPullback` (Stacks 03ZS) together with
`AlgebraicGeometry.AlgebraicSpaces.isPullback_hom`, which says that a Cartesian square of
algebraic spaces is Cartesian in presheaves; and the two composition instances from
`AlgebraicGeometry.Space.isIntegralHom_comp` and `AlgebraicGeometry.Space.isFinite_comp`
(Stacks 03ZR).

No declaration here carries a `@[stacks]` attribute: each is an already-tagged statement read at
a different spelling of the same property, so a tag here would duplicate the one its general
form carries.

## References

* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 03ZR](https://stacks.math.columbia.edu/tag/03ZR)
* [Stacks Project, Tag 03ZS](https://stacks.math.columbia.edu/tag/03ZS)
* [Stacks Project, Tag 0425](https://stacks.math.columbia.edu/tag/0425)
* [Stacks Project, Tag 0426](https://stacks.math.columbia.edu/tag/0426)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0425** at the fppf precoverage: integrality of morphisms of algebraic spaces over
`S` is local on the target for the fppf topology. This is the form in which Stacks 03YK's
relative properties ask for it, and it follows from the fpqc form because every fppf covering
family of algebraic spaces is an fpqc covering family. -/
@[sga "4 IV 8.5.5" "partial"]
instance integralMorphismProperty_isLocalAtTarget_fppf :
    (integralMorphismProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fppf B S hS) :=
  .of_le (fppfPrecoverage_le_fpqcPrecoverage B S hS)

/-- **Stacks 03ZR at the packaged spelling**: integrality, as a morphism property of algebraic
spaces over `S`, is stable under composition. -/
instance integralMorphismProperty_isStableUnderComposition :
    (integralMorphismProperty B S hS).IsStableUnderComposition where
  comp_mem _ _ hf hg := isIntegralHom_comp B S hS hf hg

/-- **Stacks 03ZS at the packaged spelling**: finiteness, as a morphism property of algebraic
spaces over `S`, is stable under base change. A Cartesian square of algebraic spaces is
Cartesian in presheaves, so this is Stacks 03ZS for a Cartesian square of presheaves. -/
instance finiteMorphismProperty_isStableUnderBaseChange :
    (finiteMorphismProperty B S hS).IsStableUnderBaseChange where
  of_isPullback sq hg := isFinite_of_isPullback B S hS (AlgebraicSpaces.isPullback_hom _ _ _ sq) hg

/-- **Stacks 03ZR at the packaged spelling**: finiteness, as a morphism property of algebraic
spaces over `S`, is stable under composition. -/
instance finiteMorphismProperty_isStableUnderComposition :
    (finiteMorphismProperty B S hS).IsStableUnderComposition where
  comp_mem _ _ hf hg := isFinite_comp B S hS hf hg

end AlgebraicGeometry.Space

end
