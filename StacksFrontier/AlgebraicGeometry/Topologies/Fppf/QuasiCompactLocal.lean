module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget

/-!
# Quasi-compact morphisms are fppf local on the base

A property `P` of morphisms of schemes is *fppf local on the base* if, for every fppf covering
`{Yᵢ → Y}` and every `f : X ⟶ Y`, the morphism `f` has `P` if and only if each base change
`Yᵢ ×_Y X ⟶ Yᵢ` has `P`. In Mathlib this is `CategoryTheory.MorphismProperty.IsLocalAtTarget P
AlgebraicGeometry.Scheme.fppfPrecoverage`.

This file records that quasi-compactness of a morphism of schemes has this property, which is the
quasi-compact entry of the list of Tag 02WH.

## Main results

* `Stacks.Descent.isLocalAtTarget_fppfPrecoverage`: a property of morphisms of schemes which is
  fpqc local on the base is fppf local on the base.
* `Stacks.Descent.quasiCompact_isLocalAtTarget_fppf`: quasi-compactness of a morphism of schemes
  is fppf local on the base.

## Implementation notes

Tag 02WH asserts fpqc locality on the base for the properties it lists, and fppf locality "a
fortiori". That implication is exactly the monotonicity of
`CategoryTheory.MorphismProperty.IsLocalAtTarget` in its precoverage argument
(`CategoryTheory.MorphismProperty.IsLocalAtTarget.of_le`) applied to
`AlgebraicGeometry.Scheme.fppfPrecoverage_le_fpqcPrecoverage`: every fppf covering family is an
fpqc covering family, so a criterion tested against all fpqc coverings is in particular tested
against all fppf ones. The general step is isolated as
`Stacks.Descent.isLocalAtTarget_fppfPrecoverage` so that the remaining entries of the list of Tag
02WH can reuse it.

The fpqc locality of quasi-compactness itself is
`Stacks.Descent.quasiCompact_isLocalAtTarget_fpqc`, proved in
`StacksFrontier/AlgebraicGeometry/Descent/FpqcLocalAtTarget.lean` from the fpqc case of Tag 02KP.

## References

* [Stacks Project, Tag 02WH](https://stacks.math.columbia.edu/tag/02WH)
* [Stacks Project, Tag 02KQ](https://stacks.math.columbia.edu/tag/02KQ)
-/

@[expose] public section

open CategoryTheory MorphismProperty AlgebraicGeometry

universe u

namespace Stacks.Descent

/-- A property of morphisms of schemes which is local on the base for the fpqc precoverage is a
fortiori local on the base for the fppf precoverage, every fppf covering family being an fpqc
covering family. -/
public theorem isLocalAtTarget_fppfPrecoverage (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtTarget Scheme.fpqcPrecoverage] :
    P.IsLocalAtTarget Scheme.fppfPrecoverage :=
  .of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage

/-- **Stacks 02WH.** Quasi-compactness of a morphism of schemes is fppf local on the base. -/
@[stacks 02WH "quasi_compact"]
public instance quasiCompact_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget (@QuasiCompact : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
  isLocalAtTarget_fppfPrecoverage _

end Stacks.Descent

end
