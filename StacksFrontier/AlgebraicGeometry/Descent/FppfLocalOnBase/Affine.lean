module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcAffine
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasiAffine
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.Integral
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.QuasiCompactLocal

/-!
# The affine entries of the list of Tag 02WH

Tag 02WH lists the properties of morphisms of schemes which, being stable under base change,
are moreover *fpqc local on the base*, hence a fortiori *fppf local on the base*. This file
records the entries of that list which say that a morphism is affine over its target: being
affine, being quasi-affine, being finite, and being integral.

## Main results

* `Stacks.Descent.isAffineHom_isLocalAtTarget_fppf`: being affine is fppf local on the base.
* `Stacks.Descent.isQuasiAffineHom_isLocalAtTarget_fppf`: being quasi-affine is fppf local on
  the base.
* `Stacks.Descent.isFinite_isLocalAtTarget_fppf`: being finite is fppf local on the base.
* `Stacks.Descent.isIntegralHom_isLocalAtTarget_fppf`: being integral is fppf local on the
  base.

## Implementation notes

Each entry of the list of Tag 02WH is stated, and carries the tag, as a single conjunction in
`StacksFrontier/AlgebraicGeometry/Descent/FppfLocalOnBase/Entries.lean`: the property is stable
under arbitrary base change, it is local on the base for the fpqc precoverage, **and** it is
local on the base for the fppf precoverage. This file supplies the "a fortiori" half of the
remark, that the property is local on the base for the fppf precoverage, obtained from the fpqc
half by `Stacks.Descent.isLocalAtTarget_fppfPrecoverage`. These instances deliberately do not
carry the tag themselves: one record per entry is what makes the tag's coverage readable, and
the conjunction that does carry it asserts this fppf locality itself, so none of the remark's
content rests on an untagged declaration.

The entry "finite or integral" of the list cites only Descent, Lemma 02LA, which is about
finite morphisms; the integral half of the entry is Descent, Lemma 02L9, recorded as
`AlgebraicGeometry.isIntegralHom_isLocalAtTarget_fpqc`. Both halves are stated in full in
`Entries.lean`, one conjunction each, so that neither reading of the entry is left implicit.

## References

* [Stacks Project, Tag 02WH](https://stacks.math.columbia.edu/tag/02WH)
-/

@[expose] public section

open CategoryTheory MorphismProperty AlgebraicGeometry

universe u

namespace Stacks.Descent

/-! ### Affine morphisms -/

/-- **Stacks 02WH**, entry (8). Being affine is fppf local on the base. -/
public instance isAffineHom_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget (@IsAffineHom : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
  isLocalAtTarget_fppfPrecoverage _

/-! ### Quasi-affine morphisms -/

/-- **Stacks 02WH**, entry (9). Being quasi-affine is fppf local on the base. -/
public instance isQuasiAffineHom_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget (@IsQuasiAffineHom : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
  isLocalAtTarget_fppfPrecoverage _

/-! ### Finite morphisms -/

/-- **Stacks 02WH**, entry (21), finite case. Being finite is fppf local on the base. -/
public instance isFinite_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
  isLocalAtTarget_fppfPrecoverage _

/-! ### Integral morphisms -/

/-- **Stacks 02WH**, entry (21), integral case. Being integral is fppf local on the base. -/
public instance isIntegralHom_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget (@IsIntegralHom : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
  isLocalAtTarget_fppfPrecoverage _

end Stacks.Descent

end
