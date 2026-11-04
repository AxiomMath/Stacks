module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.Immersion
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismPropertyTopology.FppfLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.QuasiCompactLocal

/-!
# The immersion entries of the list of Tag 02WH

Tag 02WH lists the properties of morphisms of schemes which, being stable under base change,
are moreover *fpqc local on the base*, hence a fortiori *fppf local on the base*. This file
records its first entry, the one about immersions, which splits into three cases.

## Main results

* `Stacks.Descent.isClosedImmersion_isLocalAtTarget_fppf`: being a closed immersion is fppf
  local on the base.
* `Stacks.Descent.isOpenImmersion_isLocalAtTarget_fppf`: being an open immersion is fppf local
  on the base.
* `Stacks.Descent.isImmersion_inf_quasiCompact_isStableUnderBaseChange` and
  `Stacks.Descent.isImmersion_inf_quasiCompact_isLocalAtTarget_fppf`: being a quasi-compact
  immersion is stable under base change and fppf local on the base.

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

The last sentence of Tag 02WH is a warning rather than an entry: being an *immersion* is not
asserted to be fpqc local on the base, only fppf local on the base, which is Tag 02YM. That is
why the entry of the list is confined to the three cases above. The warning is stated, and
carries the tag, as `Stacks.Descent.isImmersion_isStableUnderBaseChange_and_isLocalAtTarget_fppf`
in `Entries.lean`, whose second conjunct is fppf locality and which has no fpqc conjunct at all;
the fppf locality itself is `Stacks.Descent.isImmersion_isLocalAtTarget_fppf`, which carries Tag
02YM where it is proved.

## References

* [Stacks Project, Tag 02WH](https://stacks.math.columbia.edu/tag/02WH)
-/

@[expose] public section

open CategoryTheory MorphismProperty AlgebraicGeometry

universe u

namespace Stacks.Descent

/-! ### Closed immersions -/

/-- **Stacks 02WH**, entry (1)(a). Being a closed immersion is fppf local on the base. -/
@[sga "4 IV 8.5.5" "special case"]
public instance isClosedImmersion_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget (@IsClosedImmersion : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
  isLocalAtTarget_fppfPrecoverage _

/-! ### Open immersions -/

/-- **Stacks 02WH**, entry (1)(b). Being an open immersion is fppf local on the base. -/
@[sga "4 IV 8.5.5" "special case"]
public instance isOpenImmersion_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget (@IsOpenImmersion : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
  isLocalAtTarget_fppfPrecoverage _

/-! ### Quasi-compact immersions -/

/-- Being a quasi-compact immersion is stable under arbitrary base change, both halves of the
conjunction being so. -/
public instance isImmersion_inf_quasiCompact_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (@IsImmersion ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) := .inf

/-- **Stacks 02WH**, entry (1)(c). Being a quasi-compact immersion is fppf local on the
base. -/
@[sga "4 IV 8.5.5" "special case"]
public instance isImmersion_inf_quasiCompact_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget
      (@IsImmersion ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
  isLocalAtTarget_fppfPrecoverage _

/-! ### Immersions in general: the caveat of the last sentence -/

end Stacks.Descent

end
