module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.Syntomic
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.Unramified
public import StacksFrontier.AlgebraicGeometry.Descent.SmoothFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.QuasiCompactLocal

/-!
# The smoothness entries of the list of Tag 02WH

Tag 02WH lists the properties of morphisms of schemes which, being stable under base change,
are moreover *fpqc local on the base*, hence a fortiori *fppf local on the base*. This file
records the entries of that list which are conditions on the fibres and the sheaf of
differentials: being flat, being syntomic, being smooth, and being unramified respectively
G-unramified.

## Main results

* `Stacks.Descent.flat_isLocalAtTarget_fppf`: being flat is fppf local on the base.
* `Stacks.Descent.syntomic_isLocalAtTarget_fppf`: being syntomic is fppf local on the base.
* `Stacks.Descent.smooth_isLocalAtTarget_fppf`: being smooth is fppf local on the base.
* `Stacks.Descent.unramified_isLocalAtTarget_fppf` and
  `Stacks.Descent.gUnramified_isLocalAtTarget_fppf`: being unramified, respectively
  G-unramified, is fppf local on the base.

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

The étale entry of the list is `AlgebraicGeometry.etale_isLocalAtTarget_fppf`, recorded in
`StacksFrontier/AlgebraicGeometry/Descent/EtaleFpqcLocalAtTarget.lean` beside the fpqc half it
comes from.

## References

* [Stacks Project, Tag 02WH](https://stacks.math.columbia.edu/tag/02WH)
-/

@[expose] public section

open CategoryTheory MorphismProperty AlgebraicGeometry

universe u

namespace Stacks.Descent

/-! ### Flat morphisms -/

/-- **Stacks 02WH**, entry (15). Being flat is fppf local on the base. -/
@[sga "4 IV 8.5.5" "special case"]
public instance flat_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget (@Flat : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
  isLocalAtTarget_fppfPrecoverage _

/-! ### Syntomic morphisms -/

/-- **Stacks 02WH**, entry (16). Being syntomic is fppf local on the base. -/
public instance syntomic_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget (@Syntomic : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
  isLocalAtTarget_fppfPrecoverage _

/-! ### Smooth morphisms -/

/-- **Stacks 02WH**, entry (17). Being smooth is fppf local on the base. -/
public instance smooth_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget (@Smooth : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
  isLocalAtTarget_fppfPrecoverage _

/-! ### Unramified and G-unramified morphisms -/

/-- **Stacks 02WH**, entry (18), unramified case. Being unramified is fppf local on the
base. -/
public instance unramified_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget (@Unramified : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
  isLocalAtTarget_fppfPrecoverage _

/-- **Stacks 02WH**, entry (18), G-unramified case. Being G-unramified is fppf local on the
base. -/
public instance gUnramified_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget (@GUnramified : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
  isLocalAtTarget_fppfPrecoverage _

end Stacks.Descent

end
