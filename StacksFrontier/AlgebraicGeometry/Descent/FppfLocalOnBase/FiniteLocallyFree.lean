module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FiniteFreeActionSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.QuasiCompactLocal

/-!
# The finite locally free entry of the list of Tag 02WH

Tag 02WH lists the properties of morphisms of schemes which, being stable under base change,
are moreover *fpqc local on the base*, hence a fortiori *fppf local on the base*. This file
records the entry of that list about finite locally free morphisms, in both the shapes in which
Descent, Lemma 02VO states it: with the rank unconstrained, and with the rank fixed to a given
natural number.

## Main results

* `Stacks.Morphisms.isFiniteLocallyFreeOfRank_isLocalAtTarget_fppf`: being finite locally free
  of rank `d` is fppf local on the base.

## Implementation notes

Each entry of the list of Tag 02WH is stated, and carries the tag, as a single conjunction in
`StacksFrontier/AlgebraicGeometry/Descent/FppfLocalOnBase/Entries.lean`: the property is stable
under arbitrary base change, it is local on the base for the fpqc precoverage, **and** it is
local on the base for the fppf precoverage. Both shapes of this entry are stated there, with the
rank unconstrained and with the rank fixed. This file supplies the "a fortiori" half of the
remark for a fixed rank, that the property is local on the base for the fppf precoverage, proved
from the fpqc half by `Stacks.Descent.isLocalAtTarget_fppfPrecoverage`. That instance
deliberately does not carry the tag itself: one record per entry is what makes the tag's
coverage readable, and the conjunction that does carry it asserts this fppf locality itself, so
none of the remark's content rests on an untagged declaration.

With the rank unconstrained the same "a fortiori" half is
`Stacks.Morphisms.isFiniteLocallyFree_isLocalAtTarget_fppf`, recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/FiniteFreeActionSchematicLocus.lean`, which this
file imports; there is no second copy of it here.

## References

* [Stacks Project, Tag 02WH](https://stacks.math.columbia.edu/tag/02WH)
-/

@[expose] public section

open CategoryTheory MorphismProperty AlgebraicGeometry

universe u

namespace Stacks.Morphisms

/-! ### Finite locally free morphisms of a fixed rank -/

/-- **Stacks 02WH**, entry (22) of the list: **finite locally free**, Descent, Lemma 02VO, for a
fixed rank `d`. The source's "finite locally free" is `Stacks.Morphisms.IsFiniteLocallyFree` in
Lean, and of rank `d` it is `IsFiniteLocallyFreeOfRank.property d`. Being finite locally free of
rank `d` is fppf local on the base. -/
public instance isFiniteLocallyFreeOfRank_isLocalAtTarget_fppf (d : ℕ) :
    MorphismProperty.IsLocalAtTarget (IsFiniteLocallyFreeOfRank.property.{u} d)
      Scheme.fppfPrecoverage :=
  Stacks.Descent.isLocalAtTarget_fppfPrecoverage _

end Stacks.Morphisms

end
