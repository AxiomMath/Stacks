module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.ClosedSubspaceExistence

/-!
# Sheaves supported on a closed subset, with the object universe freed

Stacks Tag 00AH is `Stacks.essImage_sheafPushforward_subsetInclusion_iff` (with
`Stacks.full_and_faithful_sheafPushforward_subsetInclusion`), in
`StacksFrontier.Topology.Sheaves.ClosedImmersion.PushforwardAlgStruct`. It is stated for an
`AlgebraicStructureType.{u, w}` with the object universe `w` independent of the hom universe
`u`, so it applies to `CommRingCat.{u}`, an `AlgebraicStructureType.{u, u + 1}`. The older
`Stacks.essImage_pushforward_subsetInclusion_iff` in the same file is stated for an
`AlgebraicStructureType.{u, u}` and does not apply to `CommRingCat.{u}`. The implication that
is needed downstream — stalks terminal off a closed set implies the sheaf is pushed forward from
that set — was proved separately, with the object universe kept independent of the hom
universe and under `HasColimits`, in `Stacks.ClosedImmersion`
(`StacksFrontier/AlgebraicGeometry/ClosedImmersion/ClosedSubspaceExistence.lean`). Those
declarations are re-exported here and nothing is redeclared.

## Main declarations

* `commRingAlgStructure` is `CommRingCat.{u}` as a type of algebraic structure, with its
  objects in `Type (u + 1)`, and `commRingAlgStructureWithFinal` equips it with the final
  object `PUnit`.
* `closedSupport_isTerminalSections`: a sheaf whose stalks on an open `W` are all final has
  final sections on `W`.
* `closedSupport_essImage_of_terminal_stalks`: a sheaf whose stalks vanish off a closed `Z`
  lies in the essential image of pushforward along `Z ↪ X`.

## References

* [Stacks Project, Tag 00AH](https://stacks.math.columbia.edu/tag/00AH)
* [Stacks Project, Tag 01HN](https://stacks.math.columbia.edu/tag/01HN)
-/

@[expose] public section

namespace Stacks.ClosedSubspaceIdeal

export Stacks.ClosedImmersion (commRingAlgStructure commRingAlgStructureWithFinal
  closedSupport_isTerminalSections closedSupport_isIsoRestriction
  closedSupport_essImage_of_terminal_stalks)

end Stacks.ClosedSubspaceIdeal
