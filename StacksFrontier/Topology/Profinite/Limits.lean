module

public import Mathlib.Topology.Category.Profinite.Basic

/-!
# A limit of profinite spaces is profinite

Stacks 0ET8 says that a limit of profinite spaces is profinite, where the limit is the one taken
in topological spaces: for a diagram `F` of profinite spaces, the topological limit of the
underlying spaces is compact, Hausdorff and totally disconnected.

This module holds the faithful statement of the tag, with the limit taken in `TopCat`. The
reviewed tree also registers 0ET8 on Mathlib's `Profinite.hasLimits` (in
`StacksCore.Topology.Profinite.Limits`); that is the weaker categorical statement, which only provides
some limit object inside the category `Profinite` and by itself says nothing about the limit in
`TopCat`. Here the tag is registered on
`Profinite.compactSpace_t2Space_totallyDisconnectedSpace_of_isLimit`, which is stated for an
arbitrary limit cone of `F ⋙ Profinite.toTopCat` in `TopCat`, and is proved by comparing that cone
with the image of Mathlib's explicit limit cone `Profinite.limitCone F`, whose underlying cone is
`TopCat`'s limit cone.

## Main results

* `Profinite.compactSpace_t2Space_totallyDisconnectedSpace_of_isLimit`: the point of any limit
  cone in `TopCat` of a small diagram of profinite spaces is compact, Hausdorff and totally
  disconnected.

## References

* [Stacks Project, Tag 0ET8](https://stacks.math.columbia.edu/tag/0ET8)
-/

@[expose] public section

open CategoryTheory Limits

universe v u

namespace Profinite

/-- **Stacks 0ET8.** A limit of profinite spaces is profinite: for a small diagram `F` of profinite
spaces, the point of any limit cone of the underlying diagram `F ⋙ Profinite.toTopCat` in `TopCat`
is compact, Hausdorff and totally disconnected.

This is the faithful form of the tag, with the limit taken in `TopCat`; the registration of 0ET8 on
`Profinite.hasLimits` in the reviewed tree is the weaker categorical statement that `Profinite` has
limits. -/
@[stacks 0ET8 "the limit is taken in `TopCat`, as an arbitrary limit cone of
  `F ⋙ Profinite.toTopCat`"]
theorem compactSpace_t2Space_totallyDisconnectedSpace_of_isLimit {J : Type v} [SmallCategory J]
    {F : J ⥤ Profinite.{max u v}} {c : Cone (F ⋙ Profinite.toTopCat)} (hc : IsLimit c) :
    CompactSpace c.pt ∧ T2Space c.pt ∧ TotallyDisconnectedSpace c.pt := by
  have h : IsLimit (Profinite.toTopCat.mapCone (limitCone.{v, u} F)) :=
    TopCat.limitConeIsLimit.{v, u} (F ⋙ Profinite.toTopCat)
  let e : (limitCone.{v, u} F).pt.toTop ≃ₜ c.pt := TopCat.homeoOfIso (h.conePointUniqueUpToIso hc)
  exact ⟨e.compactSpace, e.symm.isEmbedding.t2Space, e.totallyDisconnectedSpace⟩

end Profinite
