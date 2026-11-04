module

public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctors.FlatPullbackStalkFree
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeAtGenericPoints

/-!
# The pointwise stalk form of the generic-freeness condition of Situation 05MP

The condition `AlgebraicGeometry.FreeAtPointOfRank` of Situation 05MP — the module is finite
locally free of rank `p` on some neighbourhood of the point — implies that its stalk there is
free of rank `p`. The converse needs the module to be of finite presentation (Stacks 080Q) and is
not available in Situation 05MP, where the module is of finite type only; this is why the proof
of the first assertion of Stacks 05MS passes through the stalk in one direction only, descending
freeness of the stalk along a member of an fpqc covering and spreading it out again by the
dévissage of Stacks 05IA rather than by Stacks 080Q.

## Main results

* `AlgebraicGeometry.StalkFreeOfRank.of_freeAtPointOfRank`: freeness of rank `p` near a point
  gives a free stalk of rank `p` there.

## References

* [Stacks Project, Tag 05MP](https://stacks.math.columbia.edu/tag/05MP)
* [Stacks Project, Tag 05MS](https://stacks.math.columbia.edu/tag/05MS)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- **Freeness of rank `p` near a point gives a free stalk of rank `p` there.** The witness
neighbourhood carries the module as finite locally free of rank `p`, so the stalk of its
restriction there is free of rank `p`, and the inclusion of an open is flat. -/
theorem StalkFreeOfRank.of_freeAtPointOfRank {X : Scheme.{u}} (F : X.Modules) [F.IsFiniteType]
    (x : X) (p : ℕ) (h : FreeAtPointOfRank F x p) :
    StalkFreeOfRank F x p := by
  obtain ⟨U, hxU, hrank⟩ := h
  exact StalkFreeOfRank.of_isFiniteLocallyFreeOfRank_restrict F hxU p
    { exists_isFiniteLocallyFreeOfRankData := hrank.exists_isFiniteLocallyFreeOfRankData }

end AlgebraicGeometry

end
