module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Continuity of slice base change, for one morphism at a time

Base change `CategoryTheory.Over.pullback f : Over Y ⥤ Over X` along a morphism `f : X ⟶ Y`
needs only the pullbacks of `f` against the arrows into `Y`. That is Mathlib's
`CategoryTheory.Limits.HasPullbacksAlong f`, and it is the hypothesis carried by
`CategoryTheory.Over.pullback`, by `CategoryTheory.Over.mapPullbackAdj` and by the resulting
`(Over.pullback f).IsRightAdjoint`.

Continuity of `Over.pullback f` between the topologies localized at `Y` and at `X` is stated in
Mathlib under the global `CategoryTheory.Limits.HasPullbacks C` instead, even though its proof
uses nothing beyond that adjunction. This file restates it at `HasPullbacksAlong f`.

## Main results

* `CategoryTheory.GrothendieckTopology.isContinuous_overPullback`: `Over.pullback f` is
  continuous from `J.over Y` to `J.over X` as soon as `f` alone has base change.

## Implementation notes

The weaker hypothesis is what a site without fibre products needs. The comparison situation of
Stacks 0EZ3, `Stacks.ComparingTopologies.CohomologyComparison`, assumes base change for its
distinguished class of arrows (`CohomologyComparison.morphismProperty_baseChange`) and for its
covering families (`Precoverage.HasPullbacks`), and nothing else; so `HasPullbacks C` is not
available there, while `HasPullbacksAlong f` is available for every distinguished arrow `f`,
by `CohomologyComparison.morphismProperty_baseChange`. That is what puts the
slice morphism of topoi, and with it the Leray identification
`Stacks.Cohomology.Localization.cohomologyOverPushforwardIso` of Stacks 0D6H, inside the reach
of the situation.

Mathlib's companion `CategoryTheory.GrothendieckTopology.coverPreserving_overPullback` is not
restated here. Continuity is the stronger of the two statements and is not proved through cover
preservation — `CategoryTheory.Adjunction.isContinuous_of_isCocontinuous` goes through
representable flatness of a right adjoint — and `CoverPreserving.of_isContinuous` recovers cover
preservation from the instance below, so a second generalized spelling would be dead weight.

No Stacks attribute appears in this file: it states no tag, being the hypothesis-weakening of a
Mathlib instance.
-/

@[expose] public section

namespace CategoryTheory.GrothendieckTopology

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- **Base change between localized sites is continuous**, assuming only that the morphism `f`
itself has base change — `CategoryTheory.Limits.HasPullbacksAlong f` — and not that `C` has all
fibre products.

`Over.map f` is cocontinuous with no hypothesis whatever, and `Over.pullback f` is its right
adjoint by `Over.mapPullbackAdj f`; a right adjoint of a cocontinuous functor is continuous,
which is `CategoryTheory.Adjunction.isContinuous_of_isCocontinuous`. This is Mathlib's instance
of the same name for the same functor, with its `Limits.HasPullbacks C` weakened to the one
morphism at hand; the proof is the same term. -/
instance isContinuous_overPullback {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f] :
    (Over.pullback f).IsContinuous (J.over Y) (J.over X) :=
  (Over.mapPullbackAdj f).isContinuous_of_isCocontinuous _ _

end CategoryTheory.GrothendieckTopology

end
