module

/-
Copyright (c) 2026 the Stacks in Lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import StacksFrontier.CategoryTheory.Sites.UniverseBridge.ExactnessFromSmallDiagrams
public import StacksFrontier.CategoryTheory.Sites.UniverseBridge.SheafDensity

/-!
# The universe transfer for left exactness of the sheaf pullback

`ExactnessFromSmallDiagrams` reduces left exactness of the pullback on large-valued sheaves to
left exactness on small-valued ones, given a filtered presentation of every finite diagram of
large-valued sheaves by small-valued ones. `SheafDensity` supplies those presentations. Composing
the two discharges the hypothesis, so left exactness at the site's own universe transfers to every
larger valuation universe with **no** added assumption.

This is what lets a morphism of sites — whose definition fixes the valuation universe to the
site's, as Stacks 00X1 does — be used on sheaves valued in any larger universe.

## Main results

* `preservesFiniteLimits_sheafPullback_large`: the transfer.

## References

* [Stacks Project, Tag 0GN2](https://stacks.math.columbia.edu/tag/0GN2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.Sites.UniverseBridge

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (F : C ⥤ D) [F.IsContinuous J K]

/-- **Left exactness of the sheaf pullback transfers to a larger valuation universe.** The
presentation hypothesis of `preservesFiniteLimits_sheafPullback_of_small_presentations` is
discharged by `exists_small_presentation`, so this carries no extra assumption: left exactness at
the site's own universe is all that is required.

This is the universe bridge of Stacks 0GN2. The hypothesis is exactly the `preservesFiniteLimits`
field of `Functor.IsMorphismOfSites`, which is stated at the site universe. -/
public theorem preservesFiniteLimits_sheafPullback_large
    (hsmall : PreservesFiniteLimits (F.sheafPullback (Type u) J K)) :
    PreservesFiniteLimits (F.sheafPullback (Type (max u v)) J K) :=
  preservesFiniteLimits_sheafPullback_of_small_presentations J K F hsmall
    fun T _ _ G => exists_small_presentation J T G

end Stacks.Sites.UniverseBridge

end
