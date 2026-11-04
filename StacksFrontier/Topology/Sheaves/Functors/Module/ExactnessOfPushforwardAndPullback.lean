module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPullbackRightExact
public import StacksFrontier.Topology.Sheaves.Functors.Pushforward.Injective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Exactness of pushforward and pullback of sheaves of modules

For a morphism of ringed spaces `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)`, pushforward of sheaves of modules
commutes with all limits and pullback commutes with all colimits; in particular `f_*` is left
exact and `f^*` is right exact.

For a continuous map of spaces, the inverse image of sheaves of abelian groups is exact.

## Main results

* `RingedSpaceModuleAdjunction.preservesLimits_modulePushforward`: pushforward commutes with all
  limits.
* `RingedSpaceModuleAdjunction.exactFunctor_sheafPullback`: the inverse image of sheaves of
  abelian groups is exact.

## References

* [Stacks Project, Tag 01AJ](https://stacks.math.columbia.edu/tag/01AJ)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace RingedSpaceModuleAdjunction

/-- Pushforward of sheaves of modules along a morphism of ringed spaces commutes with all
limits. -/
@[stacks 01AJ "(1)", sga "4 IV 13.6" "ringed spaces, u_*"]
public lemma preservesLimits_modulePushforward {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    PreservesLimitsOfSize.{u, u} (modulePushforward f) :=
  (modulePullbackPushforwardAdjunction f).rightAdjoint_preservesLimits

/-- The inverse image of sheaves of abelian groups along a continuous map is exact. -/
@[stacks 01AJ "(3)"]
public lemma exactFunctor_sheafPullback {Xt Yt : TopCat.{u}} (g : Xt ⟶ Yt) :
    exactFunctor (TopCat.Sheaf AddCommGrpCat.{u} Yt) (TopCat.Sheaf AddCommGrpCat.{u} Xt)
      (TopCat.Sheaf.pullback AddCommGrpCat.{u} g) :=
  ⟨TopCat.Sheaf.pullback_preservesFiniteLimits g,
    PreservesColimits.preservesFiniteColimits _⟩

end RingedSpaceModuleAdjunction

add_to_stacks 01AJ "(2)" RingedSpaceModuleAdjunction.preservesColimits_modulePullback

end
