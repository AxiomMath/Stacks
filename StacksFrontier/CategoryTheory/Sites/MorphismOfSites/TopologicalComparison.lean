module

public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits
public import Mathlib.Topology.Sheaves.Functors
import StacksCore.Tactic.EgaSgaAttribute

/-! # A continuous map of topological spaces is a morphism of sites

Let `f : X ⟶ Y` be a continuous map of topological spaces and give `X` and `Y` the small Zariski
sites `X_Zar`, `Y_Zar` of Stacks 00VJ, i.e. the lattices of open sets with the topology generated
by open coverings (`TopologicalSpace.Opens.grothendieckTopology`).  Stacks 00X2 considers the
functor `u : Y_Zar ⥤ X_Zar`, `V ↦ f⁻¹(V)`, which is `TopologicalSpace.Opens.map f`, and asserts:
`u` is continuous, the site-theoretic pushforward `u^s` is the topological `f_*`, the
site-theoretic
pullback `u_s` is the topological `f⁻¹`, and `u_s` is exact — so `u` defines a morphism of sites
`X_Zar → Y_Zar`.

## Main results

* `StacksZariskiSite.topPushforward_eq_sheafPushforwardContinuous`,
  `StacksZariskiSite.topPullback_eq_sheafPullback`,
  `StacksZariskiSite.topAdjunction_eq_sheafAdjunctionContinuous`: the topological pushforward,
  pullback and adjunction on sheaves are the site-theoretic `u^s`, `u_s` and `u_s ⊣ u^s`.
* `StacksZariskiSite.isMorphismOfSites_opensMap`: `u = Opens.map f` defines a morphism of sites
  `X_Zar → Y_Zar`; equivalently `u_s = f⁻¹` is exact.

Tags covered: 00X2.
-/

@[expose] public section

namespace StacksZariskiSite

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- **Stacks 00X2.** The site-theoretic pushforward `u^s` along `u = Opens.map f` is the usual
topological pushforward `f_*` on sheaves of sets: Mathlib's `TopCat.Sheaf.pushforward` is defined
to be precisely `(Opens.map f).sheafPushforwardContinuous`, so the identification asserted by the
example holds on the nose. -/
@[stacks 00X2]
theorem topPushforward_eq_sheafPushforwardContinuous :
    TopCat.Sheaf.pushforward (Type u) f =
      (Opens.map f).sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X) :=
  rfl

/-- **Stacks 00X2.** The site-theoretic pullback `u_s` along `u = Opens.map f` is the usual
topological pullback `f⁻¹` on sheaves of sets. -/
@[stacks 00X2]
theorem topPullback_eq_sheafPullback :
    TopCat.Sheaf.pullback (Type u) f =
      (Opens.map f).sheafPullback (Type u) (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X) :=
  rfl

/-- **Stacks 00X2.** Consequently the topological adjunction `f⁻¹ ⊣ f_*` is the site-theoretic
adjunction `u_s ⊣ u^s`; this is the step by which the example concludes `f⁻¹ ≅ u_s` from
uniqueness of adjoints. -/
@[stacks 00X2]
theorem topAdjunction_eq_sheafAdjunctionContinuous :
    TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f =
      (Opens.map f).sheafAdjunctionContinuous (Type u) (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X) :=
  rfl

/-- **Stacks 00X2.** The functor `u = Opens.map f : Y_Zar ⥤ X_Zar`, `V ↦ f⁻¹(V)`, defines a
morphism of sites `X_Zar → Y_Zar`: it is continuous, and the induced pullback `u_s = f⁻¹` on
sheaves of sets is exact.

Continuity is Mathlib's instance for `Opens.map f` and the Zariski topologies.  For exactness the
example argues that `u_s ≅ f⁻¹` is exact because `f⁻¹` is; here it is obtained from the criterion
of Stacks 00X5 (`CategoryTheory.Functor.isMorphismOfSites_of_representablyFlat`), whose hypothesis
`RepresentablyFlat (Opens.map f)` holds because the categories `I_V^u` of Stacks 00VC are the
lattices of open `W ⊆ Y` with `V ⊆ f⁻¹(W)`, which are closed under intersection and contain
`W = Y`. -/
@[stacks 00X2,
  sga "4 IV 4.1.1" "morphism of topoi Top(f)",
  sga "4 III 1.9.1" "continuity of f^{-1}"]
theorem isMorphismOfSites_opensMap :
    (Opens.map f).IsMorphismOfSites (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) :=
  Functor.isMorphismOfSites_of_representablyFlat (Opens.map f) _ _

end StacksZariskiSite
