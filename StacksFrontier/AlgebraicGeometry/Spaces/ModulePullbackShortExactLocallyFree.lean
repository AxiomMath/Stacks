module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackShortExactFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeDualShortExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRank

/-!
# The inverse image of a short exact sequence with finite locally free third term

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `0 → F → G → H → 0` a short exact
sequence of `𝒪_Y`-modules on the small étale site with `H` finite locally free of rank `r`.
Then `0 → f^*F → f^*G → f^*H → 0` is short exact.

A finite locally free module has a dual
(`AlgebraicGeometry.Space.hasRightDual_of_isFiniteLocallyFreeOnSite`), hence is flat
(`AlgebraicGeometry.Space.isFlat_of_hasRightDual`), and the inverse image of a short exact
sequence with flat third term is short exact
(`Stacks.Sheaves.RingedToposModules.shortExact_map_pullbackModules`, Stacks 0G6R).

## Main results

* `AlgebraicGeometry.Space.shortExact_map_modulePullback_of_isFiniteLocallyFreeOfRank`: **the
  inverse image along any morphism of algebraic spaces keeps a short exact sequence with finite
  locally free third term short exact.**

## References

* [Stacks Project, Tag 0G6R](https://stacks.math.columbia.edu/tag/0G6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

attribute [local instance] preservesZeroMorphisms_modulePullback

/-- **The inverse image along a morphism of algebraic spaces keeps a short exact sequence whose
third term is finite locally free short exact** (Stacks 0G6R, a finite locally free module being
flat). -/
theorem shortExact_map_modulePullback_of_isFiniteLocallyFreeOfRank (f : X ⟶ Y)
    (T : ShortComplex (Modules.{u, u} B S hS Y.1 Y.2)) (hT : T.ShortExact) {r : ℕ}
    (h₃ : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Y.1 Y.2) T.X₃ r) :
    (T.map (modulePullback B S hS f)).ShortExact :=
  letI := hasRightDual_of_isFiniteLocallyFreeOnSite B S hS Y.1 Y.2 T.X₃
    h₃.isFiniteLocallyFreeOnSite
  Stacks.Sheaves.RingedToposModules.shortExact_map_pullbackModules
    (smallEtaleRingedToposModulesHom B S hS f) T hT
    (isFlat_of_hasRightDual B S hS Y.1 Y.2 T.X₃)

end AlgebraicGeometry.Space

end
