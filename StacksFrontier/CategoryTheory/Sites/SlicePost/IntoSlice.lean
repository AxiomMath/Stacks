module

public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Sites.Over
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Continuity and cocontinuity of a functor into a slice site

Let `X` be an object of a site `(C, K)` and let `G : E ⥤ Over X` be a functor from a site `(E, J)`
into the slice. The continuity and the cocontinuity of `G` for the localized topology `K.over X`
follow from the same properties of the composite `G ⋙ Over.forget X`, which is a functor into `C`
itself.

## Main results

* `CategoryTheory.Sieve.functorPullback_eq_functorPullback_overEquiv` — pulling a sieve back along
  `G` is pulling its image in `C` back along `G ⋙ Over.forget X`.
* `CategoryTheory.Sieve.overEquiv_functorPushforward` — the image in `C` of the pushforward of a
  sieve along `G` is its pushforward along `G ⋙ Over.forget X`.
* `CategoryTheory.Functor.isCocontinuous_of_comp_overForget` — a functor into a slice site is
  cocontinuous as soon as its composite with the forgetful functor is.
* `CategoryTheory.CoverPreserving.of_comp_overForget` — the same for cover-preservation.
* `CategoryTheory.Functor.isContinuous_of_comp_overForget` — a functor into a slice site is
  continuous as soon as its composite with the forgetful functor is cover-preserving, provided
  the source has pullbacks and the functor preserves them.

## References

* [Stacks Project, Tag 03CF](https://stacks.math.columbia.edu/tag/03CF)
-/

@[expose] public section

open CategoryTheory.Limits

namespace CategoryTheory

universe v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] {E : Type u₂} [Category.{v₂} E]

namespace Sieve

/-- Pulling a sieve on `G.obj U` back along a functor `G : E ⥤ Over X` is pulling its image in
`C` under `CategoryTheory.Sieve.overEquiv` back along `G ⋙ Over.forget X`. -/
theorem functorPullback_eq_functorPullback_overEquiv {X : C} (G : E ⥤ Over X) {U : E}
    (S : Sieve (G.obj U)) :
    S.functorPullback G = (Sieve.overEquiv _ S).functorPullback (G ⋙ Over.forget X) := by
  rw [Sieve.functorPullback_comp]
  exact congrArg (Sieve.functorPullback G)
    (Sieve.functorPullback_functorPushforward_overForget S).symm

/-- The image in `C`, under `CategoryTheory.Sieve.overEquiv`, of the pushforward of a sieve along a
functor `G : E ⥤ Over X` is its pushforward along `G ⋙ Over.forget X`. -/
theorem overEquiv_functorPushforward {X : C} (G : E ⥤ Over X) {U : E} (S : Sieve U) :
    Sieve.overEquiv _ (S.functorPushforward G) = S.functorPushforward (G ⋙ Over.forget X) :=
  (Sieve.functorPushforward_comp _ _ _).symm

end Sieve

/-- A functor into a slice site is cocontinuous as soon as its composite with the forgetful
functor is. -/
theorem Functor.isCocontinuous_of_comp_overForget {X : C} (G : E ⥤ Over X)
    (J : GrothendieckTopology E) (K : GrothendieckTopology C)
    (h : (G ⋙ Over.forget X).IsCocontinuous J K) : G.IsCocontinuous J (K.over X) where
  cover_lift {_} {T} hT := by
    rw [Sieve.functorPullback_eq_functorPullback_overEquiv G T]
    exact h.cover_lift hT

/-- A functor into a slice site is cover-preserving as soon as its composite with the forgetful
functor is. -/
theorem CoverPreserving.of_comp_overForget {X : C} (G : E ⥤ Over X)
    (J : GrothendieckTopology E) (K : GrothendieckTopology C)
    (h : CoverPreserving J K (G ⋙ Over.forget X)) : CoverPreserving J (K.over X) G where
  cover_preserve {_} {T} hT := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_functorPushforward G T]
    exact h.cover_preserve hT

/-- A functor into a slice site is continuous as soon as its composite with the forgetful
functor is cover-preserving, provided the source has pullbacks and the functor preserves them. -/
@[sga "4 III 1.6" "special case"]
theorem Functor.isContinuous_of_comp_overForget {X : C} (G : E ⥤ Over X)
    (J : GrothendieckTopology E) (K : GrothendieckTopology C) [HasPullbacks E]
    [PreservesLimitsOfShape WalkingCospan G]
    (h : CoverPreserving J K (G ⋙ Over.forget X)) : G.IsContinuous J (K.over X) :=
  have : Functor.PreservesOneHypercovers.{max u₂ v₂} G J (K.over X) :=
    Functor.PreservesOneHypercovers.of_coverPreserving
      (CoverPreserving.of_comp_overForget G J K h)
  Functor.isContinuous_of_preservesOneHypercovers.{max u₂ v₂} _ _ _

end CategoryTheory

end
