module

public import StacksFrontier.AlgebraicGeometry.ReflexiveStalk.ClosedPoints
public import StacksFrontier.AlgebraicGeometry.ReflexiveOpenEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Reflexive
public import StacksFrontier.Algebra.Module.Reflexive
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Stacks, Tag 0EBF: flat pullback preserves coherent reflexive modules

Let `f : X ⟶ Y` be a flat morphism of integral locally Noetherian schemes and let `G` be a
coherent reflexive `𝒪_Y`-module.  Then `f^* G` is coherent and reflexive.  That is
[Stacks, Tag 0EBF](https://stacks.math.columbia.edu/tag/0EBF).

## Main results

* `isReflexive_pullback_of_opens`: the case of the inclusion of an open subscheme, with *no*
  hypothesis on the open — exactly the `hpullback` that
  `reflexiveCoherentEquivalenceOfPullbackPushforward` carries.
* `reflexiveCoherentEquivalenceOfPushforward`: **Tag 0EBJ from the direct-image step alone**,
  that is `reflexiveCoherentEquivalenceOfPullbackPushforward` with its `hpullback` hypothesis
  discharged.

## Method

The general statement is `isReflexive_pullback`, proved by the stalkwise criterion of Tag 0AY3
over the base change of Tag 0098 and the flat base change of reflexivity of Tag 0EB9.

For the inclusion of an open subscheme no hypothesis on the open is needed: an open immersion
is flat, an open subscheme of a locally Noetherian scheme is locally Noetherian, and a
*nonempty* open subscheme of an integral scheme is integral, while over an **empty** open
subscheme the stalkwise criterion is vacuously satisfied and every module is reflexive.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 0AY3](https://stacks.math.columbia.edu/tag/0AY3)
* [Stacks Project, Tag 0EB9](https://stacks.math.columbia.edu/tag/0EB9)
* [Stacks Project, Tag 0EBF](https://stacks.math.columbia.edu/tag/0EBF)
* [Stacks Project, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

open Stacks.SheafOfModules.SheafHomStalk

/-- Every module on a scheme with no points is reflexive: the stalkwise criterion for the
canonical map to the double dual has nothing to check. -/
public theorem isReflexive_of_isEmpty {X : Scheme.{u}} [IsEmpty X] (F : X.Modules) :
    IsReflexive F :=
  isIso_of_bijective_stalkHom _ fun x => (IsEmpty.false x).elim

/-- **Tag 0EBF, reflexivity of the pullback, for the inclusion of an open subscheme**, with no
hypothesis on the open.  This is exactly the `hpullback` hypothesis that
`reflexiveCoherentEquivalenceOfPullbackPushforward` carries. -/
public theorem isReflexive_pullback_of_opens (X : Scheme.{u}) [IsIntegral X]
    [IsLocallyNoetherian X] (U : X.Opens) (F : X.Modules) (hFcoh : F.IsCoherent)
    (hF : IsReflexive F) :
    IsReflexive ((Scheme.Modules.pullback U.ι).obj F) := by
  rcases isEmpty_or_nonempty (U : Type u) with hU | hU
  · have : IsEmpty U.toScheme := hU
    exact isReflexive_of_isEmpty _
  · have : Nonempty U := hU
    have : IsIntegral U.toScheme := inferInstance
    have := hFcoh
    exact isReflexive_pullback U.ι F hF

/-- **Stacks Project, Tag 0EBJ, from the direct-image step alone.**  On an integral locally
Noetherian scheme, restriction to an open subscheme whose complement has structure-sheaf depth at
least two is an equivalence on coherent reflexive modules, with direct image as its inverse.

This is `reflexiveCoherentEquivalenceOfPullbackPushforward` with its `hpullback` hypothesis
discharged by `isReflexive_pullback_of_opens`, that is by Tag 0EBF clause (2).  The one hypothesis
that remains is the direct-image extension step, so the tag is still withheld. -/
-- stacks attribute for 0EBJ withheld: the direct-image extension step is still assumed here.
public noncomputable def reflexiveCoherentEquivalenceOfPushforward (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens)
    (hdepth : ∀ x : X, x ∉ (U : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
    (hpushforward : ∀ G : U.toScheme.Modules, G.IsCoherent → IsReflexive G →
      ((Scheme.Modules.pushforward U.ι).obj G).IsCoherent ∧
        IsReflexive ((Scheme.Modules.pushforward U.ι).obj G)) :
    Σ e : ReflexiveCoherentModules X ≌ ReflexiveCoherentModules U.toScheme,
      (e.functor ⋙ ObjectProperty.ι
          (fun F : U.toScheme.Modules =>
            F.IsCoherent ∧ IsReflexive F) ≅
        ObjectProperty.ι
          (fun F : X.Modules => F.IsCoherent ∧ IsReflexive F) ⋙
          Scheme.Modules.pullback U.ι) ×
      (e.inverse ⋙ ObjectProperty.ι
          (fun F : X.Modules => F.IsCoherent ∧ IsReflexive F) ≅
        ObjectProperty.ι
          (fun F : U.toScheme.Modules =>
            F.IsCoherent ∧ IsReflexive F) ⋙
          Scheme.Modules.pushforward U.ι) :=
  reflexiveCoherentEquivalenceOfPullbackPushforward X U hdepth
    (isReflexive_pullback_of_opens X U) hpushforward

end Stacks.AlgebraicGeometry.ReflexiveModules

end
