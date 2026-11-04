module

public import StacksFrontier.AlgebraicGeometry.DepthTwoReflexiveExtension.Extension
public import StacksFrontier.AlgebraicGeometry.InternalHomLocalKernel.Basic
public import StacksFrontier.Algebra.Module.Reflexive
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksCore.Tactic.StacksAttribute

/-!
# Depth two at the stalks of a coherent reflexive module

On a locally Noetherian scheme, a coherent reflexive module has depth at least two at every point
where the structure sheaf does. The stalk of such a module is a finite reflexive module over the
local ring, hence linearly equivalent to its double dual, and the dual of a finite module has
depth at least two whenever the ring does.

## Main results

* `two_le_depth_stalk_of_isCoherent_of_isReflexive`: a coherent reflexive module on a locally
  Noetherian scheme has depth at least two at every point where the structure sheaf does.
* `reflexiveDepthTwo`: the same statement in the form
  `Stacks.AlgebraicGeometry.DepthTwoReflexiveExtension.ReflexiveDepthTwo`.
* `depthTwoExtension_of_pushforwardPreservation`: on an integral locally Noetherian scheme whose
  structure sheaf has depth at least two off an open `U`, restriction to `U` and direct image
  form an equivalence of coherent reflexive modules, given that direct image along `U.ι`
  preserves coherence and reflexivity.

## Implementation notes

No integrality hypothesis is needed for the depth bound: reflexivity of the stalks comes from
reflexivity of the sheaf.

## References

* [Stacks Project, Tag 0EBI](https://stacks.math.columbia.edu/tag/0EBI)
* [Stacks Project, Tag 0EBA](https://stacks.math.columbia.edu/tag/0EBA)
* [Stacks Project, Tag 0AV5](https://stacks.math.columbia.edu/tag/0AV5)
* [Stacks Project, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ)
* [Stacks Project, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.AlgebraicGeometry.DepthTwoReflexiveExtension

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveStalkDepthTwo

variable {X : Scheme.{u}}

/-- On a locally Noetherian scheme, a coherent reflexive module has depth at least two at every
point at which the structure sheaf has depth at least two. -/
@[stacks 0EBI "part (1)"]
theorem two_le_depth_stalk_of_isCoherent_of_isReflexive [IsLocallyNoetherian X]
    (G : X.Modules) (hc : G.IsCoherent) (hr : IsReflexive G) (x : X)
    (hx : (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) := by
  have : G.IsCoherent := hc
  have : G.IsFinitePresentation := CoherentTFAE.isFinitePresentation_of_isCoherent' G
  have : (dualSheaf G).IsCoherent := InternalHomLocalKernel.isCoherent_dualSheaf G hc
  have : (dualSheaf G).IsFinitePresentation :=
    CoherentTFAE.isFinitePresentation_of_isCoherent' (dualSheaf G)
  have : G.IsFiniteType := StalkFiniteType.isFiniteType_of_isFinitePresentation G
  have : Module.Finite (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x)) :=
    StalkFiniteType.finite_stalk G x
  have : Module.IsReflexive (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x)) :=
    DepthTwoReflexiveExtension.isReflexive_stalk_of_isReflexive G hr x
  rw [Module.depth_eq_depth_of_linearEquiv _ (Module.evalEquiv (ToType (X.presheaf.stalk x))
    (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x)))]
  exact (one_le_depth_and_two_le_depth_linearMap
    (R := ToType (X.presheaf.stalk x))
    (M := Module.Dual (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x)))
    (N := ToType (X.presheaf.stalk x))).2 hx

/-- On an integral locally Noetherian scheme, a coherent reflexive module has depth at least two
at every point at which the structure sheaf has depth at least two. -/
example {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (hF : IsReflexive F) (x : X)
    (hx : (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :
    letI : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
  two_le_depth_stalk_of_isCoherent_of_isReflexive F ‹F.IsCoherent› hF x hx

/-- On a locally Noetherian scheme `X`, every coherent reflexive module has depth at least two
at every point where the structure sheaf does, in the form
`Stacks.AlgebraicGeometry.DepthTwoReflexiveExtension.ReflexiveDepthTwo X`. -/
theorem reflexiveDepthTwo [IsLocallyNoetherian X] : ReflexiveDepthTwo X :=
  two_le_depth_stalk_of_isCoherent_of_isReflexive

/-- On an integral locally Noetherian scheme whose structure sheaf has depth at least two off an
open `U`, restriction to `U` is an equivalence of the coherent reflexive modules with direct
image as inverse. It takes as hypothesis `hpush`: direct image along `U.ι` preserves coherence
and reflexivity. -/
noncomputable def depthTwoExtension_of_pushforwardPreservation (X : Scheme.{u}) (U : X.Opens)
    [IsIntegral X] [IsLocallyNoetherian X]
    (hdepth : StructureDepthTwoOff X U)
    (hpush : ∀ G : U.toScheme.Modules, G.IsCoherent → IsReflexive G →
      ((Scheme.Modules.pushforward U.ι).obj G).IsCoherent ∧
        IsReflexive ((Scheme.Modules.pushforward U.ι).obj G)) :
    ReflexiveExtensionGate.DepthTwoExtension X U :=
  depthTwoExtension_of_pushforward X U hdepth reflexiveDepthTwo hpush

end Stacks.AlgebraicGeometry.ReflexiveStalkDepthTwo

end
