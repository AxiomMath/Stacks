module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.GlobalSheafCohomology

/-!
# Carrying the engine's vanishing off the fibre and into the module-valued spelling

Part (2) of [Stacks, Tag 0897], in the form the fibre of [Stacks, Tag 0D2N] uses it, concludes
on the fibre and in the group-valued model of cohomology: its conclusion is

`IsZero (Hgroup Z.ringCatSheaf ⊤ p 𝒢)` for `Z = X_y`,

where `Hgroup R ⊤ p` — which lives in the **root** namespace, not in `Stacks.Cohomology`, and is
written `_root_.Hgroup` below — is the `p`-th right derived functor of sections over `⊤`,
valued in `AddCommGrpCat`. What assertion (B) of [Stacks, Tag 0D2M] consumes — the hypothesis
`hgr` of `Stacks.Cohomology.FormalFunctions.exists_surjective_fibreCohomology_twistModule` — is

`IsZero ((((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).obj 𝓕)`

on `X`, where `moduleGlobalSections X` is `SheafOfModules.evaluation X.ringCatSheaf (op ⊤)`,
valued in `ModuleCat Γ(X, ⊤)`. Two things differ: the scheme, and the functor. This file composes
the two existing comparisons that close both gaps, so that the assembly has one name to use.

## Main results

* `Stacks.Cohomology.FormalFunctions.isZero_rightDerived_pushforward_iff_isZero_hgroup` — for a
  closed immersion `v : Z ⟶ X` and `𝒢` on `Z`, the module-valued `p`-th cohomology of `v_* 𝒢`
  on `X` vanishes exactly when the group-valued `Hᵖ(Z, 𝒢)` does.

## Both gaps were already closed; this adds no mathematics

Neither difference needed new work, and it is worth recording which declarations settle them,
because they live in two distant files.

* **The scheme.** `Stacks.Cohomology.ClosedImmersion.isZero_hgroup_iff_pushforward`
  (`../ClosedImmersionCohomology/GlobalSheafCohomology.lean`) is the group-valued form of
  [Stacks, Tag 089W] along a closed immersion: `IsZero (Hgroup Z.ringCatSheaf ⊤ n 𝒢)` holds
  exactly when `IsZero (Hgroup X.ringCatSheaf ⊤ n (v_* 𝒢))` does. It is an `Iff`, so it
  transports vanishing in both directions, and — as in the proof of assertion (B) — it asks
  **no quasi-coherence** of `𝒢` and nothing of `v` beyond being a closed immersion. That is why
  the three `@[stacks 089W]` sites, which all ask `[IsAffineHom]` and `[IsQuasicoherent]`, are
  not used.
* **The functor.** `Stacks.Cohomology.ModuleComparison`
  `.isZero_rightDerived_evaluation_iff_isZero_hgroup`
  (`../../Topology/Sheaves/Cohomology/ModuleComparison/VanishingTransfer.lean`) is
  `IsZero (((SheafOfModules.evaluation R (op U)).rightDerived n).obj F) ↔ IsZero (Hgroup R U n F)`
  for an arbitrary ring sheaf on an arbitrary space. Since
  `Stacks.Cohomology.AffineBase.moduleGlobalSections X` is an `abbrev` for
  `SheafOfModules.evaluation X.ringCatSheaf (op ⊤)`, it applies at `R = X.ringCatSheaf`, `U = ⊤`
  with nothing to transport. Its own proof goes by `ModuleCat.isZero_iff_subsingleton` and
  `AddCommGrpCat.subsingleton_of_isZero` over
  `Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso`, which identifies the
  forgetful image of the module-valued derived sections with `Hgroup`.

The remaining identification — of `v_* 𝒢`, for `𝒢` the twisted graded layer on the fibre, with
`Limits.kernel (Stacks.Algebraization.idealPowerQuotientDrop (𝔪 · 𝒪_X) (Nat.le_succ n) ℱ(d))`,
which is the commutation of the layer with the twist together with [Stacks, Tag 08M3]
(`Stacks.Algebraization.idealQuotientPushforwardIso`) — is not built here either. It is
`Stacks.Algebraization.kernelIdealPowerQuotientDropTwistReesIso`
(`FibreLayerTwistKernel.lean`), and with it `hgr` is discharged outright, in
`Stacks.GradedProperCohomology.exists_isZero_rightDerived_kernelIdealPowerQuotientDropTwist`
(`../GradedProperCohomology/FibreLayerVanishing.lean`).

## References

* [Stacks Project, Tag 0D2M](https://stacks.math.columbia.edu/tag/0D2M)
* [Stacks Project, Tag 0D2N](https://stacks.math.columbia.edu/tag/0D2N)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Cohomology.FormalFunctions

/-- **The engine's vanishing, read on the base and in the module-valued spelling.** For a closed
immersion `v : Z ⟶ X` of schemes, a sheaf of modules `𝒢` on `Z` and `p ≥ 0`, the `p`-th right
derived functor of module-valued global sections of `v_* 𝒢` on `X` is a zero object exactly when
the group-valued `Hᵖ(Z, 𝒢)` is.

This is the interface between part (2) of [Stacks, Tag 0897] on the fibre, whose conclusion is
the right-hand side at `Z = X_y`, and the hypothesis `hgr` of the two assertions of
[Stacks, Tag 0D2M] over a local base, whose shape is the left-hand side.

Both halves are already in the library: the scheme is handled by
`Stacks.Cohomology.ClosedImmersion.isZero_hgroup_iff_pushforward`, which needs no
quasi-coherence, and the functor by `Stacks.Cohomology.ModuleComparison`
`.isZero_rightDerived_evaluation_iff_isZero_hgroup`, which applies on the nose because
`Stacks.Cohomology.AffineBase.moduleGlobalSections X` is an `abbrev` for
`SheafOfModules.evaluation X.ringCatSheaf (op ⊤)`. -/
theorem isZero_rightDerived_pushforward_iff_isZero_hgroup {Z X : Scheme.{u}} (v : Z ⟶ X)
    [IsClosedImmersion v] (G : Z.Modules) (p : ℕ) :
    IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).obj
        ((Scheme.Modules.pushforward v).obj G)) ↔
      IsZero (_root_.Hgroup Z.ringCatSheaf ⊤ p G) :=
  (Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup
      X.ringCatSheaf ⊤ p ((Scheme.Modules.pushforward v).obj G)).trans
    (Stacks.Cohomology.ClosedImmersion.isZero_hgroup_iff_pushforward v G p).symm

end Stacks.Cohomology.FormalFunctions

end
