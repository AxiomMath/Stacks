module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomUniverseLift
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionInternalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.InternalHomQuasicoherentPresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationSiteEquivalence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-coherence of the internal Hom on an étale chart where the source is presented

`AlgebraicGeometry.Space.isQuasicoherentOnSite_smallEtaleInternalHom_of_presentation'` proves
quasi-coherence of `𝓗om_{𝒪_F}(M, N)` when `M` carries a presentation by finite free modules on
the small étale site of `F` *itself*.  The hypothesis of clause (6) of Stacks 03M1 is
Stacks 03DL(7), which is local: a finite presentation on a covering of each étale chart.  This
file closes that gap at a single chart, which is all the locality of quasi-coherence then needs.

Three steps, and each was missing before:

* the finite presentation of `M` on the slice at a chart is carried to the small étale site of
  the chart by `Stacks.SheafOfModules.hasFiniteGlobalPresentation_reindex'`;
* the internal Hom commutes with that passage, by
  `AlgebraicGeometry.Space.chartSmallEtaleRestrictionInternalHomIso`;
* and the universe lift of the sections, which the presented statement forces — its modules live
  at the module universe `max (u + 1) m` in which the internal Hom itself lives, never at `m` —
  is invisible to the internal Hom, by
  `Stacks.SheafOfModules.InternalHom.internalHomUliftIso`.

Without the third step the only modules the presented statement could speak about are those whose
sections already contain `u + 1`, and a coherent `𝒪_F`-module is not one of those: it is a
`AlgebraicGeometry.Space.Modules.{u, u}`.

## Main definitions

* `AlgebraicGeometry.Space.uliftModules`: the universe lift of the sections of an `𝒪_F`-module to
  the universe `u + 1` in which the internal Hom has its own sections.
* `AlgebraicGeometry.Space.smallEtaleInternalHomUliftIso`: **the internal Hom of `𝒪_F`-modules
  does not see that lift**, in either variable.

## Main results

* `AlgebraicGeometry.Space.hasFiniteGlobalPresentation_chartSmallEtaleRestriction'`: a finite
  global presentation on the slice at an étale chart is one on the small étale site of the chart.
* `Space.isQuasicoherentOnSite_smallEtaleInternalHom_over_of_hasFiniteGlobalPresentation`:
  **the restriction of `𝓗om_{𝒪_F}(M, N)` to the slice at an étale chart is quasi-coherent as
  soon as `M` has a finite global presentation on that slice and `N` is quasi-coherent.**
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_smallEtaleInternalHom`: **the internal-Hom
  clause of Stacks 03M1** — the internal Hom of two quasi-coherent `𝒪_F`-modules, the first of
  finite presentation, is quasi-coherent.

## Implementation notes

The chart-local step carries no `@[stacks 03M1]` attribute.  Clause (6) itself is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_smallEtaleInternalHom`, at the end of this file,
which assembles the chart-local step by locality of quasi-coherence.  Clause (5) is registered on
`AlgebraicGeometry.Space.isQuasicoherentOnSite_tensorModule`.

The module universe is pinned to `u`, the universe of the schemes, which is where the
quasi-coherent and the coherent `𝒪_F`-modules of this development live
(`AlgebraicGeometry.Space.IsCoherent`, `AlgebraicGeometry.Space.chartSmallEtaleRestriction`).
What pins it is `AlgebraicGeometry.Space.isQuasicoherentOnSite_chartSmallEtaleRestriction`,
Stacks 03DM in the direction from the slice to the chart, which this development has only at
that universe; the other three inputs are at a free module universe.

The étale chart is taken as an object of `(smallEtaleRingedSite B S hS F hF).C` rather than of
`AlgebraicGeometry.Space.SmallEtale B S hS F`.  The two are the same type, but the restriction
`SheafOfModules.over` of an `𝒪_F`-module to the slice at it carries the category instance of the
first spelling, and at the pinned module universe `u` instance search does not find
`CategoryTheory.Category (CategoryTheory.Over V)` from the second.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The universe lift of the sections of an `𝒪_F`-module to `u + 1`, the universe in which the
internal Hom of `𝒪_F`-modules has its own sections.  This is the lift that the global
presentations of Stacks 03DE take, and the one
`AlgebraicGeometry.Space.smallEtaleInternalHomUliftIso` shows the internal Hom cannot see. -/
noncomputable abbrev uliftModules (G : Modules.{u, m} B S hS F hF) :
    Modules.{u, max (u + 1) m} B S hS F hF :=
  SheafOfModules.uliftForPresentation.{u + 1, u, u, m, u + 1} G

/-- **The internal Hom of `𝒪_F`-modules does not see a universe lift of the sections of its
arguments**, in either variable:

`𝓗om_{𝒪_F}(ULift G, ULift G') ≅ 𝓗om_{𝒪_F}(G, G')`.

Both sides are `𝒪_F`-modules with sections in `max (u + 1) m`: the internal Hom of modules with
sections in `m` already has its own there, so the lift raises nothing.

This is `Stacks.SheafOfModules.InternalHom.internalHomUliftIso` at the small étale ringed site,
read through the fully faithful forgetful functor from sheaves of modules. -/
noncomputable def smallEtaleInternalHomUliftIso (G G' : Modules.{u, m} B S hS F hF) :
    smallEtaleInternalHom B S hS F hF (uliftModules B S hS F hF G)
        (uliftModules B S hS F hF G') ≅
      smallEtaleInternalHom B S hS F hF G G' :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (Stacks.SheafOfModules.InternalHom.internalHomUliftIso
      (O := (smallEtaleRingedSite B S hS F hF).O.obj)
      (hO := ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).property) G G')

/-- **A finite global presentation on the slice at an étale chart is one on the small étale site
of the chart.**  This is `Stacks.SheafOfModules.hasFiniteGlobalPresentation_reindex'` at the
comparison of Stacks 04M0, whose two continuity hypotheses are supplied as explicit arguments:
`AlgebraicGeometry.Space.isContinuous_chartLocalization_chartSpace` is stated for
`AlgebraicGeometry.Space.SmallEtale.chartLocalization`, and the equivalence's `functor` field
reaches it only by unfolding
`AlgebraicGeometry.Space.SmallEtale.chartLocalizationEquivalence`, which instance search does not
do.

It is the finite analogue of the presentation transport inside
`AlgebraicGeometry.Space.isQuasicoherentOnSite_over_of_chartSmallEtaleRestriction'`, and is
written in the same `@`-applied style for the same reason. -/
theorem hasFiniteGlobalPresentation_chartSmallEtaleRestriction'
    (X : AlgebraicSpaces B S hS) (M : SheafOfModules.{m} (structureRingSheaf B S hS X))
    (U : SmallEtale B S hS X.1) (h : (M.over U).HasFiniteGlobalPresentation) :
    (chartSmallEtaleRestriction' B S hS X M U).HasFiniteGlobalPresentation :=
  @Stacks.SheafOfModules.hasFiniteGlobalPresentation_reindex' _ _ _ _ _ _
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 U)
    (isContinuous_chartLocalization_chartSpace B S hS X U)
    (@Functor.IsDenseSubsite.instIsContinuous _ _ _ _ _ _ _
      (isDenseSubsite_chartLocalizationEquivalence_inverse B S hS X U))
    ((structureRingSheaf B S hS X).over U) (M.over U) h

/-- **The chart-local step of clause (6) of Stacks 03M1.**  Let `M`, `N` be `𝒪_F`-modules on an
algebraic space with `N` quasi-coherent, and let `V` be an étale scheme chart on whose slice `M`
has a finite global presentation.  Then the restriction of `𝓗om_{𝒪_F}(M, N)` to the slice at `V`
is quasi-coherent.

The proof is the source's: pass to the small étale site of the chart, where the internal Hom is
the internal Hom of the restrictions
(`AlgebraicGeometry.Space.chartSmallEtaleRestrictionInternalHomIso`) and the presentation is a
presentation
(`AlgebraicGeometry.Space.hasFiniteGlobalPresentation_chartSmallEtaleRestriction'`), and apply
the globally presented case
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_smallEtaleInternalHom_of_presentation'`) there.
That case lives at the module universe `max (u + 1) u` of the internal Hom, so its conclusion is
about the universe lifts of the two restrictions; the lift is undone by
`AlgebraicGeometry.Space.smallEtaleInternalHomUliftIso`. -/
theorem isQuasicoherentOnSite_smallEtaleInternalHom_over_of_hasFiniteGlobalPresentation
    (M N : Modules.{u, u} B S hS F hF) (hN : N.IsQuasicoherentOnSite)
    (V : (smallEtaleRingedSite B S hS F hF).C)
    (hMV : (M.over V).HasFiniteGlobalPresentation) :
    ((smallEtaleInternalHom B S hS F hF M N).over V).IsQuasicoherentOnSite := by
  have hpres : (chartSmallEtaleRestriction' B S hS ⟨F, hF⟩ M V).HasFiniteGlobalPresentation :=
    hasFiniteGlobalPresentation_chartSmallEtaleRestriction' B S hS ⟨F, hF⟩ M V hMV
  have hNc : (chartSmallEtaleRestriction' B S hS ⟨F, hF⟩ N V).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_chartSmallEtaleRestriction B S hS ⟨F, hF⟩ N hN V
  obtain ⟨p, q, P, Q, ιP, ιQ, hP, hQ, a, b, hab, hb⟩ := hpres
  refine isQuasicoherentOnSite_over_of_chartSmallEtaleRestriction' B S hS ⟨F, hF⟩
    (smallEtaleInternalHom B S hS F hF M N) V ?_
  refine (_root_.SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u + 1}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (chartSpace B S hS ⟨F, hF⟩ V).1 (chartSpace B S hS ⟨F, hF⟩ V).2).O))).prop_of_iso
    ((smallEtaleInternalHomUliftIso.{u, u} B S hS (chartSpace B S hS ⟨F, hF⟩ V).1
      (chartSpace B S hS ⟨F, hF⟩ V).2 (chartSmallEtaleRestriction' B S hS ⟨F, hF⟩ M V)
      (chartSmallEtaleRestriction' B S hS ⟨F, hF⟩ N V)) ≪≫
      (chartSmallEtaleRestrictionInternalHomIso.{u, u} B S hS ⟨F, hF⟩ M N V).symm) ?_
  exact isQuasicoherentOnSite_smallEtaleInternalHom_of_presentation'.{u, u}
    ιP hP.some ιQ hQ.some
    hab hb.some
    (_root_.SheafOfModules.isQuasicoherentOnSite_uliftForPresentation'.{u + 1, u, u, u, u + 1}
      hNc)

section InternalHom

/-- **Stacks 03M1, the internal Hom.**  Let `F` be an algebraic space over a scheme `S` and let
`M`, `N` be quasi-coherent `𝒪_F`-modules with `M` of finite presentation, Stacks 03DL(7).  Then
the internal Hom `𝓗om_{𝒪_F}(M, N)` is quasi-coherent.

The internal Hom is `AlgebraicGeometry.Space.smallEtaleInternalHom`, formed on the small étale
ringed site of `F`; its sections over an étale chart `U` are the morphisms `M|_U ⟶ N|_U`, so they
lie in `u + 1` even though those of `M` and `N` lie in `u`.

The proof is the source's.  Quasi-coherence is local on a covering of each object
(`Stacks.SheafOfModules.isQuasicoherentOnSite_of_locally_over`), the finite-presentation
hypothesis supplies for each étale chart a covering on whose members `M` has a finite global
presentation, and on such a member the conclusion is
`isQuasicoherentOnSite_smallEtaleInternalHom_over_of_hasFiniteGlobalPresentation`: restriction
to an étale chart is a localization and formation of internal Hom commutes with localization
(Stacks 04M1 and 0E8H), so the chart case is the globally presented case
`AlgebraicGeometry.Space.isQuasicoherentOnSite_smallEtaleInternalHom_of_presentation'` on the
small étale site of the chart.

The quasi-coherence of `M` is one of the source's hypotheses and is listed; the proof does not
use it, since finite presentation already implies it. -/
@[stacks 03M1 "(6) internal hom out of a module of finite presentation",
  sga "3 III 0.6" "more general"]
theorem isQuasicoherentOnSite_smallEtaleInternalHom (M N : Modules.{u, u} B S hS F hF)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (hMfp : M.IsFinitePresentationOnSite) :
    (smallEtaleInternalHom B S hS F hF M N).IsQuasicoherentOnSite := by
  refine Stacks.SheafOfModules.isQuasicoherentOnSite_of_locally_over _ fun U => ?_
  obtain ⟨I, V, f, hcov, hpres⟩ := hMfp.locally_hasFiniteGlobalPresentation U
  exact ⟨I, V, f, hcov, fun i =>
    isQuasicoherentOnSite_smallEtaleInternalHom_over_of_hasFiniteGlobalPresentation
      B S hS F hF M N hN (V i) (hpres i)⟩

end InternalHom

end AlgebraicGeometry.Space

end
