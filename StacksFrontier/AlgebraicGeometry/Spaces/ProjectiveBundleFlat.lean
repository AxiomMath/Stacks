module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Properties
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.BaseChange
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocallyFreeFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFiniteLocallyFreeRank
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SurjectivePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionChart
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components

/-!
# The projection of the projective bundle is flat of relative dimension `r - 1`

Let `X` be an algebraic space over a scheme `S` and `ℰ` a quasi-coherent `𝒪_X`-module which is
finite locally free of rank `n + 1` in the sense of the rank clause of Stacks 0409.  The
projection `π : 𝐏(ℰ) ⟶ X` of the projective bundle is flat of relative dimension `n`.

Both properties are read on the presenting chart `U` of `X`, over which `π` is the projection of
the projective bundle of the chart restriction `ℰ|_U`, a module of rank `n + 1`
(`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_restrictToChartScheme`): there it is flat
and every nonempty fibre is equidimensional of dimension `n` (Stacks 02TX's finiteness
assertions, `Stacks.ProjectiveBundle.flat_toBase` and
`Stacks.ProjectiveBundle.relativeDimension_toBase`).  Flatness is étale local on source and
target (Stacks 03MJ), and relative dimension at a point of an algebraic space is read on one
pointed chart (Stacks 04NM).

## Main results

* `AlgebraicGeometry.Space.flat_and_relativeDimension_chartBundleToChart` and
  `AlgebraicGeometry.Space.topologicalKrullDimAt_fiber_chartBundleToChart`: over a chart.
* `AlgebraicGeometry.Space.isFlat_projectiveBundleProj`: **`π` is flat.**
* `AlgebraicGeometry.Space.hasRelativeDimension_projectiveBundleProj`: **`π` has relative
  dimension `n`.**

## References

* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 0ERT](https://stacks.math.columbia.edu/tag/0ERT)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (E : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite] (n : ℕ)
  (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) E (n + 1))

include hr

/-- The chart restriction of a module of rank `n + 1` has rank `n + 1`. -/
theorem isFiniteLocallyFreeOfRank_chartBundleModule (V : SmallEtale B S hS X.1) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (chartBundleModule E V) (n + 1) :=
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    (chartBundleModuleRestrictIso E V).symm
    (isFiniteLocallyFreeOfRank_restrictToChartScheme B S hS X E hE (n + 1) hr V)

/-- **Over a chart, the projection of the chart bundle is flat and of relative dimension `n`.**
The two presentations of the projective bundle of a quasi-coherent module agree over the base
(`AlgebraicGeometry.projectiveBundlePresentationsAgree`), and over the second the two properties
are Stacks 02TX. -/
theorem flat_and_relativeDimension_chartBundleToChart (V : SmallEtale B S hS X.1) :
    Flat (chartBundleToChart E V) ∧
      ∃ _ : LocallyOfFiniteType (chartBundleToChart E V),
        RelativeDimension (chartBundleToChart E V) n := by
  have := isFiniteLocallyFreeOfRank_chartBundleModule E n hr V
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (chartBundleModule E V) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ (n + 1)
  have hqc := Stacks.Chow.bundlePieces (chartBundleModule E V)
  obtain ⟨b, hb⟩ := projectiveBundlePresentationsAgree (chartBundleModule E V) hqc
  have heq : chartBundleToChart E V = b.inv ≫ (Stacks.SymGraded.schemeProjectiveBundle
      (chartBundleModule E V) hqc).toBase := by
    rw [Iso.eq_inv_comp]
    exact hb
  have hflat : Flat (Stacks.SymGraded.schemeProjectiveBundle (chartBundleModule E V) hqc).toBase :=
    Stacks.ProjectiveBundle.flat_toBase (chartBundleModule E V) hqc n
  have hlft : LocallyOfFiniteType
      (Stacks.SymGraded.schemeProjectiveBundle (chartBundleModule E V) hqc).toBase :=
    Stacks.ProjectiveBundle.locallyOfFiniteType_toBase (chartBundleModule E V) hqc n
  have hrel := Stacks.ProjectiveBundle.relativeDimension_toBase (chartBundleModule E V) hqc n
  rw [heq]
  refine ⟨inferInstance, inferInstance, ?_⟩
  exact RelativeDimension.comp_isOpenImmersion b.inv _ hrel

/-- **Over a chart, the fibres of the chart bundle have local dimension `n` at every point.** -/
theorem topologicalKrullDimAt_fiber_chartBundleToChart (V : SmallEtale B S hS X.1)
    (u : chartBundle E V) :
    topologicalKrullDimAt ((chartBundleToChart E V).fiber (chartBundleToChart E V u))
        ((chartBundleToChart E V).asFiber u) = (n : WithBot ℕ∞) := by
  obtain ⟨-, hlft, hrel⟩ := flat_and_relativeDimension_chartBundleToChart E n hr V
  set s := chartBundleToChart E V u
  obtain ⟨he, hd⟩ := hrel s ⟨(chartBundleToChart E V).asFiber u⟩
  have : LocallyOfFiniteType ((chartBundleToChart E V).fiberToSpecResidueField s) := by
    change LocallyOfFiniteType
      (Limits.pullback.snd (chartBundleToChart E V) ((chartScheme V).fromSpecResidueField s))
    infer_instance
  exact @topologicalKrullDimAt_eq_of_equidimensional _ _ _
    ((chartBundleToChart E V).fiberToSpecResidueField s) this _ he hd _

omit hr in
/-- The chart square of the projective bundle, in the form the chart criteria consume. -/
theorem projectiveBundleChart_comm (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E) :
    yoneda.map ((projectiveBundleChartFamily E hfree).siteToChart
        (presentationChart (projectiveBundlePresentation X))) ≫
        (presentationChart (projectiveBundlePresentation X)).obj.hom =
      projectiveBundleChart E hfree ≫ (projectiveBundleProj E hfree).hom :=
  (isPullback_projectiveBundleProj E hfree).w.symm

/-- **The projection `π : 𝐏(ℰ) ⟶ X` of the projective bundle of a module of rank `n + 1` is
flat.** -/
theorem isFlat_projectiveBundleProj (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E) :
    IsFlat B S hS (projectiveBundleProj E hfree).hom := by
  refine (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS _ isEtaleLocalOnSourceAndTarget_flat
    (projectiveBundle E hfree).2 X.2 _).2 ?_
  exact ⟨_, _, projectiveBundleChart E hfree,
    (presentationChart (projectiveBundlePresentation X)).obj.hom,
    (projectiveBundleChartFamily E hfree).siteToChart
      (presentationChart (projectiveBundlePresentation X)),
    (projectiveBundleChartFamily E hfree).etale_quotientChart _ _
      (isPullback_projectiveBundlePresentation X),
    (presentationChart (projectiveBundlePresentation X)).property,
    (projectiveBundleChartFamily E hfree).surjective_quotientChart _ _
      (isPullback_projectiveBundlePresentation X),
    projectiveBundleChart_comm E hfree,
    (flat_and_relativeDimension_chartBundleToChart E n hr _).1⟩

/-- **The projection `π : 𝐏(ℰ) ⟶ X` of the projective bundle of a module of rank `n + 1` has
relative dimension `n`.** -/
theorem hasRelativeDimension_projectiveBundleProj
    (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E) :
    HasRelativeDimension n B S hS (projectiveBundleProj E hfree).hom := by
  intro x
  obtain ⟨y, rfl⟩ := surjective_pointsMap_of_presheaf_surjective B S hS
    (projectiveBundleChart E hfree)
    ((projectiveBundleChartFamily E hfree).surjective_quotientChart _ _
      (isPullback_projectiveBundlePresentation X)) x
  obtain ⟨u, rfl⟩ := (pointsEquivScheme B S hS _).symm.surjective y
  refine (hasRelativeDimensionAt_pointsMap_iff B S hS (n : ℕ∞) _ _ _
    (projectiveBundleChart E hfree)
    (presentationChart (projectiveBundlePresentation X)).obj.hom
    ((projectiveBundleChartFamily E hfree).siteToChart
      (presentationChart (projectiveBundlePresentation X)))
    ((projectiveBundleChartFamily E hfree).etale_quotientChart _ _
      (isPullback_projectiveBundlePresentation X))
    (presentationChart (projectiveBundlePresentation X)).property
    (projectiveBundleChart_comm E hfree) u).2 ?_
  exact topologicalKrullDimAt_fiber_chartBundleToChart E n hr _ u

end AlgebraicGeometry.Space

end
