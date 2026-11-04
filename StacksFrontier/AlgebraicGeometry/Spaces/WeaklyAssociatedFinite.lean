module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finite
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtCompactSet
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSchemePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedChartHenselization
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPoints

/-!
# Finiteness of the weakly associated points in a quasi-compact open

A coherent module on a locally Noetherian algebraic space has only finitely many weakly
associated points — the associated points, in the terminology the source uses once the space
is locally Noetherian — in any quasi-compact open subset of the space of points.

## Main results

* `AlgebraicGeometry.Space.weaklyAssociatedPoints_inter_finite`: **Stacks 0CUN**, that
  finiteness statement.

## Implementation notes

The source introduces no separate notion of associated point for an algebraic space and uses
the word "associated" for the weakly associated points of Stacks 0CTX once the space is
locally Noetherian, so `Ass(ℱ)` is `AlgebraicGeometry.Space.weaklyAssociatedPoints` here.
Locally Noetherian is the étale-local scheme property of Stacks 03E6 and quasi-compactness of
`W` is `IsCompact` for the topology of Stacks 03BX.

The source argument chooses a quasi-compact scheme `U` with an étale morphism `U → X` whose
image is `W`, observes that `U` is then Noetherian, and applies Stacks 05AF on `U`.  All three
of its inputs are carried here:

* the chart, affine even, is
  `AlgebraicGeometry.Space.exists_affine_etale_chart_of_isCompact`, and Noetherianity of its
  scheme is Stacks 03E8, `AlgebraicGeometry.Space.exists_atlas_iff_forall_etale`;
* coherence of the restriction of `ℱ` to that chart, in the shape Stacks 05AF consumes it, is
  `AlgebraicGeometry.Space.isCoherent_chartSchemeModule`, carried onto the restriction
  `AlgebraicGeometry.Space.restrictToChart` by
  `AlgebraicGeometry.Space.weaklyAssociatedPoints_restrictToChart_eq`;
* the transfer of weak association between `X` and a point of a scheme chart is Stacks 0CTW,
  conditions (1) and (2), in the form (in the namespace `AlgebraicGeometry`)
  `Space.isWeaklyAssociatedPoint_restrictToChart_iff_isWeaklyAssociatedPoint_of_isQuasicoherent`,
  whose hypothesis — quasi-coherence of the chart restriction on the *Zariski* site of the
  chart's scheme — is discharged by
  `AlgebraicGeometry.Space.isQuasicoherent_restrictToChart`.

Finiteness on the chart is Stacks 05AF, reached through the agreement of associated and weakly
associated points on a locally Noetherian scheme, Stacks 05AR.  The chart's scheme is affine,
so the quasi-compact open of it over which Stacks 05AF is applied is the whole of it.

Openness of `W` is a hypothesis of the source and is kept, but it is not used: the chart of
`AlgebraicGeometry.Space.exists_affine_etale_chart_of_isCompact` covers any quasi-compact set
of points, open or not.

The module universe is the universe of the schemes, which is the universe at which the chart
restriction lands in `AlgebraicGeometry.Scheme.Modules` of the chart's scheme and therefore the
one at which Stacks 05AF and Stacks 0CTW apply to it.

## References

* [Stacks Project, Tag 0CUN](https://stacks.math.columbia.edu/tag/0CUN)
* [Stacks Project, Tag 05AF](https://stacks.math.columbia.edu/tag/05AF)
* [Stacks Project, Tag 05AR](https://stacks.math.columbia.edu/tag/05AR)
* [Stacks Project, Tag 0CTW](https://stacks.math.columbia.edu/tag/0CTW)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **Stacks 0CUN.** Let `X` be a locally Noetherian algebraic space over a scheme `S` and let
`F` be a coherent `𝒪_X`-module.  Then the weakly associated points of `F` — the associated
points, in the terminology of the source — meet every quasi-compact open subset of `|X|` in a
finite set. -/
@[stacks 0CUN]
theorem weaklyAssociatedPoints_inter_finite
    (hX : HasEtaleLocalProperty B S hS X.1 (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (F : Modules.{u, u} B S hS X.1 X.2) [hF : IsCoherent B S hS X.1 X.2 F]
    (W : Set (points B S hS X.1)) (_hWopen : IsOpen W) (hWcompact : IsCompact W) :
    (weaklyAssociatedPoints B S hS X F ∩ W).Finite := by
  have : F.IsQuasicoherentOnSite := hF.toIsQuasicoherentOnSite
  -- An affine étale chart of `X` whose image on points covers `W`.
  obtain ⟨Z, c, hZaff, hc, hWsub⟩ :=
    exists_affine_etale_chart_of_isCompact B S hS X.1 X.2 hWcompact
  let A : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk c, hc⟩
  -- Its scheme is affine and, by Stacks 03E8, locally Noetherian.
  have haff : IsAffine (chartScheme A) := hZaff
  have : IsLocallyNoetherian (chartScheme A) :=
    (exists_atlas_iff_forall_etale B S hS X.1
      (fun Y : Scheme.{u} => IsLocallyNoetherian Y) X.2).mp hX Z c hc
  have hNA : IsNoetherianAffineChart B S hS X.1 A :=
    ⟨hZaff, IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top (chartScheme A)⟩⟩
  -- Every point of `W` comes from a point of the chart's scheme.
  have himg : ∀ x ∈ W, ∃ w : chartScheme A, chartSchemeToPoints B S hS X.1 A w = x := by
    intro x hx
    obtain ⟨p, hp⟩ := hWsub hx
    refine ⟨pointsEquivScheme B S hS Z p, ?_⟩
    have hsymm : (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj A)).symm
        (pointsEquivScheme B S hS Z p) = p :=
      (pointsEquivScheme B S hS Z).symm_apply_apply p
    rw [chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm, hsymm]
    exact hp
  -- Stacks 0CTW carries each weakly associated point of `F` in `W` to one of the restriction.
  have hsub : weaklyAssociatedPoints B S hS X F ∩ W ⊆
      chartSchemeToPoints B S hS X.1 A ''
        Stacks.Divisors.weaklyAssociatedPoints (restrictToChart B S hS X.2 F A) := by
    rintro x ⟨hxass, hxW⟩
    obtain ⟨w, hw⟩ := himg x hxW
    refine ⟨w, ?_, hw⟩
    refine (isWeaklyAssociatedPoint_restrictToChart_iff_isWeaklyAssociatedPoint_of_isQuasicoherent
      B S hS F A w
      (isQuasicoherent_restrictToChart B S hS X F hF.toIsQuasicoherentOnSite A)).mpr ?_
    rw [hw]
    exact hxass
  -- On the chart the restriction is coherent, so Stacks 05AF applies.
  have : SheafOfModules.IsCoherent
      (chartSchemeModule B S hS X F hF.toIsQuasicoherentOnSite A) :=
    isCoherent_chartSchemeModule B S hS X F hF A hNA
  have hfin : (Stacks.Divisors.weaklyAssociatedPoints
      (chartSchemeModule B S hS X F hF.toIsQuasicoherentOnSite A)).Finite := by
    have h := associatedPoints_inter_finite
      (chartSchemeModule B S hS X F hF.toIsQuasicoherentOnSite A) ⊤
      (by simpa using isCompact_univ (X := ↥(chartScheme A)))
    have heq : Stacks.Divisors.associatedPoints
          (chartSchemeModule B S hS X F hF.toIsQuasicoherentOnSite A) =
        Stacks.Divisors.weaklyAssociatedPoints
          (chartSchemeModule B S hS X F hF.toIsQuasicoherentOnSite A) :=
      associatedPoints_eq_weaklyAssociatedPoints _ _
    rw [heq] at h
    simpa using h
  refine Set.Finite.subset (Set.Finite.image _ ?_) hsub
  exact (congrArg Set.Finite (weaklyAssociatedPoints_restrictToChart_eq B S hS X F
    hF.toIsQuasicoherentOnSite A)).mpr hfin

end AlgebraicGeometry.Space

end
