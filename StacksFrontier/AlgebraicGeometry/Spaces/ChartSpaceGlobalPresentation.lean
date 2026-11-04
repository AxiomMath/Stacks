module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackChartInjectives
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineSectionBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.GlobalPresentationComparison

/-!
# Global presentations across the chart-space comparison of Stacks 04M0

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `W` be
an étale scheme chart of `X`.  The pullback of `𝒪_X`-modules along the structure morphism of `W`
is restriction to the slice `X_étale/W` read through the comparison equivalence of Stacks 04M0,
so a global presentation of `M|_W` *on the slice* is a global presentation of the pullback *on
the whole small étale site of the chart space*.  Combined with Stacks 03DX at an affine chart
this makes the pullback of a quasi-coherent module to an affine chart space globally presented.

## Main results

* `AlgebraicGeometry.Space.hasGlobalPresentation_etaleModulePullback_chartToSpace`: the pullback
  of an `𝒪_X`-module to the chart space of `W` has a global presentation as soon as `M|_W` has
  one on the slice at `W`.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_etaleModulePullback_chartToSpace_iff`: the same
  comparison for quasi-coherence.
* `AlgebraicGeometry.Space.hasGlobalPresentation_over_of_isAffine`: **Stacks 03DX for the small
  étale ringed site of an algebraic space, at the module universe of the structure rings.**
* `AlgebraicGeometry.Space.nonempty_presentation_modulePullback_chartToSpace_of_isAffine`: the
  pullback of a quasi-coherent `𝒪_X`-module along the structure morphism of an étale chart with
  affine underlying scheme admits a `SheafOfModules.Presentation`.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_coversTop_etaleModulePullback`: condition (4)
  of Stacks 03M0 for an arbitrary covering family of étale charts, read through the pullback.

## Implementation notes

The identification of the pullback with the restriction is *definitional*: the comparison
functor of Stacks 04M0 followed by the slice projection is postcomposition with the structure
morphism of the chart (`AlgebraicGeometry.Space.chartLocalization_comp_forget`), and no change
of scalars occurs on either leg, so
`AlgebraicGeometry.Space.chartSmallEtaleRestriction` and
`AlgebraicGeometry.Space.etaleModulePullback` along `AlgebraicGeometry.Space.chartToSpace` agree
on the nose.  Quasi-coherence therefore transports by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_chartSmallEtaleRestriction_iff` with nothing to
prove, while a global presentation is carried by
`Stacks.SheafOfModules.hasGlobalPresentation_map` along the comparison, exactly as in
`AlgebraicGeometry.Space.hasGlobalPresentation_over_postcomp_iff`.  The two functors are taken
at the module universe and one above it, the latter being where a global presentation lives;
the comparison between them is `Stacks.SheafOfModules.pushforwardUliftIso`.

The statement of Stacks 03DX recorded in
`AlgebraicGeometry.Space.HasAffineChartPresentations` has its module sections in
`max (u + 1) m`, the universe in which the construction of Stacks 04CK takes its direct sums,
whereas the modules of Stacks 03LU have theirs in the universe `u` of the structure rings.  The
two inputs of `AlgebraicGeometry.Space.hasAffineChartPresentations` are stated at an arbitrary
module universe, so the version needed here is the same two-line assembly at `u`.

The slices of the small étale site of a chart space are essentially small and have
sheafification, but instance search finds neither at the projections of
`AlgebraicGeometry.Space.smallEtaleRingedSite` of a
`AlgebraicGeometry.Space.chartSpace`: both spellings have to be unfolded by hand, as elsewhere
in this directory.

## References

* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- **Quasi-coherence of the pullback of an `𝒪_X`-module to a chart space.**  The pullback of
Stacks 03LU of an `𝒪_X`-module along the structure morphism of an étale scheme chart `W` is
quasi-coherent exactly when the restriction of the module to the slice at `W` is.

The pullback *is* that restriction read through the comparison equivalence of Stacks 04M0, so
this is `AlgebraicGeometry.Space.isQuasicoherentOnSite_chartSmallEtaleRestriction_iff`. -/
theorem isQuasicoherentOnSite_etaleModulePullback_chartToSpace_iff
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X)) (W : SmallEtale B S hS X.1) :
    ((etaleModulePullback B S hS (chartToSpace B S hS X W)
        (isEtale_chartToSpace B S hS X W)).obj M).IsQuasicoherentOnSite ↔
      (M.over W).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_chartSmallEtaleRestriction_iff B S hS X M W

/-- **A global presentation on the slice at a chart is a global presentation on the chart
space.**  If an `𝒪_X`-module `M` restricted to the slice of the small étale site at an étale
scheme chart `W` has a global presentation, then its pullback of Stacks 03LU along the structure
morphism of `W` has a global presentation on the whole small étale site of the chart space.

The pullback is the restriction to the slice read through the comparison equivalence of
Stacks 04M0, along which a global presentation is carried by
`Stacks.SheafOfModules.hasGlobalPresentation_map`. -/
theorem hasGlobalPresentation_etaleModulePullback_chartToSpace
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X)) (W : SmallEtale B S hS X.1)
    (h : (M.over W).HasGlobalPresentation) :
    ((etaleModulePullback B S hS (chartToSpace B S hS X W)
      (isEtale_chartToSpace B S hS X W)).obj M).HasGlobalPresentation := by
  let E : SmallEtale B S hS (chartSpace B S hS X W).1 ≌ Over W :=
    SmallEtale.chartLocalizationEquivalence B S hS X.1 W
  have hc1 : E.functor.IsContinuous
      (SmallEtale.topology B S hS (chartSpace B S hS X W).1)
      ((SmallEtale.topology B S hS X.1).over W) :=
    isContinuous_chartLocalization_chartSpace B S hS X W
  have hc2 : E.inverse.IsContinuous
      ((SmallEtale.topology B S hS X.1).over W)
      (SmallEtale.topology B S hS (chartSpace B S hS X W).1) :=
    isContinuous_chartLocalizationInverse_chartSpace B S hS X W
  let RX := structureRingSheaf B S hS X
  let RW := structureRingSheaf B S hS (chartSpace B S hS X W)
  let φ : RW ⟶ (E.functor.sheafPushforwardContinuous RingCat.{u}
      (SmallEtale.topology B S hS (chartSpace B S hS X W).1)
      ((SmallEtale.topology B S hS X.1).over W)).obj (RX.over W) := 𝟙 _
  let ψ : RX.over W ⟶ (E.inverse.sheafPushforwardContinuous RingCat.{u}
      ((SmallEtale.topology B S hS X.1).over W)
      (SmallEtale.topology B S hS (chartSpace B S hS X W).1)).obj RW := 𝟙 _
  have H₁ : Functor.whiskerRight (NatTrans.op E.counit) (RX.over W).obj =
      ψ.hom ≫ E.inverse.op.whiskerLeft φ.hom := by
    ext : 2
    exact rfl
  have H₂ : φ.hom ≫ E.functor.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op E.unit) RW.obj = 𝟙 RW.obj := by
    ext : 2
    exact rfl
  let eHi := SheafOfModules.pushforwardPushforwardEquivalence.{u + 1} E φ ψ H₁ H₂
  let F₀ := SheafOfModules.pushforward.{u} φ
  let F := SheafOfModules.pushforward.{u + 1} φ
  have hFadj : F.IsLeftAdjoint := eHi.isLeftAdjoint_functor
  have hFzero : F.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have step : (F₀.obj (M.over W)).HasGlobalPresentation :=
    Stacks.SheafOfModules.hasGlobalPresentation_map (F₀ := F₀) (F := F) _
      (Stacks.SheafOfModules.pushforwardUliftIso.{u + 1, u, u, u, u + 1} φ
        (SheafOfModules.unit (RX.over W)))
      (Stacks.SheafOfModules.pushforwardUliftIso.{u + 1, u, u, u, u + 1} φ (M.over W)) h
  have key : F₀.obj (M.over W) ≅
      (etaleModulePullback B S hS (chartToSpace B S hS X W)
        (isEtale_chartToSpace B S hS X W)).obj M :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun _ => Iso.refl _) (fun _ _ _ => by ext x; rfl))
  exact SheafOfModules.HasGlobalPresentation.of_iso key step

/-- **Stacks 03DX for the small étale ringed site of an algebraic space**, at the module universe
of the structure rings: a quasi-coherent `𝒪_X`-module has a global presentation after
restriction to an étale chart whose underlying scheme is affine.

This is `AlgebraicGeometry.Space.hasAffineChartPresentations` with the module sections in the
universe `u` of the structure rings rather than in `max (u + 1) m`; both of its inputs are
stated at an arbitrary module universe. -/
theorem hasGlobalPresentation_over_of_isAffine (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (W : (smallEtaleRingedSite B S hS X.1 X.2).C)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj W))) :
    (M.over W).HasGlobalPresentation := by
  obtain ⟨_, _, g, hcov, hbc⟩ :=
    SmallEtale.exists_hasSectionBaseChangeOn_of_isQuasicoherentOnSite B S hS X.1 X.2 M hM W hW
  exact SmallEtale.hasGlobalPresentation_of_hasSectionBaseChangeOn B S hS X.1 X.2
    (M.over W) hW g hcov hbc

/-- **The pullback of a quasi-coherent module to an affine chart space is globally presented.**
If `W` is an étale scheme chart of `X` whose underlying scheme is affine and `M` is a
quasi-coherent `𝒪_X`-module, then the pullback of Stacks 03LU of `M` along the structure
morphism of `W` admits a `SheafOfModules.Presentation`.

Stacks 03DX presents `M|_W` on the slice at `W`; the comparison of Stacks 04M0 carries that to a
global presentation on the chart space, and the small étale site of the chart space is
essentially small in the module universe, which is what turns a
`SheafOfModules.HasGlobalPresentation` back into a `SheafOfModules.Presentation`. -/
theorem nonempty_presentation_modulePullback_chartToSpace_of_isAffine
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (W : SmallEtale B S hS X.1)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj W))) :
    Nonempty ((modulePullback B S hS (chartToSpace B S hS X W)).obj M).Presentation := by
  have hws : HasWeakSheafify
      (smallEtaleRingedSite B S hS (chartSpace B S hS X W).1
        (chartSpace B S hS X W).2).J AddCommGrpCat.{u} := by
    show HasWeakSheafify (SmallEtale.topology B S hS (chartSpace B S hS X W).1)
      AddCommGrpCat.{u}
    infer_instance
  have hwl : (smallEtaleRingedSite B S hS (chartSpace B S hS X W).1
      (chartSpace B S hS X W).2).J.WEqualsLocallyBijective AddCommGrpCat.{u} := by
    show (SmallEtale.topology B S hS (chartSpace B S hS X W).1).WEqualsLocallyBijective
      AddCommGrpCat.{u}
    infer_instance
  have hes : EssentiallySmall.{u}
      (smallEtaleRingedSite B S hS (chartSpace B S hS X W).1 (chartSpace B S hS X W).2).C := by
    show EssentiallySmall.{u} (SmallEtale B S hS (chartSpace B S hS X W).1)
    infer_instance
  obtain ⟨P⟩ := Stacks.SheafOfModules.nonempty_presentation_of_hasGlobalPresentation
    (hasGlobalPresentation_etaleModulePullback_chartToSpace B S hS X M W
      (hasGlobalPresentation_over_of_isAffine B S hS X M hM W hW))
  exact ⟨SheafOfModules.Presentation.ofIsIso
    ((modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X W)
      (isEtale_chartToSpace B S hS X W)).app M).inv P⟩

/-- **Quasi-coherence is detected on any covering family of étale charts.**  If a family of
étale scheme charts of `X` covers the final object of the small étale site and the pullback of
Stacks 03LU of an `𝒪_X`-module along the structure morphism of each member is quasi-coherent,
then the module is quasi-coherent.

This is condition (4) of Stacks 03M0 with the affine charts replaced by an arbitrary covering
family, read through the pullback rather than through restriction to a slice; the passage
between the two readings is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_etaleModulePullback_chartToSpace_iff`. -/
theorem isQuasicoherentOnSite_of_coversTop_etaleModulePullback {I : Type (u + 1)}
    (W : I → SmallEtale B S hS X.1)
    (hcov : (SmallEtale.topology B S hS X.1).CoversTop W)
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (h : ∀ i, ((etaleModulePullback B S hS (chartToSpace B S hS X (W i))
      (isEtale_chartToSpace B S hS X (W i))).obj M).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite :=
  (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite M).2
    ⟨I, W, hcov, fun i =>
      (isQuasicoherentOnSite_etaleModulePullback_chartToSpace_iff B S hS X M (W i)).1 (h i)⟩

end AlgebraicGeometry.Space

end
