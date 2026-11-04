module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartsBoundedRelocalize
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescentSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartStandardPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineStageDescentLastStep
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentSituationRebase
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentToLimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentToLimitSituationSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.PresentationSpecProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SeparatedRelationSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SeparatedRelationSystemSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitsSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.SpecGlobalFunctionsContained
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveAffineSpectrum

/-!
# Stacks 07SQ: an affine limit has an affine stage

Let `X = lim X_i` be the limit of a directed inverse system of quasi-compact and quasi-separated
algebraic spaces over a scheme `S` with affine transition morphisms, the situation of Stacks 084R,
whose charts are bounded in the sense of `AlgebraicGeometry.Space.ChartsBounded` — the index type
and its slices smaller than the size cutoff of the ambient big fppf site, and for each stage and
each affine scheme-valued point of it one cardinal below the cutoff bounding every object of the
site representing a base change of that point along a transition morphism into the stage. If `X` is
an affine algebraic space then so is `X_i` for some `i` beyond the distinguished index.

This proves `AlgebraicGeometry.Space.HasAffineStageDescent`.

## Main results

* `DescentSituation.exists_isAffineSpace_system_obj_of_isTerminal_of_chartsBounded`: Stacks 07SQ
  over a terminal base scheme.
* `hasAffineStageDescent_of_chartsBounded`: Stacks 07SQ over an arbitrary base.

All of these are in the namespace `AlgebraicGeometry.Space`.

## References

* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
* [Stacks Project, Tag 084S](https://stacks.math.columbia.edu/tag/084S)
* [Stacks Project, Tag 084T](https://stacks.math.columbia.edu/tag/084T)
* [Stacks Project, Tag 084U](https://stacks.math.columbia.edu/tag/084U)
* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Tag 01Z0](https://stacks.math.columbia.edu/tag/01Z0)
* [Stacks Project, Tag 00U9](https://stacks.math.columbia.edu/tag/00U9)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Stacks 07SQ over a terminal base scheme.** In the situation of Stacks 084R over a terminal
base, with the charts of the system bounded in the sense of
`AlgebraicGeometry.Space.ChartsBounded`, if the limit of the inverse system is an affine
algebraic space then so is some stage beyond the distinguished one. -/
theorem DescentSituation.exists_isAffineSpace_system_obj_of_isTerminal_of_chartsBounded
    (hterminal : IsTerminal S) {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : DescentSituation B S hS hZ I) (hI : ChartsBounded B S hS D.system)
    (hX : IsAffineSpace B S hS D.limitCone.pt) :
    ∃ i, D.base ≤ i ∧ IsAffineSpace B S hS (D.system.obj (op i)) := by
  have hSaff : IsAffine S :=
    IsAffine.of_isIso (hterminal.uniqueUpToIso terminalIsTerminal).hom
  have hXc : IsAffineSpace B S hS D.atCanonicalLimit.limitCone.pt :=
    hX.of_iso (D.isLimit.conePointUniqueUpToIso (limit.isLimit D.system))
  obtain ⟨i₁, hbi₁, hsep₁⟩ :=
    DescentSituation.exists_isAbsolutelySeparated_system_obj_of_isAffine_of_chartsBounded
      B S hS hZ hSaff D.atCanonicalLimit hI
      (isAbsolutelySeparated_of_isAffineSpace B S hS hZ hXc)
  set A := (D.atCanonicalLimit.rebase i₁).toLimitSituation with hA
  have hIA : A.ChartsBounded := hI
  have hXalg : IsAlgebraicSpace B S hS A.cone.pt :=
    (D.atCanonicalLimit.rebase i₁).limitAlgebraicSpace
  obtain ⟨U₀, f₀, hf₀, hsurjf₀⟩ := A.exists_affine_isSurjective_etaleChart_stage B S hS A.base
  obtain ⟨R₀, tt, ss, hpbR⟩ :=
    A.exists_affine_relationChart_of_isAbsolutelySeparated hsep₁ U₀ f₀
  set C := A.chartSystem U₀ f₀ with hC
  set L := A.chartLimitBridgeOfChartsBounded U₀ f₀ hIA with hL
  set Vlim := A.limitEtaleChart C L hf₀ with hVlim
  have hWaff : IsAffine ((BigFppfOver.toScheme B S hS).obj L.cone.pt) :=
    AffineChartSystem.LimitBridge.isAffine_pt L
  have hVetale : IsEtale B S hS Vlim.1.hom :=
    (isEtale_iff_presheaf_of_yoneda B S hS Vlim.1.hom).2 Vlim.2
  have hVsurj : IsSurjective B S hS Vlim.1.hom :=
    A.isSurjective_limitEtaleChart C L hf₀ hsurjf₀
  have hcsurj := presheafSurjective_of_isSurjective B S hS Vlim.1.hom
    (hXalg.diagonal_representable.of_diag Vlim.1.hom) hVsurj
  obtain ⟨T, hT, ⟨eT⟩⟩ := hXc
  set φ : L.cone.pt ⟶ T := yoneda.preimage (Vlim.1.hom ≫ eT.hom) with hφ
  have hφmap : yoneda.map φ = Vlim.1.hom ≫ eT.hom := Functor.map_preimage _ _
  have hφetale : IsEtale B S hS (yoneda.map φ) := by
    rw [hφmap]
    exact isEtale_comp B S hS hVetale (isEtale_of_isIso B S hS eT.hom)
  obtain ⟨n, gl, hl, hrell, hΔ, hbij⟩ :=
    exists_coordinateHom_bijective_of_isEtale B S hS hWaff hT φ hφetale
  have hsurjSpec : Function.Surjective (PrimeSpectrum.comap
      ((BigFppfOver.toScheme B S hS).map φ).appTop.hom) :=
    surjective_primeSpectrum_comap_appTop_of_isSurjective_of_iso B S hS hWaff hT
      Vlim.1.hom eT hVsurj
  set eA := (globalFunctionsAffineEquiv B S hS (A.limitSpace hXalg) T eT).symm with heA
  have hψl : (globalFunctionsChartRestriction B S hS (A.limitSpace hXalg) Vlim).comp
      eA.toRingHom = ((BigFppfOver.toScheme B S hS).map φ).appTop.hom :=
    RingHom.ext fun s => globalFunctionsChartRestriction_globalFunctionsAffineEquiv_symm
      B S hS (A.limitSpace hXalg) T eT Vlim s
  obtain ⟨j, hij, g, hh, hrelj, hgmap, hhmap, hΔj, hsurjSpecj⟩ :=
    A.exists_ge_chartPresentationStageDescent hf₀ hsurjf₀ hpbR hXalg hIA eA gl hl
      (fun l => by rw [hψl]; exact hrell l) hΔ (by rw [hψl]; exact hsurjSpec)
      ⟨A.base, le_refl _⟩
  set Vj := A.stagesEtaleChart C hf₀ j with hVj
  have hVjsurj : IsSurjective B S hS Vj.1.hom :=
    A.isSurjective_stagesEtaleChart C hf₀ hsurjf₀ j
  obtain ⟨pj, hpj⟩ := exists_specMap_of_globalHom B S hS (A.stage j.1) (A.stageModel j)
    (A.stageModelEquiv j).toRingHom
  have hUjaff : IsAffine ((BigFppfOver.toScheme B S hS).obj Vj.1.left) := C.isAffine_obj _
  have ha : IsEtale B S hS Vj.1.hom :=
    (isEtale_iff_presheaf_of_yoneda B S hS Vj.1.hom).2 Vj.2
  have hcommSq := commSq_chart_specOfGlobalFunctions B S hS (A.stage j.1) Vj
    (A.stageModel j) (A.stageModelEquiv j) g hh hrelj pj (hpj Vj)
  have hcA : B.Contains (Spec (CommRingCat.of (A.stageModel j))) :=
    contains_spec_of_globalFunctionsEquiv B S hS (A.stage j.1) Vj hVjsurj _
      (A.stageModelEquiv j)
  have hcB : B.Contains (Spec (CommRingCat.of (presentationAlgebra g))) :=
    contains_spec_presentationAlgebra B S hS (A.stage j.1) Vj hVjsurj _
      (A.stageModelEquiv j) g
  have hstage := A.isPullback_limitChartToSpace_stage C L hf₀ j
  have hmp := A.comp_modelProjection_eq_of_eq hf₀ hsurjf₀ hpbR hXalg hIA eA hψl j
  have hgl : (fun k => MvPolynomial.map (A.modelProjection hXalg eA j) (g k)) = gl :=
    funext hgmap
  subst hgl
  obtain ⟨k, hk, hkaff⟩ :=
    (D.atCanonicalLimit.rebase j.1).exists_isAffineSpace_system_obj_of_presentation_of_chartsBounded
      hterminal hI g hUjaff ha
      (Over.homMk (pullback.lift Vj.1.hom _ hcommSq) (pullback.lift_fst _ _ _))
      (pullback.lift_snd _ _ _) hWaff hstage Vlim.2 hcsurj hT eT
      (A.modelProjection hXalg eA j) hψl.symm (fun k => (hhmap k).symm) hmp hbij
      hcA hcB inferInstance (flat_Spec_map_presentationStructureHom g hΔj)
      (surjective_Spec_map_presentationStructureHom g hsurjSpecj)
  refine ⟨k, le_trans hbi₁ (le_trans ?_ hk), hkaff⟩
  exact hij

/-- In the situation of Stacks 084R, if the limit `X` of the inverse system is an affine algebraic
space then `X_i` is an affine algebraic space for some `i` beyond the distinguished index, the
charts of the system being bounded in the sense of `AlgebraicGeometry.Space.ChartsBounded`.

The size restriction cannot be dropped: `Stacks.Refute07SQ.not_statement07SQ` exhibits a descent
situation over an index as large as the cutoff whose limit is the empty algebraic space, which is
affine, and none of whose stages is affine. -/
@[stacks 07SQ]
theorem hasAffineStageDescent_of_chartsBounded : HasAffineStageDescent B S hS hZ := by
  intro J _ _ E hJ hX
  obtain ⟨i, hi, hres⟩ :=
    DescentSituation.exists_isAffineSpace_system_obj_of_isTerminal_of_chartsBounded B
      (⊤_ Scheme.{u}) hZ hZ terminalIsTerminal (E.viewOverIntegers B S hS hZ)
      (hJ.viewOverIntegers hZ)
      ((isAffineSpace_viewOverIntegers_iff B S hS hZ (F := E.limitCone.pt)).2 hX)
  exact ⟨i, hi, (isAffineSpace_viewOverIntegers_iff B S hS hZ (F := (E.system.obj (op i)))).1 hres⟩

end AlgebraicGeometry.Space

end
