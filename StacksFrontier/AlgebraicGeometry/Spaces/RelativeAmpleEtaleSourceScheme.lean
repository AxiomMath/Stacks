module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.AlgebraicGeometry.AmpleAffineAvoidance.AmpleFiniteSet
public import StacksFrontier.AlgebraicGeometry.AmpleFiniteAvoidance.FromAmple
public import StacksFrontier.AlgebraicGeometry.AmpleTheory.Basic
public import StacksFrontier.AlgebraicGeometry.HProjective.AffineBase
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseChangeModuleInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionTensorPowers
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardChartNonvanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleEtaleDescentRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleEtaleSourceQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.StableQuasiAffineCoverRepresentable

/-!
# Relative ampleness and surjective étale base change of an affine base

Let `V ⟶ U` be a surjective étale morphism of affine schemes, let `X` be an algebraic space
over `U`, let `L` be an invertible `𝒪_X`-module, let `Y = V ×_U X` and let `N` be the pullback of
`L` to `Y`. [Stacks, Tag 0D35] says that `L` is ample on `X/U` if and only if `N` is ample on
`Y/V`. This file proves it at exactly those hypotheses.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_of_isRelativelyAmple_baseChange_etale`: if `N` is
  ample on `Y/V` then `X` is a scheme.
* `AlgebraicGeometry.Space.isRelativelyAmple_of_isRelativelyAmple_baseChange_etale`:
  **Stacks 0D35, (2) implies (1)**.
* `AlgebraicGeometry.Space.isRelativelyAmple_iff_isRelativelyAmple_baseChange_etale`:
  **Stacks 0D35**, the equivalence.

## The proof

The implication (1) ⇒ (2) is [Stacks, Tag 0D33],
`AlgebraicGeometry.Space.isRelativelyAmple_baseChange`. Assume (2). Then `Y` is a scheme `Y₀`
and `N` is ample on `Y₀`, `V` being affine; `X ⟶ U` is quasi-compact and separated
(`AlgebraicGeometry.Space.isQuasiCompact_of_isRelativelyAmple_baseChange_etale`), so the direct
images `f_* L^{⊗ k}` are quasi-coherent ([Stacks, Tag 03M9]). The source then shows that the
relative `Proj` of `⨁ f_* L^{⊗ k}` receives an open immersion from `X`, so that `X` is a scheme.
Here the conclusion that `X` is a scheme is reached directly, through the same sections:

* a section `s` of `L^{⊗ k}` on `X` — a section of `f_* L^{⊗ k}` over `U` — has a nonvanishing
  locus `T_s` on the chart `Y₀ ⟶ X`, which is the nonvanishing locus of the corresponding
  section of `N^{⊗ k}` (`AlgebraicGeometry.Space.chartRestrictionSchemeModuleNatTensorPowIso`),
  hence quasi-affine, `N` being ample (`Stacks.AmpleAffineAvoidance.isQuasiAffine_nvOpen`);
* `T_s` is stable for the relation `Y₀ ×_X Y₀ ⇉ Y₀`, because `s` comes from `X` and the
  nonvanishing locus is read on geometric stalks
  (`AlgebraicGeometry.Space.mem_nonvanishingLocus_chartRestrictionTopSection_map_iff`);
* the `T_s` cover `Y₀`: the sections of `N^{⊗ k}` over `Y₀ = V ×_U X` are the base change of the
  sections of `f_* L^{⊗ k}` over `U` (`f_* L^{⊗ k}` is quasi-coherent, hence cartesian on affine
  charts), and `N` is ample
  (`AlgebraicGeometry.Space.nonvanishingLocus_subset_iUnion_modulePushforwardCounitApp`).

So `X` is a scheme by `AlgebraicGeometry.Space.isRepresentable_of_forall_mem_stable_isQuasiAffine`,
and then ampleness descends along `V ⟶ U`
(`AlgebraicGeometry.Space.isRelativelyAmple_of_baseChange_etale_of_isRepresentable`).

## References

* [Stacks Project, Tag 0D35](https://stacks.math.columbia.edu/tag/0D35)
* [Stacks Project, Tag 0D33](https://stacks.math.columbia.edu/tag/0D33)
* [Stacks Project, Tag 0D34](https://stacks.math.columbia.edu/tag/0D34)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 01VJ](https://stacks.math.columbia.edu/tag/01VJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U V X Y : AlgebraicSpaces B S hS} {f : X ⟶ U} {g : V ⟶ U} {f' : Y ⟶ V} {pr : Y ⟶ X}

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the big fppf site is slow
/-- Discrete limits of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete_presheaf_RelativeAmpleEtaleSourceScheme
    (J : Type) : HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site is slow
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_RelativeAmpleEtaleSourceScheme :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_RelativeAmpleEtaleSourceScheme
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **If the pullback of an invertible module along a surjective étale base change of an affine
base is relatively ample, the source is a scheme.** This is the part of the proof of
[Stacks, Tag 0D35] that the source concludes with "Thus `X` is a scheme"; see the module
documentation. -/
theorem isRepresentable_of_isRelativelyAmple_baseChange_etale (hsq : IsPullback pr f' f g)
    (L : Modules.{u, u} B S hS X.1 X.2)
    (hLinv : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L)
    (U₀ V₀ : BigFppfOver B S hS) (hU₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀))
    (hV₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj V₀))
    (eU : U.1 ≅ yoneda.obj U₀) (eV : V.1 ≅ yoneda.obj V₀)
    (h₀ : V₀ ⟶ U₀) (hg : g.hom ≫ eU.hom = eV.hom ≫ yoneda.map h₀)
    (hsurj : Surjective ((BigFppfOver.toScheme B S hS).map h₀))
    (hetale : Etale ((BigFppfOver.toScheme B S hS).map h₀))
    (hN : IsRelativelyAmple B S hS f' ((modulePullback B S hS pr).obj L)) :
    X.1.IsRepresentable := by
  classical
  obtain ⟨Y₀, eY, hNinv, hNamp⟩ := hN.exists_scheme V₀ eV
  have hfqc := isQuasiCompact_of_isRelativelyAmple_baseChange_etale hsq eU eV h₀ hg hsurj hetale hN
  have hfqs :=
    isQuasiSeparated_of_isRelativelyAmple_baseChange_etale hsq eU eV h₀ hg hsurj hetale hN
  have hetP := isMultiplicative_presheaf_etale B S hS
  have hetBC : MorphismProperty.IsStableUnderBaseChange (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) :=
    MorphismProperty.relative_isStableUnderBaseChange _
  /- The chart `Y₀ ⟶ X` and its cartesian square. -/
  set gX : yoneda.obj Y₀ ⟶ X.1 := eY.hom ≫ pr.hom
  set ρ : yoneda.obj Y₀ ⟶ yoneda.obj V₀ := eY.hom ≫ f'.hom ≫ eV.hom
  set q₀ : Y₀ ⟶ V₀ := yoneda.preimage ρ
  have hmq₀ : yoneda.map q₀ = ρ := Functor.map_preimage _ _
  have sqc : IsPullback gX (yoneda.map q₀) f.hom (yoneda.map h₀ ≫ eU.inv) := by
    rw [hmq₀]
    exact (isPullback_chart_of_baseChange_etale hsq eU eV h₀ hg).of_iso eY.symm (Iso.refl _)
      (Iso.refl _) (Iso.refl _) (by simp [gX]) (by simp [ρ]) (by simp) (by simp)
  have sqg : IsPullback gX ρ (f.hom ≫ eU.hom) (yoneda.map h₀) :=
    (hmq₀ ▸ sqc).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eU (by simp) (by simp) (by simp)
      (by simp)
  have hgE : IsEtaleChart B S hS X.1 (CostructuredArrow.mk gX) :=
    MorphismProperty.of_isPullback sqg.flip
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ h₀).2 hetale)
  set cX : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk gX, hgE⟩
  /- The relation `Y₀ ×_X Y₀ ⇉ Y₀`. -/
  have hgrep : yoneda.relativelyRepresentable gX :=
    MorphismProperty.of_isPullback sqg.flip (Functor.relativelyRepresentable.map yoneda h₀)
  set D := hgrep.pullback gX
  set π₁ : D ⟶ Y₀ := hgrep.snd gX
  set π₂ : D ⟶ Y₀ := hgrep.fst' gX
  have sqD : IsPullback (yoneda.map π₁) (yoneda.map π₂) gX gX := (hgrep.isPullback' gX).flip
  have hπ₁ : QuasiCompact ((BigFppfOver.toScheme B S hS).map π₁) := by
    have hp := (hgrep.isPullback' gX).paste_horiz sqg.flip
    have hrep : yoneda.map (π₂ ≫ q₀) = yoneda.map (hgrep.fst' gX) ≫ ρ := by
      rw [Functor.map_comp, hmq₀]
    rw [← hrep, ← yoneda.map_preimage (gX ≫ f.hom ≫ eU.hom)] at hp
    have hp' := IsPullback.of_map yoneda (yoneda.map_injective (by simpa using hp.w)) hp
    have := hU₀
    have := hV₀
    exact MorphismProperty.of_isPullback (P := @QuasiCompact)
      (hp'.map (BigFppfOver.toScheme B S hS)) inferInstance
  /- The charts of `U` and the cartesian chart diagram `Y₀ ⟶ V₀`. -/
  let cU : SmallEtale B S hS U.1 :=
    ⟨CostructuredArrow.mk eU.inv, presheaf_etale_of_isEtale B S hS (isEtale_of_isIso B S hS eU.inv)⟩
  let cV : SmallEtale B S hS U.1 :=
    ⟨CostructuredArrow.mk (yoneda.map h₀ ≫ eU.inv),
      presheaf_etale_chart_of_baseChange_etale eU h₀ hetale⟩
  let j : cV ⟶ cU := ObjectProperty.homMk (CostructuredArrow.homMk h₀ rfl)
  have hbq : cX.1.hom ≫ f.hom = yoneda.map q₀ ≫ cV.1.hom := sqc.w
  have hcart : IsPullback cX.1.hom (yoneda.map q₀) f.hom cV.1.hom := sqc
  /- The tensor powers of `L` and their direct images. -/
  have hLqc : L.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_of_isInvertible B S hS X L (hLinv.toAlgebraicGeometry _ _ _)
  let P : ℕ → Modules.{u, u} B S hS X.1 X.2 := fun k => Stacks.TensorPowers.natTensorPow L k
  have hPqc : ∀ k, (P k).IsQuasicoherentOnSite := isQuasicoherentOnSite_natTensorPow B S hS X L
  have hfP : ∀ k, ((modulePushforward B S hS f).obj (P k)).IsQuasicoherentOnSite := fun k =>
    isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS f hfqc hfqs (P k) (hPqc k)
  let bX : (SmallEtale.toOver B S hS X.1).obj cX ⟶ (SmallEtale.toOver B S hS U.1).obj cU :=
    q₀ ≫ (SmallEtale.toOver B S hS U.1).map j
  have hbX : cX.1.hom ≫ f.hom = yoneda.map bX ≫ cU.1.hom :=
    chartDiagram_comm_comp (W := cX) f j q₀ hbq
  let σ : ∀ k, ((modulePushforward B S hS f).obj (P k)).val.obj (op cU) → (P k).val.obj (op cX) :=
    fun k => modulePushforwardCounitApp B S hS f (P k) ⟨cX, cU, bX, hbX⟩
  /- The module `N` on `Y₀`: invertible and ample. -/
  set N₀ := chartRestrictionSchemeModule B S hS X L cX
  let eN : N₀ ≅ baseChangeModule B S hS ((modulePullback B S hS pr).obj L) Y₀ eY.hom :=
    restrictToChartIsoChartSpaceIdEtaleChart B S hS X cX L hLqc ≪≫
      baseChangeModuleCompIso B S hS pr L Y₀ eY.hom
  have : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj Y₀)
      (baseChangeModule B S hS ((modulePullback B S hS pr).obj L) Y₀ eY.hom) := hNinv
  have hN₀inv : Stacks.Ample.IsInvertibleModule (chartScheme cX) N₀ :=
    Stacks.SheafOfModules.isInvertible_of_iso _ _ eN.symm
  have hN₀amp : Stacks.Ample.IsAmple (chartScheme cX) N₀ := by
    have := hV₀
    refine Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine
      ((BigFppfOver.toScheme B S hS).map q₀) N₀ ?_
    exact (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ eN).mpr hNamp
  /- The nonvanishing loci of the sections of the powers of `L` on `X`. -/
  let eK : ∀ k : ℕ, chartRestrictionSchemeModule B S hS X (P k) cX ≅
      Stacks.Ample.tensorPowModule (chartScheme cX) N₀ (k : ℤ) := fun k =>
    have := hLqc
    chartRestrictionSchemeModuleNatTensorPowIso B S hS X cX L k
  let T : ∀ k : ℕ, ((modulePushforward B S hS f).obj (P k)).val.obj (op cU) →
      (chartScheme cX).Opens := fun k n =>
    Stacks.AmpleTheory.powNonvanishingOpen (chartScheme cX) N₀ k
      ((eK k).hom.app ⊤ (chartRestrictionTopSection B S hS X (P k) cX (σ k n)))
  have hT : ∀ k n, (T k n : Set (chartScheme cX)) = Stacks.Ample.nonvanishingLocus
      (chartRestrictionSchemeModule B S hS X (P k) cX)
      (chartRestrictionTopSection B S hS X (P k) cX (σ k n)) := fun k n =>
    (Stacks.AmpleTheory.coe_powNonvanishingOpen _ _ _ _).trans
      (Stacks.Ample.nonvanishingLocus_congr (eK k) _)
  -- quasi-affine
  have hTqa : ∀ k, 1 ≤ k → ∀ n, (T k n).toScheme.IsQuasiAffine := by
    intro k hk n
    obtain ⟨a, ha⟩ := Stacks.AmpleFiniteAvoidance.exists_powSections_nvLocus_eq N₀ k
      ((eK k).hom.app ⊤ (chartRestrictionTopSection B S hS X (P k) cX (σ k n)))
    have hTa : Stacks.AmpleFiniteAvoidance.nvOpen N₀ a = T k n :=
      Opens.ext (by rw [Stacks.AmpleFiniteAvoidance.coe_nvOpen, ha]; rfl)
    rw [← hTa]
    exact Stacks.AmpleAffineAvoidance.isQuasiAffine_nvOpen _ hN₀amp hk a
  -- stable
  have hπE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)))
      (yoneda.map π₁) :=
    MorphismProperty.of_isPullback sqD.flip hgE
  let cD : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk (yoneda.map π₁ ≫ gX), MorphismProperty.comp_mem _ _ _ hπE hgE⟩
  let h₁ : cD ⟶ cX := ObjectProperty.homMk (CostructuredArrow.homMk π₁ rfl)
  let h₂ : cD ⟶ cX := ObjectProperty.homMk (CostructuredArrow.homMk π₂ sqD.w.symm)
  have : Mono cU.1.hom :=
    (show Mono eU.inv from ⟨fun _ _ h => by simpa using h =≫ eU.hom⟩)
  have hbX' : gX ≫ f.hom = yoneda.map bX ≫ cU.1.hom := hbX
  have eπ : ∀ π : D ⟶ Y₀, yoneda.map (π ≫ bX) ≫ cU.1.hom = (yoneda.map π ≫ gX) ≫ f.hom :=
    fun π => by rw [Functor.map_comp, Category.assoc, Category.assoc, hbX']
  have hπb : π₂ ≫ bX = π₁ ≫ bX := by
    apply yoneda.map_injective
    rw [← cancel_mono cU.1.hom, eπ, eπ, sqD.w]
  have hcommD : cD.1.hom ≫ f.hom = yoneda.map (π₁ ≫ bX) ≫ cU.1.hom := (eπ π₁).symm
  have hsame : ∀ k n, (P k).val.map h₁.op (σ k n) = (P k).val.map h₂.op (σ k n) := by
    intro k n
    have e : ∀ (h : cD ⟶ cX), _ → (P k).val.map h.op (σ k n) = _ := fun h hh =>
      (modulePushforwardCounitApp_naturality B S hS f (P k) ⟨cX, cU, bX, hbX⟩
        ⟨cD, cU, π₁ ≫ bX, hcommD⟩ h (𝟙 cU) hh n).symm
    exact (e h₁ (by simp; rfl)).trans
      (e h₂ (by rw [CategoryTheory.Functor.map_id, Category.comp_id]; exact hπb)).symm
  have hTst : ∀ k n, (BigFppfOver.toScheme B S hS).map π₂ ''
      ((BigFppfOver.toScheme B S hS).map π₁ ⁻¹' (T k n : Set (chartScheme cX))) ⊆
        (T k n : Set (chartScheme cX)) := by
    intro k n
    have := hPqc k
    rintro _ ⟨x, hx, rfl⟩
    rw [Set.mem_preimage, hT] at hx
    rw [hT]
    have h1 := (mem_nonvanishingLocus_chartRestrictionTopSection_map_iff B S hS X (P k) h₁
      (σ k n) x).2 hx
    rw [hsame] at h1
    exact (mem_nonvanishingLocus_chartRestrictionTopSection_map_iff B S hS X (P k) h₂
      (σ k n) x).1 h1
  -- covering
  have hcov : ∀ y : chartScheme cX, ∃ k, 1 ≤ k ∧ ∃ n, y ∈ T k n := by
    intro y
    obtain ⟨k, hk, t, Uo, hUo, hyUo, -⟩ := hN₀amp.2 y
    have hyt : y ∈ Stacks.Ample.nonvanishingLocus _ t := hUo ▸ hyUo
    refine ⟨k, hk, ?_⟩
    have := hPqc k
    obtain ⟨p, hp⟩ := surjective_chartRestrictionTopSection B S hS X (P k) cX
      ((eK k).inv.app ⊤ t)
    have hy : y ∈ Stacks.Ample.nonvanishingLocus (chartRestrictionSchemeModule B S hS X (P k) cX)
        (chartRestrictionTopSection B S hS X (P k) cX p) := by
      rwa [hp, ← Iso.symm_hom, Stacks.Ample.nonvanishingLocus_congr (eK k).symm]
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1
      (nonvanishingLocus_subset_iUnion_modulePushforwardCounitApp f (P k) (hfP k) j hV₀ hU₀ cX q₀
        hbq hcart p hy)
    exact ⟨n, show y ∈ (T k n : Set _) by rwa [hT]⟩
  refine isRepresentable_of_forall_mem_stable_isQuasiAffine X.2 (f.hom ≫ eU.hom) h₀ hV₀ hsurj
    hetale sqg sqD hπ₁ fun y => ?_
  obtain ⟨k, hk, n, hy⟩ := hcov y
  exact ⟨T k n, hy, hTst k n, hTqa k hk n⟩

/-- **Stacks 0D35, (2) implies (1).** Let `g : V ⟶ U` be a morphism of algebraic spaces which
are the affine schemes `V₀` and `U₀`, induced by a surjective étale `h₀ : V₀ ⟶ U₀`, let
`f : X ⟶ U` be a morphism of algebraic spaces, let `L` be an invertible `𝒪_X`-module and let
`pr : Y ⟶ X`, `f' : Y ⟶ V` present `Y` as `V ×_U X`. If the pullback of `L` to `Y` is ample on
`Y/V`, then `L` is ample on `X/U`.

The source `X` is a scheme by
`AlgebraicGeometry.Space.isRepresentable_of_isRelativelyAmple_baseChange_etale`, and then
ampleness descends along `V₀ ⟶ U₀` by
`AlgebraicGeometry.Space.isRelativelyAmple_of_baseChange_etale_of_isRepresentable`. -/
@[stacks 0D35 "(2) implies (1)"]
theorem isRelativelyAmple_of_isRelativelyAmple_baseChange_etale (hsq : IsPullback pr f' f g)
    (L : Modules.{u, u} B S hS X.1 X.2)
    (hLinv : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L)
    (U₀ V₀ : BigFppfOver B S hS) (hU₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀))
    (hV₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj V₀))
    (eU : U.1 ≅ yoneda.obj U₀) (eV : V.1 ≅ yoneda.obj V₀)
    (h₀ : V₀ ⟶ U₀) (hg : g.hom ≫ eU.hom = eV.hom ≫ yoneda.map h₀)
    (hsurj : Surjective ((BigFppfOver.toScheme B S hS).map h₀))
    (hetale : Etale ((BigFppfOver.toScheme B S hS).map h₀))
    (hN : IsRelativelyAmple B S hS f' ((modulePullback B S hS pr).obj L)) :
    IsRelativelyAmple B S hS f L :=
  isRelativelyAmple_of_baseChange_etale_of_isRepresentable hsq L hLinv U₀ V₀ hU₀ hV₀ eU eV h₀ hg
    hsurj hetale
    (isRepresentable_of_isRelativelyAmple_baseChange_etale hsq L hLinv U₀ V₀ hU₀ hV₀ eU eV h₀ hg
      hsurj hetale hN) hN

/-- **Stacks 0D35.** Let `g : V ⟶ U` be a morphism of algebraic spaces which are the affine
schemes `V₀` and `U₀`, induced by a surjective étale morphism `h₀ : V₀ ⟶ U₀`, let `f : X ⟶ U` be
a morphism of algebraic spaces, let `L` be an invertible `𝒪_X`-module and let `pr : Y ⟶ X`,
`f' : Y ⟶ V` present `Y` as `V ×_U X`. The following are equivalent:

1. `L` is ample on `X/U`;
2. the pullback of `L` to `Y` is ample on `Y/V`.

Clause (1) implies clause (2) by [Stacks, Tag 0D33],
`AlgebraicGeometry.Space.isRelativelyAmple_baseChange`, and the converse is
`AlgebraicGeometry.Space.isRelativelyAmple_of_isRelativelyAmple_baseChange_etale`. -/
@[stacks 0D35]
theorem isRelativelyAmple_iff_isRelativelyAmple_baseChange_etale (hsq : IsPullback pr f' f g)
    (L : Modules.{u, u} B S hS X.1 X.2)
    (hLinv : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L)
    (U₀ V₀ : BigFppfOver B S hS) (hU₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀))
    (hV₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj V₀))
    (eU : U.1 ≅ yoneda.obj U₀) (eV : V.1 ≅ yoneda.obj V₀)
    (h₀ : V₀ ⟶ U₀) (hg : g.hom ≫ eU.hom = eV.hom ≫ yoneda.map h₀)
    (hsurj : Surjective ((BigFppfOver.toScheme B S hS).map h₀))
    (hetale : Etale ((BigFppfOver.toScheme B S hS).map h₀)) :
    IsRelativelyAmple B S hS f L ↔
      IsRelativelyAmple B S hS f' ((modulePullback B S hS pr).obj L) :=
  ⟨fun hL => isRelativelyAmple_baseChange hsq L hL,
    isRelativelyAmple_of_isRelativelyAmple_baseChange_etale hsq L hLinv U₀ V₀ hU₀ hV₀ eU eV h₀ hg
      hsurj hetale⟩

end AlgebraicGeometry.Space

end
