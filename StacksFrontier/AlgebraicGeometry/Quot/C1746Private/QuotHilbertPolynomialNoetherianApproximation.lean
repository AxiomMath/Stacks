/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.C1746Private.NoetherianApproximation.ProjectiveImmersionStageModel
public import StacksFrontier.AlgebraicGeometry.Quot.C1746Private.NoetherianApproximation.QuotSchemeSituationBaseChange
public import StacksFrontier.AlgebraicGeometry.Limits.AffineSiteNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFinitePresentationBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasiAffineClosedInFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeChartFiniteness
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteUniverses
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic

/-!
# `Quot^P` over an affine base: reduction to a Noetherian base

Let `W` be an affine scheme of the site, `q : U ⟶ W` of finite presentation, `i : U ⟶ ℙⁿ_W` an
immersion over `W` and `F` a quasi-coherent module of finite presentation on `h_U`. The paragraph
"Assume `B = Spec(Λ)`" of the proof of Stacks 0DPD reduces the representability of
`Quot^{P, i^*𝒪(1)}_{F/U/W}` by a scheme separated and of finite presentation over `W` to the
case of a Noetherian affine base, by Noetherian approximation: `W` is the limit of the spectra
`W_k` of its finitely generated subrings (Stacks 01ZA), `(U, i, F)` descends to some `W_k`
(Stacks 01ZM, 01ZC, 0GTB and 01ZR), and `Quot^P` commutes with the base change `W ⟶ W_k`
(Stacks 08IT).

## Main results

* `QuotSituation.isRepresentedSeparatedFinitePresentation_hilbertPolynomialQuot_of_noetherian`:
  the reduction above, from the Noetherian affine case.

## References

* [Stacks Project, Tag 0DPD](https://stacks.math.columbia.edu/tag/0DPD)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 0GTB](https://stacks.math.columbia.edu/tag/0GTB)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 08IT](https://stacks.math.columbia.edu/tag/08IT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space.QuotSituation

open ProjectiveQuot ProjectiveQuotOverSpace

variable {B : BigFppfSite.{u}}

local notation "ℤS" => B.contains_integerBase

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-- The Zariski module represented by a quasi-coherent module of finite presentation on `h_U` is
of finite presentation. -/
private theorem isFinitePresentation_representedZariskiModule (U : BigFppfOver B integerBase ℤS)
    (F : Modules.{u, u} B integerBase ℤS (schemeSpace U).1 (schemeSpace U).2)
    (hF : F.IsQuasicoherentOnSite) (hFfp : SheafOfModules.IsFinitePresentationOnSite F) :
    (representedZariskiModule B integerBase ℤS U F).IsFinitePresentation :=
  Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
    (restrictToChartSchemeIdEtaleChartIso B integerBase ℤS U F)
    ((isFinitePresentation_restrictToChartScheme_idEtaleChart_iff B integerBase ℤS U F hF).2
      (SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite' F hFfp))

/-- A quasi-coherent module `F` on `h_U` whose Zariski reading is the pullback `g^* N` of a
quasi-coherent module `N` on `U'` is the pullback along `g` of the module on `h_{U'}` associated
to `N`. -/
private def isoModulePullbackOfZariski {U U' : BigFppfOver B integerBase ℤS}
    (F : Modules.{u, u} B integerBase ℤS (schemeSpace U).1 (schemeSpace U).2)
    (hF : F.IsQuasicoherentOnSite) (g : (𝒯).obj U ⟶ (𝒯).obj U') (N : ((𝒯).obj U').Modules)
    (hN : N.IsQuasicoherent)
    (eN : representedZariskiModule B integerBase ℤS U F ≅ (Scheme.Modules.pullback g).obj N) :
    F ≅ (modulePullback B integerBase ℤS (schemeSpaceMap (CurveFamily.homOfScheme g))).obj
      ((associatedSpaceModule U').obj N) :=
  let gs : U ⟶ U' := CurveFamily.homOfScheme g
  let F' : Modules.{u, u} B integerBase ℤS (schemeSpace U').1 (schemeSpace U').2 :=
    (associatedSpaceModule U').obj N
  have hF' : F'.IsQuasicoherentOnSite :=
    ((representedQuasicoherentSchemeEquivalence B integerBase ℤS U').functor.obj
      ⟨N, hN⟩).property
  let e₁ : F ≅ (associatedSpaceModule U).obj (representedZariskiModule B integerBase ℤS U F) :=
    (associatedSpaceModuleReadingIso U F hF).symm
  let e₃ : (Scheme.Modules.pullback g).obj N ≅
      (Scheme.Modules.pullback g).obj (representedZariskiModule B integerBase ℤS U' F') :=
    (Scheme.Modules.pullback g).mapIso (@asIso _ _ _ _ ((zariskiAdjunction B U').unit.app N)
      (isIso_zariskiAdjunction_unit_app U' N hN))
  let e₄ : (Scheme.Modules.pullback g).obj (representedZariskiModule B integerBase ℤS U' F') ≅
      representedZariskiModule B integerBase ℤS U
        ((modulePullback B integerBase ℤS (representedSpaceMap B integerBase ℤS gs)).obj F') :=
    representedZariskiModulePullbackIso B integerBase ℤS gs
      (Functor.relativelyRepresentable.map yoneda gs) F' hF'
  let e₅ : (associatedSpaceModule U).obj (representedZariskiModule B integerBase ℤS U
        ((modulePullback B integerBase ℤS (representedSpaceMap B integerBase ℤS gs)).obj F')) ≅
      (modulePullback B integerBase ℤS (representedSpaceMap B integerBase ℤS gs)).obj F' :=
    associatedSpaceModuleReadingIso U _
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B integerBase ℤS
        (representedSpaceMap B integerBase ℤS gs) F' hF')
  e₁ ≪≫ (associatedSpaceModule U).mapIso (eN ≪≫ e₃ ≪≫ e₄) ≪≫ e₅

/-- **Descent of `Quot^P` from a Noetherian affine stage.** Let `w : W ⟶ W'` be a morphism to an
affine Noetherian scheme of the site, and suppose that `q : U ⟶ W`, the immersion `i : U ⟶ ℙⁿ_W`
and `F` are the base change along `w` of a scheme `X'` of finite presentation over `W'` with an
immersion `X' ⟶ ℙⁿ_{W'}` over `W'` and a module `N'` of finite presentation on `X'`. If `Quot^P`
is represented by a scheme separated and of finite presentation over every affine Noetherian
base, then `Quot^{P, i^*𝒪(1)}_{F/U/W}` is represented by a scheme separated and of finite
presentation over `W`. -/
private theorem isRepresentedSeparatedFinitePresentation_hilbertPolynomialQuot_of_stageModel
    (hN : ∀ (W U : BigFppfOver B integerBase ℤS) (n : ℕ) (q : U ⟶ W)
      (i : U ⟶ projectiveSite B n W),
      IsAffine ((𝒯).obj W) → _root_.AlgebraicGeometry.IsNoetherian ((𝒯).obj W) →
      _root_.AlgebraicGeometry.IsImmersion ((𝒯).map i) →
      i ≫ projectiveSiteStructure B n W = q →
      ∀ (hq : IsFinitePresentation B integerBase ℤS (schemeSpaceMap q).hom)
        (F : Modules.{u, u} B integerBase ℤS (schemeSpace U).1 (schemeSpace U).2)
        (hF : F.IsQuasicoherentOnSite),
      SheafOfModules.IsFiniteTypeOnSite F →
      ∀ (P : ℤ → ℤ) (p : Polynomial ℚ), (∀ m : ℤ, p.eval (m : ℚ) = (P m : ℚ)) →
        (schemeQuotSituation q hq F hF).IsRepresentedSeparatedFinitePresentation W (𝟙 _)
          ((schemeQuotSituation q hq F hF).hilbertPolynomialQuot (projectiveTwist i) P))
    {W U Wk : BigFppfOver B integerBase ℤS} {n : ℕ} {q : U ⟶ W} (i : U ⟶ projectiveSite B n W)
    (w : W ⟶ Wk) (hWk : IsAffine ((𝒯).obj Wk))
    (hWkn : _root_.AlgebraicGeometry.IsNoetherian ((𝒯).obj Wk))
    (hq : IsFinitePresentation B integerBase ℤS (schemeSpaceMap q).hom)
    {F : Modules.{u, u} B integerBase ℤS (schemeSpace U).1 (schemeSpace U).2}
    (hF : F.IsQuasicoherentOnSite) (P : ℤ → ℤ) (p : Polynomial ℚ)
    (hP : ∀ m : ℤ, p.eval (m : ℚ) = (P m : ℚ)) {Xk : Scheme.{u}} (fk : Xk ⟶ (𝒯).obj Wk)
    (g : (𝒯).obj U ⟶ Xk) (jk : Xk ⟶ projectiveSpaceOver n ((𝒯).obj Wk)) (Nk : Xk.Modules)
    (hfk : FinitePresentation fk) (hpb : IsPullback g ((𝒯).map q) fk ((𝒯).map w))
    (hjk : jk ≫ (projectiveSpaceOver n ((𝒯).obj Wk) ↘ (𝒯).obj Wk) = fk)
    (hgj : g ≫ jk = ((𝒯).map i : (𝒯).obj U ⟶ projectiveSpaceOver n ((𝒯).obj W)) ≫
      projectiveSpaceOverMap n ((𝒯).map w))
    (himm : _root_.AlgebraicGeometry.IsImmersion jk) (hNk : Nk.IsFinitePresentation)
    (eN : representedZariskiModule B integerBase ℤS U F ≅ (Scheme.Modules.pullback g).obj Nk) :
    (schemeQuotSituation q hq F hF).IsRepresentedSeparatedFinitePresentation W (𝟙 _)
      ((schemeQuotSituation q hq F hF).hilbertPolynomialQuot (projectiveTwist i) P) := by
  have : QuasiCompact fk := hfk.2.1
  have : LocallyOfFinitePresentation fk := hfk.1
  have hXk : B.Contains Xk :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact fk Wk.left.property
  let Uk : BigFppfOver B integerBase ℤS := CurveFamily.ofScheme Xk hXk
  let ik : Uk ⟶ projectiveSite B n Wk := CurveFamily.homOfScheme jk
  let qk : Uk ⟶ Wk := ik ≫ projectiveSiteStructure B n Wk
  have hqk : (𝒯).map qk = fk := by
    rw [Functor.map_comp]
    exact hjk
  have hqkfp : IsFinitePresentation B integerBase ℤS (schemeSpaceMap qk).hom :=
    isFinitePresentation_yoneda_map B integerBase ℤS qk (hqk ▸ hfk)
  have : _root_.AlgebraicGeometry.IsImmersion ((𝒯).map ik) := himm
  have hsep : _root_.AlgebraicGeometry.IsSeparated ((𝒯).map qk) := by
    change _root_.AlgebraicGeometry.IsSeparated
      (jk ≫ (projectiveSpaceOver n ((𝒯).obj Wk) ↘ (𝒯).obj Wk))
    have := isProper_projectiveSpaceOver n ((𝒯).obj Wk)
    have : _root_.AlgebraicGeometry.IsImmersion jk := himm
    infer_instance
  obtain ⟨hNkqc, hNkft⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isFinitePresentation
      Nk hNk
  let Fk : Modules.{u, u} B integerBase ℤS (schemeSpace Uk).1 (schemeSpace Uk).2 :=
    (associatedSpaceModule Uk).obj Nk
  have hFk : Fk.IsQuasicoherentOnSite :=
    ((representedQuasicoherentSchemeEquivalence B integerBase ℤS Uk).functor.obj
      ⟨Nk, hNkqc⟩).property
  have hFkft : SheafOfModules.IsFiniteTypeOnSite Fk :=
    isFiniteTypeOnSite_representedQuasicoherentSchemeEquivalence B integerBase ℤS Uk Nk hNkqc
      hNkft
  let gs : U ⟶ Uk := CurveFamily.homOfScheme g
  have hsq : IsPullback gs q qk w := by
    refine CurveFamily.isPullback_of_isPullback_toScheme_map ?_ ?_
    · refine (𝒯).map_injective ?_
      rw [(𝒯).map_comp gs qk, (𝒯).map_comp q w, hqk]
      exact hpb.w
    · rwa [hqk]
  have hgi : gs ≫ ik = i ≫ projectiveSiteMap B n w := by
    apply (𝒯).map_injective
    rw [Functor.map_comp, Functor.map_comp]
    exact hgj
  exact isRepresentedSeparatedFinitePresentation_of_isPullback hq hF i hqkfp hsep hFk ik w gs
    hsq hgi (isoModulePullbackOfZariski (U' := Uk) F hF g Nk hNkqc eN) P
    (hN Wk Uk n qk ik hWk hWkn himm rfl hqkfp Fk hFk hFkft P p hP)

/-- **Stacks 0DPD over an affine base, from a Noetherian affine base.** Let `W` be an affine
scheme of the site, `q : U ⟶ W` of finite presentation with an immersion `i : U ⟶ ℙⁿ_W` over
`W`, `F` a quasi-coherent module of finite presentation on `h_U` and `P` a numerical polynomial.
Suppose that over every affine Noetherian scheme of the site, for every immersion into a
projective space over it and every quasi-coherent module of finite type, `Quot^P` with respect
to the inverse image of `𝒪(1)` is represented by a scheme separated and of finite presentation
over the base. Then `Quot^{P, i^*𝒪(1)}_{F/U/W}` is represented by a scheme separated and of
finite presentation over `W`. -/
theorem isRepresentedSeparatedFinitePresentation_hilbertPolynomialQuot_of_noetherian
    (hN : ∀ (W U : BigFppfOver B integerBase ℤS) (n : ℕ) (q : U ⟶ W)
      (i : U ⟶ projectiveSite B n W),
      IsAffine ((𝒯).obj W) → _root_.AlgebraicGeometry.IsNoetherian ((𝒯).obj W) →
      _root_.AlgebraicGeometry.IsImmersion ((𝒯).map i) →
      i ≫ projectiveSiteStructure B n W = q →
      ∀ (hq : IsFinitePresentation B integerBase ℤS (schemeSpaceMap q).hom)
        (F : Modules.{u, u} B integerBase ℤS (schemeSpace U).1 (schemeSpace U).2)
        (hF : F.IsQuasicoherentOnSite),
      SheafOfModules.IsFiniteTypeOnSite F →
      ∀ (P : ℤ → ℤ) (p : Polynomial ℚ), (∀ m : ℤ, p.eval (m : ℚ) = (P m : ℚ)) →
        (schemeQuotSituation q hq F hF).IsRepresentedSeparatedFinitePresentation W (𝟙 _)
          ((schemeQuotSituation q hq F hF).hilbertPolynomialQuot (projectiveTwist i) P))
    (W U : BigFppfOver B integerBase ℤS) (n : ℕ) (q : U ⟶ W) (i : U ⟶ projectiveSite B n W)
    (hW : IsAffine ((𝒯).obj W)) (hi : _root_.AlgebraicGeometry.IsImmersion ((𝒯).map i))
    (hiq : i ≫ projectiveSiteStructure B n W = q)
    (hq : IsFinitePresentation B integerBase ℤS (schemeSpaceMap q).hom)
    (F : Modules.{u, u} B integerBase ℤS (schemeSpace U).1 (schemeSpace U).2)
    (hF : F.IsQuasicoherentOnSite) (hFfp : SheafOfModules.IsFinitePresentationOnSite F)
    (P : ℤ → ℤ) (p : Polynomial ℚ) (hP : ∀ m : ℤ, p.eval (m : ℚ) = (P m : ℚ)) :
    (schemeQuotSituation q hq F hF).IsRepresentedSeparatedFinitePresentation W (𝟙 _)
      ((schemeQuotSituation q hq F hF).hilbertPolynomialQuot (projectiveTwist i) P) := by
  have := hW
  -- the Noetherian approximation of `W`
  let Dg := affineSiteStageDiagram B ℤS W
  let D := Dg ⋙ BigAffineFppf.toScheme B integerBase ℤS
  let c := (BigAffineFppf.toScheme B integerBase ℤS).mapCone (affineSiteStageCone B ℤS W)
  have hc : IsLimit c := isLimit_affineSiteStageCone B ℤS W
  have hDa : ∀ k, IsAffine (D.obj k) := fun k =>
    BigAffineFppf.isAffine_toScheme_obj B integerBase ℤS (Dg.obj k)
  have : ∀ k, CompactSpace (D.obj k) := fun _ => inferInstance
  have : ∀ k, QuasiSeparatedSpace (D.obj k) := fun _ => inferInstance
  have : ∀ {k l} (e : k ⟶ l), _root_.AlgebraicGeometry.IsAffineHom (D.map e) :=
    fun _ => inferInstance
  -- the data over `W`, read in schemes
  let j : (𝒯).obj U ⟶ projectiveSpaceOver n c.pt := (𝒯).map i
  have hj : j ≫ (projectiveSpaceOver n c.pt ↘ c.pt) = (𝒯).map q := by
    rw [← hiq, Functor.map_comp]
    rfl
  have hfp : FinitePresentation ((𝒯).map q : (𝒯).obj U ⟶ c.pt) :=
    finitePresentation_of_isFinitePresentation_yoneda_map B integerBase ℤS q hq
  have : _root_.AlgebraicGeometry.IsImmersion j := hi
  let N := representedZariskiModule B integerBase ℤS U F
  have : N.IsFinitePresentation := isFinitePresentation_representedZariskiModule U F hF hFfp
  obtain ⟨k, Xk, fk, g, jk, Nk, hfk, hpb, hjk, hgj, himm, hNk, ⟨eN⟩⟩ :=
    exists_projectiveImmersionStageModel_of_isLimit D c ((𝒯).map q) n j hj hc hfp N
  exact isRepresentedSeparatedFinitePresentation_hilbertPolynomialQuot_of_stageModel hN i
    ((affineSiteStageCone B ℤS W).π.app k).hom (Dg.obj k).property
    (isNoetherian_affineSiteStageDiagram_obj B ℤS W k) hq hF P p hP fk g jk Nk hfk hpb hjk hgj
    himm hNk eN

end AlgebraicGeometry.Space.QuotSituation

end
