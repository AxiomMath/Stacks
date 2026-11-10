/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.C1746Private.QuotSchemeSituationRepresented
public import StacksFrontier.AlgebraicGeometry.Quot.C1746Private.QuotOpenSubspaceRepresented
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.AffineFramedRepresentability
public import StacksFrontier.AlgebraicGeometry.Spaces.C1746Private.OpenImmersionModuleExtension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImmersionImage
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFiniteReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasiAffineClosedInFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeLocalCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic

/-!
# `Quot^P` over a Noetherian affine scheme for an immersion into `ℙⁿ` (the core of Stacks 0DPD)

Let `W` be an affine Noetherian scheme of the site, `i : U ⟶ ℙⁿ_W` an immersion over `W`, `F` a
quasi-coherent module of finite type on `h_U` and `P` a numerical polynomial. Then
`Quot^{P, i^*𝒪(1)}_{F/U/W}` is represented by a scheme separated, of finite presentation (and
quasi-compact) over `W`.

This is the last paragraph of the proof of Stacks 0DPD: the immersion factors through an open
immersion `j : U ⟶ X'` into its scheme-theoretic image `X' ⊆ ℙⁿ_W` (Stacks 01RG); `F` extends to a
quasi-coherent module `G` of finite type on `X'` (Stacks 0G41); `Quot^{P}_{G/X'/W}` is represented
by a scheme `Z` proper over `W` (Stacks 0DPB over the affine `W`, transported along the closed
immersion `X' ⟶ ℙⁿ_W` by Stacks 0DP4), and `Quot^{P}_{F/U/W}` is an open subscheme `V ⊆ Z`
(Stacks 0DP3). As `Z` is proper over the Noetherian `W` it is Noetherian, so `V` is quasi-compact;
`V ⟶ W` is of finite type over a Noetherian base, hence of finite presentation.

## Main results

* `exists_finiteType_modulePullback_iso_of_isOpenImmersion`: Stacks 0G41 read on the algebraic
  spaces of schemes.
* `QuotSituation.isRepresentedSeparatedFinitePresentation_hilbertPolynomialQuot_of_isNoetherian`:
  the Noetherian core.

## References

* [Stacks Project, Tag 0DPD](https://stacks.math.columbia.edu/tag/0DPD)
* [Stacks Project, Tag 01RG](https://stacks.math.columbia.edu/tag/01RG)
* [Stacks Project, Tag 0G41](https://stacks.math.columbia.edu/tag/0G41)
* [Stacks Project, Tag 0DP3](https://stacks.math.columbia.edu/tag/0DP3)
* [Stacks Project, Tag 0DPB](https://stacks.math.columbia.edu/tag/0DPB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

open ProjectiveQuot ProjectiveQuotOverSpace QuotSituation

variable {B : BigFppfSite.{u}}

local notation "ℤS" => B.contains_integerBase

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-- **Stacks 0G41 on the algebraic spaces of schemes.** Let `j : U ⟶ X` be a morphism of the site
whose morphism of schemes is a quasi-compact open immersion into a quasi-compact and
quasi-separated scheme. A quasi-coherent module `F` of finite type on `h_U` is `j^*G` for a
quasi-coherent module `G` of finite type on `h_X`. The extension is made on the Zariski readings
(Stacks 03DX), where it is
`AlgebraicGeometry.exists_finiteType_pullback_iso_of_isOpenImmersion`. -/
theorem exists_finiteType_modulePullback_iso_of_isOpenImmersion
    {U X : BigFppfOver B integerBase ℤS} (j : U ⟶ X)
    [_root_.AlgebraicGeometry.IsOpenImmersion ((𝒯).map j)] [QuasiCompact ((𝒯).map j)]
    [CompactSpace ((𝒯).obj X)] [QuasiSeparatedSpace ((𝒯).obj X)]
    (F : Modules.{u, u} B integerBase ℤS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B integerBase ℤS U))
    (hF : F.IsQuasicoherentOnSite) (hFft : SheafOfModules.IsFiniteTypeOnSite F) :
    ∃ (G : Modules.{u, u} B integerBase ℤS (yoneda.obj X)
        (isAlgebraicSpace_yoneda B integerBase ℤS X))
      (_ : G.IsQuasicoherentOnSite) (_ : SheafOfModules.IsFiniteTypeOnSite G),
      Nonempty ((modulePullback B integerBase ℤS (representedSpaceMap B integerBase ℤS j)).obj G ≅
        F) := by
  let N : ((𝒯).obj U).Modules := restrictToChartScheme B integerBase ℤS (yoneda.obj U)
    (isAlgebraicSpace_yoneda B integerBase ℤS U) F (idEtaleChart B integerBase ℤS U)
  have : N.IsQuasicoherent :=
    isQuasicoherent_restrictToChartScheme B integerBase ℤS (schemeSpace U) F hF
      (idEtaleChart B integerBase ℤS U)
  have : N.IsFiniteType := Stacks.SheafOfModules.Intrinsic.isFiniteType_of_iso
    (restrictToChartIsoRestrictToChartScheme B integerBase ℤS (G := F)
      (U := idEtaleChart B integerBase ℤS U))
    (isFiniteType_restrictToChart B integerBase ℤS (schemeSpace U) F hF hFft
      (idEtaleChart B integerBase ℤS U))
  obtain ⟨G₀, hG₀qc, hG₀ft, ⟨e₀⟩⟩ :=
    _root_.AlgebraicGeometry.exists_finiteType_pullback_iso_of_isOpenImmersion ((𝒯).map j) N
  let G := (associatedSpaceModule X).obj G₀
  have hGqc : G.IsQuasicoherentOnSite :=
    ((representedQuasicoherentSchemeEquivalence B integerBase ℤS X).functor.obj
      ⟨G₀, hG₀qc⟩).property
  have hGft : SheafOfModules.IsFiniteTypeOnSite G :=
    isFiniteTypeOnSite_representedQuasicoherentSchemeEquivalence B integerBase ℤS X G₀ hG₀qc hG₀ft
  have hjG : ((modulePullback B integerBase ℤS (representedSpaceMap B integerBase ℤS j)).obj
      G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B integerBase ℤS
      (representedSpaceMap B integerBase ℤS j) G hGqc
  have := isIso_zariskiAdjunction_unit_app X G₀ hG₀qc
  refine ⟨G, hGqc, hGft, ⟨?_⟩⟩
  let e₁ : (modulePullback B integerBase ℤS (representedSpaceMap B integerBase ℤS j)).obj G ≅
      (associatedSpaceModule U).obj (representedZariskiModule B integerBase ℤS U
        ((modulePullback B integerBase ℤS (representedSpaceMap B integerBase ℤS j)).obj G)) :=
    (associatedSpaceModuleReadingIso U _ hjG).symm
  let e₂ : representedZariskiModule B integerBase ℤS U
        ((modulePullback B integerBase ℤS (representedSpaceMap B integerBase ℤS j)).obj G) ≅
      (Scheme.Modules.pullback ((𝒯).map j)).obj (representedZariskiModule B integerBase ℤS X G) :=
    (representedZariskiModulePullbackIso B integerBase ℤS j
      (Functor.relativelyRepresentable.map yoneda j) G hGqc).symm
  let e₃ : representedZariskiModule B integerBase ℤS X G ≅ G₀ :=
    (asIso ((zariskiAdjunction B X).unit.app G₀)).symm
  let e₄ : N ≅ representedZariskiModule B integerBase ℤS U F :=
    restrictToChartSchemeIdEtaleChartIso B integerBase ℤS U F
  exact e₁ ≪≫ (associatedSpaceModule U).mapIso
      (e₂ ≪≫ (Scheme.Modules.pullback ((𝒯).map j)).mapIso e₃ ≪≫ e₀ ≪≫ e₄) ≪≫
    associatedSpaceModuleReadingIso U F hF

/-- Pushing a quasi-coherent module of finite type forward along a closed immersion into
`ℙⁿ_W`, read in the product `ℙⁿ × W`, gives a module of finite type. -/
private theorem isFiniteTypeOnSite_modulePushforward_comp_projectiveSiteProductIso {n : ℕ}
    {W X : BigFppfOver B integerBase ℤS} (c : X ⟶ projectiveSite B n W)
    [_root_.AlgebraicGeometry.IsClosedImmersion ((𝒯).map c)]
    (G : Modules.{u, u} B integerBase ℤS (yoneda.obj X)
      (isAlgebraicSpace_yoneda B integerBase ℤS X))
    (hGqc : G.IsQuasicoherentOnSite) (hGft : SheafOfModules.IsFiniteTypeOnSite G) :
    SheafOfModules.IsFiniteTypeOnSite ((modulePushforward B integerBase ℤS
      (schemeSpaceMap c ≫ (projectiveSiteProductIso n W).hom)).obj G) :=
  Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_of_iso
    ((modulePushforwardCompIso B integerBase ℤS (schemeSpaceMap c)
      (projectiveSiteProductIso n W).hom).app G)
    (Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_of_iso
      ((modulePushforwardInvIsoModulePullback B integerBase ℤS
        (projectiveSiteProductIso n W).symm).app _).symm
      (isFiniteTypeOnSite_modulePullback B integerBase ℤS (projectiveSiteProductIso n W).inv _
        (isFiniteTypeOnSite_modulePushforward_representedSpaceMap c G hGqc hGft)))

namespace QuotSituation

/-- **The Noetherian core of Stacks 0DPD.** Let `W` be a scheme of the site which is affine and
Noetherian, `i : U ⟶ ℙⁿ_W` an immersion with `i` followed by the projection equal to `q`, `F` a
quasi-coherent module of finite type on `h_U` and `P` a numerical polynomial. Then
`Quot^{P, i^*𝒪(1)}_{F/U/W}` is represented by a scheme separated, locally of finite
presentation and quasi-compact over `W`. -/
theorem isRepresentedSeparatedFinitePresentation_hilbertPolynomialQuot_of_isNoetherian
    (W U : BigFppfOver B integerBase ℤS) (n : ℕ) (q : U ⟶ W) (i : U ⟶ projectiveSite B n W)
    (hW : IsAffine ((𝒯).obj W)) (hWn : _root_.AlgebraicGeometry.IsNoetherian ((𝒯).obj W))
    (hi : _root_.AlgebraicGeometry.IsImmersion ((𝒯).map i))
    (hiq : i ≫ projectiveSiteStructure B n W = q)
    (hq : IsFinitePresentation B integerBase ℤS (schemeSpaceMap q).hom)
    (F : Modules.{u, u} B integerBase ℤS (schemeSpace U).1 (schemeSpace U).2)
    (hF : F.IsQuasicoherentOnSite) (hFft : SheafOfModules.IsFiniteTypeOnSite F)
    (P : ℤ → ℤ) (p : Polynomial ℚ) (hP : ∀ m : ℤ, p.eval (m : ℚ) = (P m : ℚ)) :
    (schemeQuotSituation q hq F hF).IsRepresentedSeparatedFinitePresentation W (𝟙 _)
      ((schemeQuotSituation q hq F hF).hilbertPolynomialQuot (projectiveTwist i) P) := by
  -- the scheme-theoretic image `X'` of `U` in `ℙⁿ_W` (Stacks 01RG)
  let h : (𝒯).obj U ⟶ (𝒯).obj (projectiveSite B n W) := (𝒯).map i
  have : _root_.AlgebraicGeometry.IsImmersion h := hi
  have : _root_.AlgebraicGeometry.IsProper ((𝒯).map (projectiveSiteStructure B n W)) :=
    isProper_projectiveSpaceOver n _
  have : _root_.AlgebraicGeometry.IsNoetherian ((𝒯).obj (projectiveSite B n W)) :=
    isNoetherian_of_locallyOfFiniteType ((𝒯).map (projectiveSiteStructure B n W))
  have : TopologicalSpace.NoetherianSpace ((𝒯).obj U) := h.isEmbedding.isInducing.noetherianSpace
  have : _root_.AlgebraicGeometry.IsClosedImmersion h.imageι := inferInstance
  have : _root_.AlgebraicGeometry.LocallyOfFiniteType h.imageι := inferInstance
  have hX'mem : B.Contains h.image :=
    contains_of_locallyOfFiniteType_of_quasiCompact B integerBase ℤS
      (Y₀ := projectiveSite B n W) h.imageι
  let X' : BigFppfOver B integerBase ℤS := CurveFamily.ofScheme (hZ := ℤS) h.image hX'mem
  let c : X' ⟶ projectiveSite B n W := CurveFamily.homOfScheme h.imageι
  let j : U ⟶ X' := CurveFamily.homOfScheme h.toImage
  have hjo : _root_.AlgebraicGeometry.IsOpenImmersion ((𝒯).map j) :=
    inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion h.toImage)
  have hcc : _root_.AlgebraicGeometry.IsClosedImmersion ((𝒯).map c) :=
    inferInstanceAs (_root_.AlgebraicGeometry.IsClosedImmersion h.imageι)
  have : _root_.AlgebraicGeometry.IsNoetherian ((𝒯).obj X') :=
    isNoetherian_of_locallyOfFiniteType ((𝒯).map c)
  have hjc : j ≫ c = i := (𝒯).map_injective ((Functor.map_comp _ _ _).trans h.toImage_imageι)
  -- the extension `G` of `F` to `X'` (Stacks 0G41)
  obtain ⟨G, hGqc, hGft, ⟨eG⟩⟩ :=
    exists_finiteType_modulePullback_iso_of_isOpenImmersion j F hF hFft
  -- the open immersion `U ⟶ X'` over `W`, as a situation of Stacks 0DP3
  subst hiq
  let πW := projectiveSiteStructure B n W
  have hcomp : schemeSpaceMap j ≫ schemeSpaceMap (c ≫ πW) = schemeSpaceMap (i ≫ πW) := by
    rw [← AlgebraicGeometry.schemeSpaceMap_comp, ← Category.assoc, hjc]
  have hsep : ∀ {T} (g : T ⟶ projectiveSite B n W)
      [_root_.AlgebraicGeometry.IsSeparated ((𝒯).map g)],
      IsSeparated B integerBase ℤS (schemeSpaceMap (g ≫ πW)).hom := fun g =>
    (isSeparated_yoneda_map_iff B integerBase ℤS (g ≫ πW)).2 (by
      rw [Functor.map_comp]
      infer_instance)
  have hfpY : IsFinitePresentation B integerBase ℤS (schemeSpaceMap (c ≫ πW)).hom :=
    isFinitePresentation_yoneda_map B integerBase ℤS (c ≫ πW) (by
      rw [Functor.map_comp]
      exact ⟨inferInstance, inferInstance, inferInstance⟩)
  let O : QuotOpenSubspaceSituation B integerBase ℤS :=
    { base := schemeSpace W
      X := schemeSpace U
      Y := schemeSpace X'
      j := schemeSpaceMap j
      structureX := schemeSpaceMap (i ≫ πW)
      structureY := schemeSpaceMap (c ≫ πW)
      comp := hcomp
      G := G
      quasicoherent := hGqc
      openImmersion := isOpenImmersion_yoneda_map B integerBase ℤS j hjo
      separatedX := hsep i
      separatedY := hsep c
      finitePresentationX := hq
      finitePresentationY := hfpY }
  -- `Quot^P_{G/X'/W}` is represented by a scheme proper over `W` (Stacks 0DPB, 0DP4)
  let κ := projectiveSiteProductIso n W
  let π' : schemeSpace X' ⟶ productSpace n (schemeSpace W) := schemeSpaceMap c ≫ κ.hom
  have : IsIso κ.hom.hom := inferInstanceAs (IsIso ((ObjectProperty.ι _).mapIso κ).hom)
  have hπ' : IsClosedImmersion B integerBase ℤS π'.hom :=
    isClosedImmersion_comp B integerBase ℤS (yoneda.map c) κ.hom.hom
      ((presheaf_yoneda_map_iff B integerBase ℤS inferInstance c).2 hcc)
      (isClosedImmersion_of_isIso B integerBase ℤS κ.hom.hom)
  have hcompπ : π' ≫ productSnd n (schemeSpace W) = schemeSpaceMap (c ≫ πW) := by
    change (schemeSpaceMap c ≫ κ.hom) ≫ productSnd n (schemeSpace W) = schemeSpaceMap (c ≫ πW)
    rw [Category.assoc, projectiveSiteProductIso_hom_productSnd,
      AlgebraicGeometry.schemeSpaceMap_comp]
  let PS : QuotPushforwardSituation B integerBase ℤS :=
    { base := schemeSpace W
      X := schemeSpace X'
      Y := productSpace n (schemeSpace W)
      π := π'
      structureX := schemeSpaceMap (c ≫ πW)
      structureY := productSnd n (schemeSpace W)
      comp := hcompπ
      F := G
      quasicoherent := hGqc
      affine := isAffineHom_of_isClosedImmersion B integerBase ℤS π'.hom hπ'
      quasiFinite := isQuasiFinite_of_isFinite B integerBase ℤS π'.hom (schemeSpace X').2
        (productSpace n (schemeSpace W)).2
        (isFinite_of_isClosedImmersion B integerBase ℤS π'.hom hπ')
      separatedX := hsep c
      separatedY := (isProper_productSnd n (schemeSpace W)).isSeparated
      finitePresentationX := hfpY
      finitePresentationY := isFinitePresentation_productSnd n (schemeSpace W) }
  have hG'qc : ((modulePushforward B integerBase ℤS π').obj G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePushforward_of_isClosedImmersion B integerBase ℤS π' hπ' G hGqc
  have hG'ft : SheafOfModules.IsFiniteTypeOnSite ((modulePushforward B integerBase ℤS π').obj G) :=
    isFiniteTypeOnSite_modulePushforward_comp_projectiveSiteProductIso c G hGqc hGft
  let M := (modulePullback B integerBase ℤS (productFst n (schemeSpace W))).obj
    (twistingModuleBase B n)
  have hM : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B integerBase ℤS (productSpace n (schemeSpace W)).1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B integerBase ℤS
        (productSpace n (schemeSpace W)).1 (productSpace n (schemeSpace W)).2).O)).property M :=
    stacksIsInvertible_modulePullback_obj B integerBase ℤS
      (productFst n (schemeSpace W)) (twistingModuleBase B n)
  have hB := isRepresentedProper_hilbertPolynomialQuot_twistingModule_of_affine
    (situation n (schemeSpace W) _ hG'qc) (situationFrame n (schemeSpace W) _ hG'qc) (Iso.refl _)
    hG'ft hP
  have hA := PS.isRepresentedProper_hilbertPolynomialQuot_of_directImage hπ' M (hM := hM) P hB
  -- `Quot^P_{F/U/W}` is an open subscheme `V` of the proper `Z` (Stacks 0DP3)
  obtain ⟨Z, V, ι, q', e, hq', hι, he⟩ :=
    O.exists_isOpenImmersion_represented_hilbertPolynomialQuot
      (M := (modulePullback B integerBase ℤS π').obj M)
      (hM := isInvertible_modulePullback B integerBase ℤS π' M) (P := P) hA
  let q'' : Z ⟶ W := Yoneda.fullyFaithful.preimage q'
  have hq'' : yoneda.map q'' = q' := Yoneda.fullyFaithful.map_preimage q'
  have : _root_.AlgebraicGeometry.IsProper ((𝒯).map q'') :=
    (isProper_yoneda_map_iff B integerBase ℤS q'').1 (hq''.symm ▸ hq')
  have := hι
  have : _root_.AlgebraicGeometry.IsNoetherian ((𝒯).obj Z) :=
    isNoetherian_of_locallyOfFiniteType ((𝒯).map q'')
  have : TopologicalSpace.NoetherianSpace ((𝒯).obj V) :=
    ((𝒯).map ι).isOpenEmbedding.isInducing.noetherianSpace
  have hrep : O.sourceSituation.IsRepresentedSeparatedFinitePresentation W (𝟙 _)
      (O.sourceSituation.hilbertPolynomialQuot
        ((modulePullback B integerBase ℤS O.j).obj ((modulePullback B integerBase ℤS π').obj M))
        (hL := isInvertible_modulePullback B integerBase ℤS O.j _
          (hL := isInvertible_modulePullback B integerBase ℤS π' M)) P) := by
    refine ⟨V, ι ≫ q'', e, ?_, ?_, ?_, inferInstance⟩
    · refine he.trans (congrArg (fun k => Functor.whiskerRight k uliftFunctor.{u + 1, u}) ?_)
      rw [Functor.map_comp, hq'']
      exact (Category.comp_id _).symm
    all_goals
      rw [Functor.map_comp]
      infer_instance
  -- transport to `F` (along `j^*G ≅ F`) and to `i^*𝒪(1)` (along `j^*π'^*M ≅ i^*M`)
  let D := schemeQuotSituation (i ≫ πW) hq F hF
  have hjπ : schemeSpaceMap j ≫ π' = schemeSpaceMap i ≫ κ.hom := by
    change schemeSpaceMap j ≫ schemeSpaceMap c ≫ κ.hom = schemeSpaceMap i ≫ κ.hom
    rw [← Category.assoc, ← AlgebraicGeometry.schemeSpaceMap_comp, hjc]
  have hL₁ := isInvertible_modulePullback B integerBase ℤS π' M
  let L := (modulePullback B integerBase ℤS (schemeSpaceMap j)).obj
    ((modulePullback B integerBase ℤS π').obj M)
  have hL : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B integerBase ℤS (schemeSpace U).1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B integerBase ℤS
        (schemeSpace U).1 (schemeSpace U).2).O)).property L :=
    isInvertible_modulePullback B integerBase ℤS (schemeSpaceMap j) _
  let eL : L ≅ projectiveTwist i :=
    (modulePullbackCompIso B integerBase ℤS (schemeSpaceMap j) π').app M ≪≫
      eqToIso (congrArg (fun k => (modulePullback B integerBase ℤS k).obj M) hjπ)
  have hjGqc : ((modulePullback B integerBase ℤS (schemeSpaceMap j)).obj G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B integerBase ℤS
      (schemeSpaceMap j) G hGqc
  let φ : D.F ⟶ (modulePullback B integerBase ℤS (schemeSpaceMap j)).obj G := eG.inv
  have : IsIso φ := ⟨⟨eG.hom, eG.inv_hom_id, eG.hom_inv_id⟩⟩
  refine IsRepresentedSeparatedFinitePresentation.of_eq
    (hilbertPolynomialQuot_congr D L (hL := hL) (hL' := isInvertible_projectiveTwist i) eL P) ?_
  have hrep' : (D.withModule _ hjGqc).IsRepresentedSeparatedFinitePresentation W (𝟙 _)
      ((D.withModule _ hjGqc).hilbertPolynomialQuot L (hL := hL) P) := hrep
  refine IsRepresentedSeparatedFinitePresentation.of_iso (D := D.withModule _ hjGqc) (D' := D)
    (𝟙 _) (Category.comp_id _)
    (D.hilbertPolynomialQuotWithModuleIso (hG := hjGqc) φ L (hL := hL) P) ?_ hrep'
  rw [hilbertPolynomialQuotWithModuleIso_hom_comp_toBase, Functor.whiskerRight_id',
    Category.comp_id]

end QuotSituation

end AlgebraicGeometry.Space

end
