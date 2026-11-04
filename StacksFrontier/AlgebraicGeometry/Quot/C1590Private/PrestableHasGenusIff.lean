module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.PrestableGenusLociOpen
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.ProperFlatFirstDirectImageRank
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.RepresentedHigherDirectImageComparison
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableModelRepresented
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStable
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeOfRankEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankChartScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeFpqcDescentQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSiteComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
public import
  StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.Qcqs

/-!
# The genus of a prestable family is the rank of `R¹f_*𝒪_X`

Let `f : X ⟶ S` be a prestable family of curves. Then `R¹f_*𝒪_X` is a locally free `𝒪_S`-module of
rank `g` exactly when every fibre of `f` has genus `g`. This is the input
`AlgebraicGeometry.C1590Private.PrestableHasGenusIff`, the consequence of Stacks 0E1J, parts (2)
and (3), used for the decomposition of `Curves^{prestable}` by genus (Stacks 0E6V).

Étale locally on `S` the family is a morphism of schemes `q : Z ⟶ U` (Stacks 0E6F, the hypothesis
`h0E6F`). The restriction of `R¹f_*𝒪_X` to the chart is `R¹` of the chart (Stacks 03LX), which is
the module associated with the Zariski `R¹q_*𝒪_Z` (Stacks 071N); ranks agree on the two sites
(Stacks 03DX, 05VG). For `q`, whose fibres are curves with `H⁰ = κ`, `R¹q_*𝒪_Z` is finite locally
free of rank `g` exactly when its fibres have genus `g`
(`StacksFrontier.AlgebraicGeometry.Quot.C1590Private.ProperFlatFirstDirectImageRank`). Finite local
freeness descends along the étale covering by the charts (Stacks 060X), and the rank is then read
on the rank loci, whose formation commutes with base change.

## Main results

* `AlgebraicGeometry.C1590Private.etaleModulePullbackFirstDirectImageIso`: the restriction of
  `R¹f_*𝒪_X` to an étale chart is `R¹` of the chart.
* `AlgebraicGeometry.C1590Private.prestableHasGenusIff_of`: the input `PrestableHasGenusIff`, from
  Stacks 0E6F.

## References

* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
* [Stacks Project, Tag 0E6V](https://stacks.math.columbia.edu/tag/0E6V)
* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
* [Stacks Project, Tag 060X](https://stacks.math.columbia.edu/tag/060X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.C1590Private

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **Ranks of a quasi-coherent module agree on the small étale site of the represented algebraic
space and on the Zariski site** (Stacks 03DX, 05VG, with the rank). -/
theorem isFiniteLocallyFreeOfRank_representedAssociatedModule_iff (U : BigFppfOver B integerBase hZ)
    (M : ((BigFppfOver.toScheme B integerBase hZ).obj U).Modules) [M.IsQuasicoherent] (r : ℕ) :
    RingedSite.IsFiniteLocallyFreeOfRank
        (Space.smallEtaleRingedSite B integerBase hZ (schemeSpace U).1 (schemeSpace U).2)
        ((Space.representedAssociatedModule B integerBase hZ U
          (isAlgebraicSpace_yoneda B integerBase hZ U)).obj M) r ↔
      Scheme.Modules.IsFiniteLocallyFreeOfRank M r :=
  (Space.isFiniteLocallyFreeOfRank_representedSmallEtaleModule_iff B integerBase hZ U _ r).trans
    ((SmallEtale.isFiniteLocallyFreeOfRank_associatedModule_iff (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B integerBase hZ).obj U) U.left.property M r).trans
      ((RingedSite.isFiniteLocallyFreeOfRank_iff_sheafOfModules
        ((BigFppfOver.toScheme B integerBase hZ).obj U).zariskiRingedSite M r).trans
        (Scheme.Modules.isFiniteLocallyFreeOfRank_iff M r).symm))

section Chart

variable (X : CurveFamily B hZ) {U Z : BigFppfOver B integerBase hZ} {φ : U ⟶ X.base}
  {p : schemeSpace Z ⟶ X.total} {q : Z ⟶ U}
  (sq : IsPullback p (schemeSpaceMap q) X.toBase (schemeSpaceMap φ))

/-- The morphism of algebraic spaces of an étale morphism of schemes of the site is étale. -/
theorem isEtale_schemeSpaceMap_of_etale {V W : BigFppfOver B integerBase hZ} (φ : V ⟶ W)
    (hφ : Etale ((BigFppfOver.toScheme B integerBase hZ).map φ)) :
    Space.IsEtale B integerBase hZ (schemeSpaceMap φ).hom :=
  Space.isEtale_of_presheaf_etale B integerBase hZ
    ((Space.presheaf_yoneda_map_etale_iff B integerBase hZ φ).2 hφ)

/-- **The restriction of `R¹f_*𝒪_X` to an étale chart is `R¹` of the chart** (Stacks 03LX). -/
def etaleModulePullbackFirstDirectImageIso
    (hφ : Space.IsEtale B integerBase hZ (schemeSpaceMap φ).hom) :
    (Space.etaleModulePullback B integerBase hZ (schemeSpaceMap φ) hφ).obj
        (X.firstDirectImage B hZ) ≅
      (curveFamilyOfIsPullback X φ p (schemeSpaceMap q) sq).firstDirectImage B hZ :=
  have := Space.hasInjectiveResolutions_modules B integerBase hZ X.total.1 X.total.2
  have := Space.hasInjectiveResolutions_modules B integerBase hZ (schemeSpace Z).1
    (schemeSpace Z).2
  ((Space.moduleHigherPushforwardEtaleBaseChangeIso B integerBase hZ p (schemeSpaceMap q)
      X.toBase (schemeSpaceMap φ) sq hφ 1).app
        (Space.structureSheafModule B integerBase hZ X.total)).symm ≪≫
    ((Space.modulePushforward B integerBase hZ (schemeSpaceMap q)).rightDerived 1).mapIso
      (Space.etaleModulePullbackStructureSheafModuleIso B integerBase hZ p _)

/-- **`R¹` of a chart is the module associated with the Zariski `R¹q_*𝒪_Z`** (Stacks 071N). -/
theorem nonempty_firstDirectImage_curveFamilyOfIsPullback_iso :
    Nonempty ((curveFamilyOfIsPullback X φ p (schemeSpaceMap q) sq).firstDirectImage B hZ ≅
      (Space.representedAssociatedModule B integerBase hZ U
          (isAlgebraicSpace_yoneda B integerBase hZ U)).obj
        (((Scheme.Modules.pushforward ((BigFppfOver.toScheme B integerBase hZ).map q)).rightDerived
          1).obj
          (SheafOfModules.unit ((BigFppfOver.toScheme B integerBase hZ).obj Z).ringCatSheaf))) := by
  have := CurveFamily.isProper_toScheme_map_of_isPullback_schemeSpaceMap X sq
  have := Space.hasInjectiveResolutions_modules B integerBase hZ (yoneda.obj Z)
    (isAlgebraicSpace_yoneda B integerBase hZ Z)
  have := Space.modulePushforward_additive B integerBase hZ
    (Space.representedSpaceMap B integerBase hZ q)
  obtain ⟨e⟩ := nonempty_rightDerived_modulePushforward_representedSpaceMap_iso B integerBase hZ q
    inferInstance inferInstance
    (SheafOfModules.unit ((BigFppfOver.toScheme B integerBase hZ).obj Z).ringCatSheaf)
    inferInstance 1
  exact ⟨((Space.modulePushforward B integerBase hZ
      (Space.representedSpaceMap B integerBase hZ q)).rightDerived 1).mapIso
        (Space.representedAssociatedModuleObjUnitIso B integerBase hZ Z
          (isAlgebraicSpace_yoneda B integerBase hZ Z)).symm ≪≫ e⟩

/-- **On a chart, `R¹` has rank `r` exactly when every fibre has genus `r`.** Over a chart on which
the prestable family `X` is a morphism of schemes `q : Z ⟶ U`, the restriction of `R¹f_*𝒪_X` to
the chart is finite locally free of rank `r` exactly when the genus-`r` locus of the base change is
the whole chart. -/
theorem isFiniteLocallyFreeOfRank_etaleModulePullback_iff (hX : IsPrestableCurveFamily B hZ X)
    (hφ : Space.IsEtale B integerBase hZ (schemeSpaceMap φ).hom) (r : ℕ) :
    RingedSite.IsFiniteLocallyFreeOfRank
        (Space.smallEtaleRingedSite B integerBase hZ (schemeSpace U).1 (schemeSpace U).2)
        ((Space.etaleModulePullback B integerBase hZ (schemeSpaceMap φ) hφ).obj
          (X.firstDirectImage B hZ)) r ↔
      (curveFamilyOfIsPullback X φ p (schemeSpaceMap q) sq).genusLocus r = Set.univ := by
  set T := BigFppfOver.toScheme B integerBase hZ
  have := CurveFamily.isProper_toScheme_map_of_isPullback_schemeSpaceMap X sq
  have := CurveFamily.flat_toScheme_map_of_isPullback X sq
  have hfp := finitePresentation_toScheme_map_of_isPullback X sq
  set XU := curveFamilyOfIsPullback X φ p (schemeSpaceMap q) sq
  have hXU : IsPrestableCurveFamily B hZ XU :=
    CurveFamily.isPrestableCurveFamily_of_hom
      (curveFamilyOfIsPullbackHom X φ p (schemeSpaceMap q) sq) hX
  obtain ⟨e⟩ := nonempty_firstDirectImage_curveFamilyOfIsPullback_iso X sq
  -- the fibres of the chart, as fibres of the scheme morphism `T.map q`
  have fibre : ∀ u : T.obj U, ∃ (K : Type u) (_ : Field K) (p' : Spec (.of K) ⟶ T.obj U)
      (Y : Scheme.{u}) (a : Y ⟶ T.obj Z) (g : Y ⟶ Spec (.of K)) (_ : IsPullback a g (T.map q) p')
      (pt : Spec (.of K)), p'.base pt = u ∧ topologicalKrullDim Y ≤ 1 ∧
        Function.Bijective g.appTop ∧ (genus g = r ↔ XU.HasGenusAt (XU.residueFieldPoint u) r) :=
    fun u => by
    obtain ⟨V, v, r₀, hV⟩ := exists_isPullback_yoneda_fieldValuedPoint B hZ XU
      (XU.residueFieldPoint u)
    obtain ⟨-, hdim, hiso, -⟩ := fibre_properties_of_isPrestableCurveFamily hXU _ v r₀ hV
    obtain ⟨a, hsq⟩ := exists_isPullback_toScheme_of_presentation q _ v r₀ hV
    exact ⟨_, inferInstance, _, _, T.map a, T.map v, hsq,
      IsLocalRing.closedPoint (XU.residueFieldPoint u).carrier,
      CurveFamily.schemePoint_residueFieldPoint XU u, hdim.le, bijective_appTop_of_isIso _ hiso,
      ⟨fun h => ⟨V, v, r₀, hV, h⟩, fun h => h.genus_eq v r₀ hV⟩⟩
  have hΓ : HasFieldGlobalFunctionsFibres (T.map q) := fun u => by
    obtain ⟨K, _, p', Y, a, g, hsq, pt, hpt, -, hb, -⟩ := fibre u
    exact ⟨K, inferInstance, p', Y, a, g, hsq, pt, hpt, hb⟩
  set R1 := ((Scheme.Modules.pushforward (T.map q)).rightDerived 1).obj
    (SheafOfModules.unit (T.obj Z).ringCatSheaf)
  have : (SheafOfModules.unit (T.obj Z).ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _
  have : R1.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.HigherDirectImageQcoh.isQuasicoherent_rightDerived _ _ 1
  let e' := etaleModulePullbackFirstDirectImageIso X sq hφ ≪≫ e
  refine Iff.trans (Iff.trans ⟨RingedSite.IsFiniteLocallyFreeOfRank.of_iso _ _ e',
    RingedSite.IsFiniteLocallyFreeOfRank.of_iso _ _ e'.symm⟩
      (isFiniteLocallyFreeOfRank_representedAssociatedModule_iff U R1 r))
    ⟨fun hR => Set.eq_univ_of_forall fun u => ?_, fun hU =>
    isFiniteLocallyFreeOfRank_rightDerived_one_of_forall_genus_eq (T.map q) hfp r fun u => ?_⟩
  · obtain ⟨K, _, p', Y, a, g, hsq, pt, -, hd, -, hg⟩ := fibre u
    exact hg.1 (genus_eq_of_isFiniteLocallyFreeOfRank_rightDerived_one (T.map q) hfp hΓ hR K p' a
      g hsq pt hd)
  · obtain ⟨K, _, p', Y, a, g, hsq, pt, hpt, hd, hb, hg⟩ := fibre u
    exact ⟨K, inferInstance, p', Y, a, g, hsq, pt, hpt, hd, hb, hg.2 (hU.ge trivial)⟩

end Chart

/-- **The genus of a prestable family is the rank of `R¹f_*𝒪_X`**, given the étale local scheme
charts of Stacks 0E6F: a prestable family of curves has `R¹f_*𝒪_X` finite locally free of rank `g`
exactly when all its fibres have genus `g`. -/
theorem hasGenus_iff_hasFibresOfGenus_of (h0E6F : HasEtaleLocalSchemeCharts B hZ)
    (X : CurveFamily B hZ) (hX : IsPrestableCurveFamily B hZ X) (g : ℕ) :
    CurveFamily.HasGenus B hZ X g ↔ X.HasFibresOfGenus g := by
  set T := BigFppfOver.toScheme B integerBase hZ
  rw [hasFibresOfGenus_iff_genusLocus_eq_univ X g]
  choose U Z φ q p hφ hu sq using fun s : T.obj X.base => h0E6F X s
  have hφ' : ∀ s, Space.IsEtale B integerBase hZ (schemeSpaceMap (φ s)).hom := fun s =>
    isEtale_schemeSpaceMap_of_etale _ (hφ s)
  have hpre : ∀ s,
      (curveFamilyOfIsPullback X (φ s) (p s) (schemeSpaceMap (q s)) (sq s)).genusLocus g =
        T.map (φ s) ⁻¹' X.genusLocus g := fun s =>
    genusLocus_eq_preimage
      (curveFamilyOfIsPullbackHom X (φ s) (p s) (schemeSpaceMap (q s)) (sq s)) g
  have hchart := fun s => isFiniteLocallyFreeOfRank_etaleModulePullback_iff X (sq s) hX (hφ' s) g
  constructor
  · intro hG
    refine Set.eq_univ_of_forall fun s => ?_
    obtain ⟨u, hus⟩ := hu s
    have hu' : u ∈ T.map (φ s) ⁻¹' X.genusLocus g := by
      rw [← hpre s, (hchart s).1 (Space.isFiniteLocallyFreeOfRank_etaleModulePullback B
        integerBase hZ _ (hφ' s) _ hG)]
      trivial
    rwa [Set.mem_preimage, hus] at hu'
  · intro hG
    set M := X.firstDirectImage B hZ
    have hrank : ∀ s, RingedSite.IsFiniteLocallyFreeOfRank
        (Space.smallEtaleRingedSite B integerBase hZ (schemeSpace (U s)).1 (schemeSpace (U s)).2)
        ((Space.modulePullback B integerBase hZ (schemeSpaceMap (φ s))).obj M) g := fun s =>
      RingedSite.IsFiniteLocallyFreeOfRank.of_iso _ _
        ((Space.modulePullbackIsoEtaleModulePullback B integerBase hZ _ (hφ' s)).app M).symm
        ((hchart s).2 (by rw [hpre s, hG]; exact Set.preimage_univ))
    have hM : M.IsQuasicoherentOnSite := by
      have : (Space.structureSheafModule B integerBase hZ X.total).IsQuasicoherentOnSite :=
        SheafOfModules.isQuasicoherentOnSite_unit _
      exact Space.isQuasicoherentOnSite_rightDerived_modulePushforward' B integerBase hZ X.toBase
        X.finitePresentation.2.1 X.finitePresentation.2.2 _ 1
    have hlf : SheafOfModules.IsFiniteLocallyFreeOnSite M :=
      Space.isFiniteLocallyFreeOnSite_of_pullback_isFpqcCovering_of_isQuasicoherentOnSite B
        integerBase hZ (fun s => schemeSpaceMap (φ s))
        (Space.isFpqcCovering_of_isEtaleCovering B integerBase hZ _ _
          (isEtaleCovering_yoneda_map B integerBase hZ φ hφ fun w => ⟨w, hu w⟩)) M hM
        fun s => (hrank s).isFiniteLocallyFreeOnSite
    have hloc : ∀ y, y ∈ Space.rankLocus M g := fun y => by
      obtain ⟨u, hu'⟩ := hu (Space.pointsToScheme B integerBase hZ X.base y)
      obtain ⟨w, rfl⟩ := Space.surjective_pointsToScheme B integerBase hZ (U _) u
      refine (Space.isFiniteLocallyFreeOfRank_modulePullback_iff
        (schemeSpaceMap (φ _)) hlf g).1 (hrank _) ⟨w, ?_⟩
      exact Space.injective_pointsToScheme B integerBase hZ X.base
        ((Space.pointsToScheme_pointsMap_yoneda B integerBase hZ (φ _) w).trans hu')
    exact RingedSite.IsFiniteLocallyFreeOfRank.of_iso _ _
      ((Space.modulePullbackIdIso B integerBase hZ _).app M)
      ((Space.isFiniteLocallyFreeOfRank_modulePullback_iff
        (𝟙 (schemeSpace X.base)) hlf g).2 fun y _ => hloc y)

/-- **The input `PrestableHasGenusIff`**, from the étale local scheme charts of Stacks 0E6F. -/
theorem prestableHasGenusIff_of (h0E6F : HasEtaleLocalSchemeCharts B hZ) :
    PrestableHasGenusIff B hZ :=
  hasGenus_iff_hasFibresOfGenus_of h0E6F

end AlgebraicGeometry.C1590Private

end
