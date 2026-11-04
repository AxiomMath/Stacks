module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartRestriction
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartRingTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartAffineQuadruple
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiDerivedPullbackCube
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiChartComparisonBridge
public import StacksFrontier.CategoryTheory.CatCommSqHInvCube
public meta import Lean
public meta import StacksFrontier.Tactic.HEqCongr

/-!
# Charts of étale squares and their affine quadruples

A chart `ch` of the square of schemes underlying a cartesian square of the site cuts out an
affine quadruple of the site. The chart is the whole chart of that quadruple, on the rings of
`ch`, pushed forward along the inclusions (`chartQuadrupleWhole_mapSquare`); hence condition (2)
of [Stacks, Tag 0DJ8] on `ch` is the one on the whole chart of the quadruple on its global
sections (`isIso_comparison_iff_chartQuadrupleChart`), for data with quasi-coherent cohomology.

## Main results

* `AlgebraicGeometry.Space.chartQuadrupleChart`: the whole chart of the affine quadruple of a
  chart, pushed forward to the square of the chart.
* `AlgebraicGeometry.Space.chartQuadrupleWhole_mapSquare`: a chart is the whole chart on its
  affine quadruple, pushed forward.
* `AlgebraicGeometry.Space.isIso_comparison_iff_chartQuadrupleChart`: condition (2) of
  Stacks 0DJ8 on a chart and on the whole chart of its affine quadruple.
* `AlgebraicGeometry.Space.representedQuasicoherentTransport_eq`: the 08GH transport of `φ` is
  the square of Stacks 08GH for the inverse equivalences followed by `E⁻¹(φ)`.
* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso_transport_coherence`: the
  composition isomorphisms of Stacks 0D6D along a transport square of algebraic spaces.
* `AlgebraicGeometry.Space.representedQuasicoherentInverseSquare_cube`: the squares of Stacks 08GH
  for the inverse equivalences paste along a commutative square of the site.
* `AlgebraicGeometry.Space.isIso_comparison_iff_chartQuadruple`: condition (2) of Stacks 0DJ8 on a
  chart and on the transported data of its affine quadruple.
-/

/- Instances that come into scope here only through the base versions of imported modules,
and that would change the elaboration below (universe joins, the small model of `D(R)`). -/
-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

attribute [-instance] SheafOfModules.hasBinBiprod

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/- The pro-étale copies of the size-bounded scheme instances (`boundedSchemeProperty` is the
same predicate as `schemeSizeBelow`) would replace the fppf ones in the fibre products below. -/
attribute [-instance]
  AlgebraicGeometry.ProEtale.instIsClosedUnderLimitsOfShapeSchemeBoundedSchemePropertyWalkingCospan
  AlgebraicGeometry.ProEtale.instIsClosedUnderIsomorphismsSchemeBoundedSchemeProperty

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- For an open immersion `i : Spec A ⟶ U`, the inclusion of the chart site object of `i` into `U`
is an open immersion of schemes. -/
instance {U : BigFppfOver B S hS} {A : CommRingCat.{u}}
    (i : Spec A ⟶ (BigFppfOver.toScheme B S hS).obj U) [AlgebraicGeometry.IsOpenImmersion i] :
    AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (chartSiteObjectι i)) := by
  rw [toScheme_map_chartSiteObjectι]
  exact inferInstanceAs (AlgebraicGeometry.IsOpenImmersion i)

section Quadruple'

attribute [local instance] BaseChangeChart.isOpenImmersion_incU BaseChangeChart.isOpenImmersion_incV
  BaseChangeChart.isOpenImmersion_incV'

variable {U V U' V' : BigFppfOver B S hS} {f₀ : U ⟶ V} {g₀ : V' ⟶ V} {f₀' : U' ⟶ V'}
  {g₀' : U' ⟶ U}
  (ch : BaseChangeChart ((BigFppfOver.toScheme B S hS).map f₀)
    ((BigFppfOver.toScheme B S hS).map g₀) ((BigFppfOver.toScheme B S hS).map f₀')
    ((BigFppfOver.toScheme B S hS).map g₀'))
  (hpb : IsPullback g₀' f₀' f₀ g₀)

/-- The whole chart of the affine quadruple of a chart `ch`, pushed forward to the square of
`ch` along the inclusions of the affine quadruple. -/
def chartQuadrupleChart :
    BaseChangeChart ((BigFppfOver.toScheme B S hS).map f₀)
      ((BigFppfOver.toScheme B S hS).map g₀) ((BigFppfOver.toScheme B S hS).map f₀')
      ((BigFppfOver.toScheme B S hS).map g₀') :=
  (affineQuadrupleChart (chartQuadrupleF ch) (chartQuadrupleG ch)
      (Limits.pullback.snd (chartQuadrupleF ch) (chartQuadrupleG ch))
      (Limits.pullback.fst (chartQuadrupleF ch) (chartQuadrupleG ch))
      (IsPullback.of_hasPullback (chartQuadrupleF ch) (chartQuadrupleG ch))).mapSquare
    ((BigFppfOver.toScheme B S hS).map (chartSiteObjectι ch.incU))
    ((BigFppfOver.toScheme B S hS).map (chartSiteObjectι ch.incV))
    ((BigFppfOver.toScheme B S hS).map (chartSiteObjectι ch.incV'))
    ((BigFppfOver.toScheme B S hS).map (chartQuadrupleι' ch hpb))
    (by rw [← Functor.map_comp, ← Functor.map_comp,
      chartSiteObjectι_comp ch.incU ch.incV f₀ (Spec.map ch.a) ch.wU])
    (by rw [← Functor.map_comp, ← Functor.map_comp,
      chartSiteObjectι_comp ch.incV' ch.incV g₀ (Spec.map ch.b) ch.wV'])
    (by rw [← Functor.map_comp, ← Functor.map_comp, chartQuadrupleι', hpb.lift_fst])
    (by rw [← Functor.map_comp, ← Functor.map_comp, chartQuadrupleι', hpb.lift_snd])

/-- The square of schemes of the affine quadruple of a chart is cartesian, over the ring maps
of the chart. -/
theorem isPullback_chartQuadruple :
    IsPullback ((BigFppfOver.toScheme B S hS).map (Limits.pullback.fst (chartQuadrupleF ch)
        (chartQuadrupleG ch)))
      ((BigFppfOver.toScheme B S hS).map (Limits.pullback.snd (chartQuadrupleF ch)
          (chartQuadrupleG ch)))
      (Spec.map ch.a) (Spec.map ch.b) := by
  have := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have h := (IsPullback.of_hasPullback (chartQuadrupleF ch) (chartQuadrupleG ch)).map
    (BigFppfOver.toScheme B S hS)
  rwa [toScheme_map_chartSiteObjectMap ch.incU ch.incV f₀ (Spec.map ch.a) ch.wU,
    toScheme_map_chartSiteObjectMap ch.incV' ch.incV g₀ (Spec.map ch.b) ch.wV'] at h

/-- The chart of the square of the affine quadruple of `ch` on the coordinate rings of `ch`:
its opens are the whole schemes. -/
def chartQuadrupleWhole :
    BaseChangeChart ((BigFppfOver.toScheme B S hS).map (chartQuadrupleF ch))
      ((BigFppfOver.toScheme B S hS).map (chartQuadrupleG ch))
      ((BigFppfOver.toScheme B S hS).map (Limits.pullback.snd (chartQuadrupleF ch)
          (chartQuadrupleG ch)))
      ((BigFppfOver.toScheme B S hS).map (Limits.pullback.fst (chartQuadrupleF ch)
          (chartQuadrupleG ch))) where
  R := ch.R
  A := ch.A
  R' := ch.R'
  A' := ch.A'
  incV := 𝟙 (Spec ch.R)
  incU := 𝟙 (Spec ch.A)
  incV' := 𝟙 (Spec ch.R')
  incU' := ((isPullback_SpecMap_of_isPushout ch.a ch.b ch.c ch.d ch.isPushout).isoIsPullback _ _
    (isPullback_chartQuadruple ch)).hom
  isOpenImmersion_incV := inferInstanceAs (AlgebraicGeometry.IsOpenImmersion (𝟙 (Spec ch.R)))
  isOpenImmersion_incU := inferInstanceAs (AlgebraicGeometry.IsOpenImmersion (𝟙 (Spec ch.A)))
  isOpenImmersion_incV' := inferInstanceAs (AlgebraicGeometry.IsOpenImmersion (𝟙 (Spec ch.R')))
  a := ch.a
  b := ch.b
  c := ch.c
  d := ch.d
  wU := (Category.id_comp _).trans
    ((toScheme_map_chartSiteObjectMap ch.incU ch.incV f₀ (Spec.map ch.a) ch.wU).trans
      (Category.comp_id _).symm)
  wV' := (Category.id_comp _).trans
    ((toScheme_map_chartSiteObjectMap ch.incV' ch.incV g₀ (Spec.map ch.b) ch.wV').trans
      (Category.comp_id _).symm)
  wU'U := (IsPullback.isoIsPullback_hom_fst _ _ _ _).trans (Category.comp_id _).symm
  wU'V' := (IsPullback.isoIsPullback_hom_snd _ _ _ _).trans (Category.comp_id _).symm
  isPushout := ch.isPushout

/-- **A chart is the whole chart on its affine quadruple, pushed forward.** -/
theorem chartQuadrupleWhole_mapSquare :
    (chartQuadrupleWhole ch).mapSquare
      ((BigFppfOver.toScheme B S hS).map (chartSiteObjectι ch.incU))
      ((BigFppfOver.toScheme B S hS).map (chartSiteObjectι ch.incV))
      ((BigFppfOver.toScheme B S hS).map (chartSiteObjectι ch.incV'))
      ((BigFppfOver.toScheme B S hS).map (chartQuadrupleι' ch hpb))
      (by rw [← Functor.map_comp, ← Functor.map_comp,
        chartSiteObjectι_comp ch.incU ch.incV f₀ (Spec.map ch.a) ch.wU])
      (by rw [← Functor.map_comp, ← Functor.map_comp,
        chartSiteObjectι_comp ch.incV' ch.incV g₀ (Spec.map ch.b) ch.wV'])
      (by rw [← Functor.map_comp, ← Functor.map_comp, chartQuadrupleι', hpb.lift_fst])
      (by rw [← Functor.map_comp, ← Functor.map_comp, chartQuadrupleι', hpb.lift_snd]) = ch := by
  have := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have h₁ : (BigFppfOver.toScheme B S hS).map (chartQuadrupleι' ch hpb) ≫
      (BigFppfOver.toScheme B S hS).map g₀' =
      (BigFppfOver.toScheme B S hS).map (Limits.pullback.fst _ _) ≫ ch.incU := by
    rw [← Functor.map_comp, chartQuadrupleι', hpb.lift_fst, Functor.map_comp,
      toScheme_map_chartSiteObjectι]
  have h₂ : (BigFppfOver.toScheme B S hS).map (chartQuadrupleι' ch hpb) ≫
      (BigFppfOver.toScheme B S hS).map f₀' =
      (BigFppfOver.toScheme B S hS).map (Limits.pullback.snd _ _) ≫ ch.incV' := by
    rw [← Functor.map_comp, chartQuadrupleι', hpb.lift_snd, Functor.map_comp,
      toScheme_map_chartSiteObjectι]
  cases ch with
  | mk R A R' A' incV incU incV' incU' hV hU hV' a b c d wU wV' wU'U wU'V' hpo =>
  dsimp only [BaseChangeChart.mapSquare, chartQuadrupleWhole]
  congr 1
  · exact (Category.id_comp _).trans (toScheme_map_chartSiteObjectι incV)
  · exact (Category.id_comp _).trans (toScheme_map_chartSiteObjectι incU)
  · exact (Category.id_comp _).trans (toScheme_map_chartSiteObjectι incV')
  · apply (hpb.map (BigFppfOver.toScheme B S hS)).hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₁).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ incU)
          (IsPullback.isoIsPullback_hom_fst _ _ _ _)).trans wU'U.symm)))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ incV')
          (IsPullback.isoIsPullback_hom_snd _ _ _ _)).trans wU'V'.symm)))

/-- **Condition (2) of Stacks 0DJ8 on a chart and on the whole chart of its affine quadruple.**
For a chart `ch` of the square of schemes of a cartesian square of the site, the comparison on
`ch` for `φ` is invertible if and only if the one on `chartQuadrupleChart ch hpb` is, for every
`K`, `K'` with quasi-coherent cohomology. -/
theorem isIso_comparison_iff_chartQuadrupleChart
    (K : DerivedCategory ((BigFppfOver.toScheme B S hS).obj U).Modules)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor _ n).obj K).IsQuasicoherent)
    (K' : DerivedCategory ((BigFppfOver.toScheme B S hS).obj U').Modules)
    (hK' : ∀ n : ℤ, ((DerivedCategory.homologyFunctor _ n).obj K').IsQuasicoherent)
    (φ : (Stacks.Duality.derivedPullback ((BigFppfOver.toScheme B S hS).map g₀')).obj K ⟶ K') :
    IsIso (ch.comparison K K' φ) ↔ IsIso ((chartQuadrupleChart ch hpb).comparison K K' φ) := by
  have : IsIso (chartQuadrupleWhole ch).incV := inferInstanceAs (IsIso (𝟙 (Spec ch.R)))
  have : IsIso (chartQuadrupleWhole ch).incU := inferInstanceAs (IsIso (𝟙 (Spec ch.A)))
  have : IsIso (chartQuadrupleWhole ch).incV' := inferInstanceAs (IsIso (𝟙 (Spec ch.R')))
  have : IsIso (chartQuadrupleWhole ch).incU' := inferInstanceAs (IsIso
    ((isPullback_SpecMap_of_isPushout ch.a ch.b ch.c ch.d ch.isPushout).isoIsPullback _ _
      (isPullback_chartQuadruple ch)).hom)
  have : IsIso (affineQuadrupleChart (chartQuadrupleF ch) (chartQuadrupleG ch)
      (Limits.pullback.snd (chartQuadrupleF ch) (chartQuadrupleG ch))
      (Limits.pullback.fst (chartQuadrupleF ch) (chartQuadrupleG ch))
      (IsPullback.of_hasPullback (chartQuadrupleF ch) (chartQuadrupleG ch))).incV :=
    (inferInstance : IsIso ((BigFppfOver.toScheme B S hS).obj
        (chartSiteObject ch.incV)).isoSpec.inv)
  have : IsIso (affineQuadrupleChart (chartQuadrupleF ch) (chartQuadrupleG ch)
      (Limits.pullback.snd (chartQuadrupleF ch) (chartQuadrupleG ch))
      (Limits.pullback.fst (chartQuadrupleF ch) (chartQuadrupleG ch))
      (IsPullback.of_hasPullback (chartQuadrupleF ch) (chartQuadrupleG ch))).incU :=
    (inferInstance : IsIso ((BigFppfOver.toScheme B S hS).obj
        (chartSiteObject ch.incU)).isoSpec.inv)
  have : IsIso (affineQuadrupleChart (chartQuadrupleF ch) (chartQuadrupleG ch)
      (Limits.pullback.snd (chartQuadrupleF ch) (chartQuadrupleG ch))
      (Limits.pullback.fst (chartQuadrupleF ch) (chartQuadrupleG ch))
      (IsPullback.of_hasPullback (chartQuadrupleF ch) (chartQuadrupleG ch))).incV' :=
    (inferInstance : IsIso ((BigFppfOver.toScheme B S hS).obj
        (chartSiteObject ch.incV')).isoSpec.inv)
  have : IsIso (affineQuadrupleChart (chartQuadrupleF ch) (chartQuadrupleG ch)
      (Limits.pullback.snd (chartQuadrupleF ch) (chartQuadrupleG ch))
      (Limits.pullback.fst (chartQuadrupleF ch) (chartQuadrupleG ch))
      (IsPullback.of_hasPullback (chartQuadrupleF ch) (chartQuadrupleG ch))).incU' :=
    (inferInstance : IsIso ((BigFppfOver.toScheme B S hS).obj
      (Limits.pullback (chartQuadrupleF ch) (chartQuadrupleG ch))).isoSpec.inv)
  refine (Iff.of_eq (congrArg (fun c => IsIso (BaseChangeChart.comparison c K K' φ))
    (chartQuadrupleWhole_mapSquare ch hpb)).symm).trans
    (((chartQuadrupleWhole ch).isIso_mapSquare_comparison_iff _ _ _ _ _ _ _ _ K K' φ).trans
      (((chartQuadrupleWhole ch).isIso_comparison_iff_of_isIso _ _
        (fun n => Stacks.Duality.isQuasicoherent_homology_derivedPullback' _ ⟨K, hK⟩ n) _
        (fun n => Stacks.Duality.isQuasicoherent_homology_derivedPullback' _ ⟨K', hK'⟩ n) _).trans
      ((BaseChangeChart.isIso_mapSquare_comparison_iff _ _ _ _ _ _ _ _ _ K K' φ).symm)))

end Quadruple'

section Transport

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)

/-- **Stacks 08GH for the inverse equivalences**: the square of Stacks 08GH read through the
inverses of the equivalences of Stacks 071Q, `E_T⁻¹ ⋙ Lg_0^* ≅ Lf^* ⋙ E_{T'}⁻¹`. -/
def representedQuasicoherentInverseSquare :
    (representedDualityQuasicoherentDerivedEquivalence B S hS T).inverse ⋙
        Stacks.Duality.quasiCoherentDerivedPullback' (B.inclusion.map g.left) ≅
      quasicoherentDerivedModulePullback (representedSpaceMap B S hS g) ⋙
        (representedDualityQuasicoherentDerivedEquivalence B S hS T').inverse :=
  (CatCommSq.hInv (representedDualityQuasicoherentDerivedEquivalence B S hS T)
    (Stacks.Duality.quasiCoherentDerivedPullback' (B.inclusion.map g.left))
    (quasicoherentDerivedModulePullback (representedSpaceMap B S hS g))
    (representedDualityQuasicoherentDerivedEquivalence B S hS T')
    ⟨(representedQuasicoherentDerivedPullbackIso g).symm⟩).iso

/-- The 08GH transport of `φ` is the inverse square at `K` followed by `E_{T'}⁻¹(φ)`. -/
theorem representedQuasicoherentTransport_eq
    (K : QuasicoherentDerivedCategory.{u, u} B S hS (representedSpace T).1
      (representedSpace T).2)
    (K' : QuasicoherentDerivedCategory.{u, u} B S hS (representedSpace T').1
      (representedSpace T').2)
    (φ : (quasicoherentDerivedModulePullback (representedSpaceMap B S hS g)).obj K ⟶ K') :
    representedQuasicoherentTransport g K K' φ =
      (representedQuasicoherentInverseSquare g).hom.app K ≫
        (representedDualityQuasicoherentDerivedEquivalence B S hS T').inverse.map φ := by
  rw [representedQuasicoherentTransport, Adjunction.homEquiv_unit,
    representedQuasicoherentInverseSquare,
    CatCommSq.hInv_iso_hom_app]
  simp only [Equivalence.toAdjunction_unit, Functor.map_comp, Iso.symm_inv, Category.assoc]
  rfl

end Transport

section Coherence

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {W' W T' T X X' : AlgebraicSpaces B S hS} (p : W' ⟶ W) (q : W ⟶ T) (r : W' ⟶ T')
  (s : T' ⟶ T) (a : T ⟶ X) (a' : T' ⟶ X') (g' : X' ⟶ X)

/-- **Coherence of Stacks 0D6D for a transport square of algebraic spaces.** For `p ≫ q = r ≫ s`
and `s ≫ a = a' ≫ g'`, the morphism `L(p ≫ q ≫ a)^* K ⟶ L(r ≫ a')^* K'` induced by
`φ : Lg'^* K ⟶ K'` is `Lr^*` of the one induced along `s`, read through the composition
isomorphisms of the square. -/
theorem smallEtaleDerivedModulePullbackCompIso_transport_coherence (hw : p ≫ q = r ≫ s)
    (ha' : s ≫ a = a' ≫ g') (hQ : p ≫ q ≫ a = (r ≫ a') ≫ g')
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K') :
    (smallEtaleDerivedModulePullback B S hS p).map
        ((smallEtaleDerivedModulePullbackCompIso B S hS q a).hom.app K) ≫
      (smallEtaleDerivedModulePullbackCompIso B S hS p (q ≫ a)).hom.app K ≫
      (smallEtaleDerivedModulePullbackCongr B S hS hQ).hom.app K ≫
      (smallEtaleDerivedModulePullbackCompIso B S hS (r ≫ a') g').inv.app K ≫
      (smallEtaleDerivedModulePullback B S hS (r ≫ a')).map φ =
    ((smallEtaleDerivedModulePullbackCompIso B S hS p q).hom.app
          ((smallEtaleDerivedModulePullback B S hS a).obj K) ≫
        (smallEtaleDerivedModulePullbackCongr B S hS hw).hom.app
          ((smallEtaleDerivedModulePullback B S hS a).obj K) ≫
        (smallEtaleDerivedModulePullbackCompIso B S hS r s).inv.app
          ((smallEtaleDerivedModulePullback B S hS a).obj K)) ≫
      (smallEtaleDerivedModulePullback B S hS r).map
        ((smallEtaleDerivedModulePullbackCompIso B S hS s a).hom.app K ≫
          (smallEtaleDerivedModulePullbackCongr B S hS ha').hom.app K ≫
          (smallEtaleDerivedModulePullbackCompIso B S hS a' g').inv.app K ≫
          (smallEtaleDerivedModulePullback B S hS a').map φ) ≫
      (smallEtaleDerivedModulePullbackCompIso B S hS r a').hom.app K' := by
  have hφ := (smallEtaleDerivedModulePullbackCompIso B S hS r a').hom.naturality φ
  have hA := smallEtaleDerivedModulePullbackCompIso_assoc_app B S hS r s a K
  have hB := smallEtaleDerivedModulePullbackCompIso_assoc_app B S hS p q a K
  have hC := smallEtaleDerivedModulePullbackCompIso_assoc_app B S hS r a' g' K
  have hD := smallEtaleDerivedModulePullbackCompIso_congr_left B S hS hw a K
  have hE := smallEtaleDerivedModulePullbackCompIso_congr_right B S hS r ha' K
  simp only [Functor.comp_obj, Functor.comp_map] at hφ
  simp only [Functor.map_comp, Category.assoc, smallEtaleDerivedModulePullbackCongr_hom_app]
  rw [hφ]
  simp only [← Category.assoc]
  refine congrArg (· ≫ (smallEtaleDerivedModulePullback B S hS (r ≫ a')).map φ) ?_
  simp only [Category.assoc]
  rw [← cancel_mono ((smallEtaleDerivedModulePullbackCompIso B S hS (r ≫ a') g').hom.app K)]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [hC, ← Functor.map_comp_assoc _
    ((smallEtaleDerivedModulePullbackCompIso B S hS a' g').inv.app K), Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, hE, ← reassoc_of% hA,
    Iso.inv_hom_id_app_assoc, reassoc_of% hD, ← reassoc_of% hB]
  rw [Stacks.Cohomology.DerivedBaseChangePasting.transportNatTrans_app_trans]

end Coherence

section Cube

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {W' W T' T : BigFppfOver B S hS} (p : W' ⟶ W) (q : W ⟶ T) (r : W' ⟶ T') (s : T' ⟶ T)
  (hw : representedSpaceMap B S hS p ≫ representedSpaceMap B S hS q =
    representedSpaceMap B S hS r ≫ representedSpaceMap B S hS s)
  (w₀ : B.inclusion.map p.left ≫ B.inclusion.map q.left =
    B.inclusion.map r.left ≫ B.inclusion.map s.left)

/-- **Pseudo-functoriality of the squares of Stacks 08GH for the inverse equivalences**: along a
commutative square `p ≫ q = r ≫ s` of the site, the two pastings of the squares
`E_T⁻¹ ⋙ Lg_0^* ≅ Lf_g^* ⋙ E_{T'}⁻¹` agree, read through the composition isomorphisms of the
derived pullbacks of the schemes and of the algebraic spaces. -/
theorem representedQuasicoherentInverseSquare_cube
    (P : QuasicoherentDerivedCategory.{u, u} B S hS (representedSpace T).1
      (representedSpace T).2) :
    (Stacks.Duality.quasiCoherentDerivedPullback' (B.inclusion.map p.left)).map
        ((representedQuasicoherentInverseSquare q).hom.app P) ≫
      (representedQuasicoherentInverseSquare p).hom.app
        ((quasicoherentDerivedModulePullback (representedSpaceMap B S hS q)).obj P) ≫
      (representedDualityQuasicoherentDerivedEquivalence B S hS W').inverse.map
        (ObjectProperty.homMk
        ((smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS p)
            (representedSpaceMap B S hS q)).hom.app P.obj ≫
          (smallEtaleDerivedModulePullbackCongr B S hS hw).hom.app P.obj ≫
          (smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS r)
            (representedSpaceMap B S hS s)).inv.app P.obj)) =
    (ObjectProperty.homMk
        ((Stacks.Duality.derivedPullbackCompIso (B.inclusion.map p.left)
            (B.inclusion.map q.left)).hom.app
            ((representedDualityQuasicoherentDerivedEquivalence B S hS T).inverse.obj P).obj ≫
          eqToHom (congrArg (fun t => (Stacks.Duality.derivedPullback t).obj
            ((representedDualityQuasicoherentDerivedEquivalence B S hS T).inverse.obj P).obj) w₀) ≫
          (Stacks.Duality.derivedPullbackCompIso (B.inclusion.map r.left)
            (B.inclusion.map s.left)).inv.app
            ((representedDualityQuasicoherentDerivedEquivalence B S hS T).inverse.obj P).obj) :
        (Stacks.Duality.quasiCoherentDerivedPullback' (B.inclusion.map p.left)).obj
            ((Stacks.Duality.quasiCoherentDerivedPullback' (B.inclusion.map q.left)).obj
              ((representedDualityQuasicoherentDerivedEquivalence B S hS T).inverse.obj P)) ⟶
          (Stacks.Duality.quasiCoherentDerivedPullback' (B.inclusion.map r.left)).obj
            ((Stacks.Duality.quasiCoherentDerivedPullback' (B.inclusion.map s.left)).obj
              ((representedDualityQuasicoherentDerivedEquivalence B S hS T).inverse.obj P))) ≫
      (Stacks.Duality.quasiCoherentDerivedPullback' (B.inclusion.map r.left)).map
        ((representedQuasicoherentInverseSquare s).hom.app P) ≫
      (representedQuasicoherentInverseSquare r).hom.app
        ((quasicoherentDerivedModulePullback (representedSpaceMap B S hS s)).obj P) := by
  have key := CategoryTheory.CatCommSq.hInv_cube_of_layers
    (representedDualityQuasicoherentDerivedEquivalence B S hS T)
    (representedDualityQuasicoherentDerivedEquivalence B S hS W)
    (representedDualityQuasicoherentDerivedEquivalence B S hS T')
    (representedDualityQuasicoherentDerivedEquivalence B S hS W')
    (Stacks.Duality.derivedPullback (B.inclusion.map q.left))
    (Stacks.Duality.isQuasicoherent_homology_derivedPullback' (B.inclusion.map q.left))
    (Stacks.Duality.derivedPullback (B.inclusion.map p.left))
    (Stacks.Duality.isQuasicoherent_homology_derivedPullback' (B.inclusion.map p.left))
    (Stacks.Duality.derivedPullback (B.inclusion.map s.left))
    (Stacks.Duality.isQuasicoherent_homology_derivedPullback' (B.inclusion.map s.left))
    (Stacks.Duality.derivedPullback (B.inclusion.map r.left))
    (Stacks.Duality.isQuasicoherent_homology_derivedPullback' (B.inclusion.map r.left))
    (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS q))
    (fun K => derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ _ K.obj K.property)
    (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS p))
    (fun K => derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ _ K.obj K.property)
    (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS s))
    (fun K => derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ _ K.obj K.property)
    (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS r))
    (fun K => derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ _ K.obj K.property)
    (representedQuasicoherentDerivedEquivalenceFunctorCompιIso T)
    (representedQuasicoherentDerivedEquivalenceFunctorCompιIso W)
    (representedQuasicoherentDerivedEquivalenceFunctorCompιIso T')
    (representedQuasicoherentDerivedEquivalenceFunctorCompιIso W')
    (Scheme.zariskiModelInverseSquare (X := representedSchemeRepresentedZariskiRingedToposHom
      B S hS W)
      (Y := representedSchemeRepresentedZariskiRingedToposHom B S hS T) (B.inclusion.map q.left))
    (Scheme.zariskiModelInverseSquare (X := representedSchemeRepresentedZariskiRingedToposHom
      B S hS W')
      (Y := representedSchemeRepresentedZariskiRingedToposHom B S hS W) (B.inclusion.map p.left))
    (Scheme.zariskiModelInverseSquare (X := representedSchemeRepresentedZariskiRingedToposHom
      B S hS T')
      (Y := representedSchemeRepresentedZariskiRingedToposHom B S hS T) (B.inclusion.map s.left))
    (Scheme.zariskiModelInverseSquare (X := representedSchemeRepresentedZariskiRingedToposHom
      B S hS W')
      (Y := representedSchemeRepresentedZariskiRingedToposHom B S hS T') (B.inclusion.map r.left))
    (representedZariskiToposDerivedPullbackCompIso B S hS q)
    (representedZariskiToposDerivedPullbackCompIso B S hS p)
    (representedZariskiToposDerivedPullbackCompIso B S hS s)
    (representedZariskiToposDerivedPullbackCompIso B S hS r)
    (representedDerivedPullbackSquareIso q) rfl (representedDerivedPullbackSquareIso p) rfl
    (representedDerivedPullbackSquareIso s) rfl (representedDerivedPullbackSquareIso r) rfl
    (representedQuasicoherentDerivedPullbackIso q)
    (representedQuasicoherentDerivedPullbackIso_hom_app_hom q)
    (representedQuasicoherentDerivedPullbackIso p)
    (representedQuasicoherentDerivedPullbackIso_hom_app_hom p)
    (representedQuasicoherentDerivedPullbackIso s)
    (representedQuasicoherentDerivedPullbackIso_hom_app_hom s)
    (representedQuasicoherentDerivedPullbackIso r)
    (representedQuasicoherentDerivedPullbackIso_hom_app_hom r)
    ((smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS p)
        (representedSpaceMap B S hS q)).hom ≫
      (smallEtaleDerivedModulePullbackCongr B S hS hw).hom ≫
      (smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS r)
        (representedSpaceMap B S hS s)).inv)
    (@Scheme.zariskiSquareDerivedPullbackIso (representedSchemeRepresentedZariskiRingedToposHom
      B S hS W')
      (representedSchemeRepresentedZariskiRingedToposHom B S hS W)
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T')
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T)
      (B.inclusion.map p.left) (B.inclusion.map q.left) (B.inclusion.map r.left)
      (B.inclusion.map s.left) w₀).hom
    (fun X => (Stacks.Duality.derivedPullbackCompIso (B.inclusion.map p.left)
        (B.inclusion.map q.left)).hom.app X ≫
      eqToHom (congrArg (fun t => (Stacks.Duality.derivedPullback t).obj X) w₀) ≫
      (Stacks.Duality.derivedPullbackCompIso (B.inclusion.map r.left)
        (B.inclusion.map s.left)).inv.app X)
    (fun Y => eq_of_heq (HEq.trans (by heq_congr) (HEq.trans
      (heq_of_eq (representedZariskiToposDerivedPullbackCompIso_cube p q r s hw w₀ Y))
      (by heq_congr))))
    (fun X => Scheme.zariskiModelInverseSquare_cube (B.inclusion.map p.left)
      (B.inclusion.map q.left) (B.inclusion.map r.left) (B.inclusion.map s.left) w₀ X) P
  exact eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq key) (by heq_congr)))

end Cube

section CoherenceHomMk

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

/-- The lift of `P.ι ⋙ F` maps `homMk x` to `homMk (F.map x)`. -/
theorem lift_comp_map_homMk {C D : Type*} {_ : Category C} {_ : Category D}
    {P : ObjectProperty C} {Q : ObjectProperty D} (F : C ⥤ D) (hF : ∀ X, Q ((P.ι ⋙ F).obj X))
    {X Y : P.FullSubcategory} (x : X.obj ⟶ Y.obj) :
    (Q.lift (P.ι ⋙ F) hF).map (ObjectProperty.homMk x) =
      ObjectProperty.homMk (X := (Q.lift (P.ι ⋙ F) hF).obj X) (Y := (Q.lift (P.ι ⋙ F) hF).obj Y)
        (F.map x) :=
  rfl

/-- `Lf^*` on `D_QCoh` maps `homMk x` to `homMk (Lf^* x)`. -/
theorem quasicoherentDerivedModulePullback_map_homMk {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    {K L : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2} (x : K.obj ⟶ L.obj) :
    (quasicoherentDerivedModulePullback f).map (ObjectProperty.homMk x) =
      ObjectProperty.homMk (X := (quasicoherentDerivedModulePullback f).obj K)
        (Y := (quasicoherentDerivedModulePullback f).obj L)
        ((smallEtaleDerivedModulePullback B S hS f).map x) :=
  lift_comp_map_homMk _ _ x

variable {W' W T' T : BigFppfOver B S hS} {X X' : AlgebraicSpaces B S hS}
  (p : W' ⟶ W) (q : W ⟶ T) (r : W' ⟶ T') (s : T' ⟶ T)
  (a : (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶ X)
  (a' : (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS) ⟶ X')
  (g' : X' ⟶ X)

/-- A square of `homMk`s in a full subcategory from the square of the underlying morphisms,
read through two heterogeneous junctions. -/
theorem homMk_comp_eq_of_heq.{v₁, u₁} {D : Type u₁} {_ : Category.{v₁} D} {Q : ObjectProperty D}
    {A₁ A₂ A₃ A₄ A₅ : Q.FullSubcategory}
    {x : A₁.obj ⟶ A₂.obj} {y : A₂.obj ⟶ A₃.obj} {c : A₁.obj ⟶ A₄.obj} {z : A₄.obj ⟶ A₅.obj}
    {e : A₅.obj ⟶ A₃.obj} {T : Type v₁} {L R : T} (hL : HEq (x ≫ y) L) (h : L = R)
    (hR : HEq R (c ≫ z ≫ e)) :
    ObjectProperty.homMk x ≫ ObjectProperty.homMk y =
      ObjectProperty.homMk c ≫ ObjectProperty.homMk z ≫ ObjectProperty.homMk e :=
  ObjectProperty.hom_ext _ (eq_of_heq (hL.trans ((heq_of_eq h).trans hR)))

/-- `smallEtaleDerivedModulePullbackCompIso_transport_coherence` in `D_QCoh`, as an equation of
`homMk`s. -/
theorem smallEtaleDerivedModulePullbackCompIso_transport_coherence_homMk (hw :
    (representedSpaceMap B S hS p) ≫ (representedSpaceMap B S hS q) =
        (representedSpaceMap B S hS r) ≫ (representedSpaceMap B S hS s))
    (ha' : (representedSpaceMap B S hS s) ≫ a = a' ≫ g') (hQ : (representedSpaceMap B S hS p) ≫
        (representedSpaceMap B S hS q) ≫ a = ((representedSpaceMap B S hS r) ≫ a') ≫ g')
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hK : QcohDerived B S hS X K)
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (hK' : QcohDerived B S hS X' K')
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K') :
    ObjectProperty.homMk (X := (quasicoherentDerivedModulePullback
        (representedSpaceMap B S hS p)).obj ((quasicoherentDerivedModulePullback
          (representedSpaceMap B S hS q)).obj
            (⟨(smallEtaleDerivedModulePullback B S hS a).obj K,
              derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a K hK⟩ :
              QuasicoherentDerivedCategory.{u, u} B S hS
              (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS).1
              (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS).2)))
        (Y := (quasicoherentDerivedModulePullback (representedSpaceMap B S hS p)).obj
          (⟨(smallEtaleDerivedModulePullback B S hS ((representedSpaceMap B S hS q)
            ≫ a)).obj K, derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _
              ((representedSpaceMap B S hS q)
                ≫ a) K hK⟩ : QuasicoherentDerivedCategory.{u, u} B S hS
                  (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS).1
                    (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS).2))
        ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS p)).map
          ((smallEtaleDerivedModulePullbackCompIso B S hS
            (representedSpaceMap B S hS q) a).hom.app K)) ≫
        ObjectProperty.homMk (X := (quasicoherentDerivedModulePullback
          (representedSpaceMap B S hS p)).obj (⟨(smallEtaleDerivedModulePullback B S hS
            ((representedSpaceMap B S hS q)
              ≫ a)).obj K, derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _
                ((representedSpaceMap B S hS q)
                  ≫ a) K hK⟩ : QuasicoherentDerivedCategory.{u, u} B S hS
                    (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS).1
                      (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ :
                        AlgebraicSpaces B S hS).2))
                        (Y := (⟨(smallEtaleDerivedModulePullback B S hS
                        ((representedSpaceMap B S hS r) ≫ a')).obj K',
                        derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _
                        ((representedSpaceMap B S hS r) ≫ a') K' hK'⟩ :
                        QuasicoherentDerivedCategory.{u, u} B S hS
                        (⟨yoneda.obj W', isAlgebraicSpace_yoneda B S hS W'⟩ :
                        AlgebraicSpaces B S hS).1 (⟨yoneda.obj W',
                        isAlgebraicSpace_yoneda B S hS W'⟩ : AlgebraicSpaces B S hS).2))
                        ((smallEtaleDerivedModulePullbackCompIso B S hS
                        (representedSpaceMap B S hS p) ((representedSpaceMap B S hS q) ≫ a)).hom.app
                        K ≫ (smallEtaleDerivedModulePullbackCongr B S hS hQ).hom.app K ≫
                        (smallEtaleDerivedModulePullbackCompIso B S hS
                        ((representedSpaceMap B S hS r) ≫ a') g').inv.app K ≫
                        (smallEtaleDerivedModulePullback B S hS
                        ((representedSpaceMap B S hS r) ≫ a')).map φ) =
      ObjectProperty.homMk (X := (quasicoherentDerivedModulePullback (X
          := representedSpace W) (representedSpaceMap B S hS p)).obj
            ((quasicoherentDerivedModulePullback (representedSpaceMap B S hS q)).obj
              (⟨(smallEtaleDerivedModulePullback B S hS a).obj K,
                derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a K hK⟩ :
                QuasicoherentDerivedCategory.{u, u} B S hS (representedSpace T).1
                (representedSpace T).2)))
          (Y := (quasicoherentDerivedModulePullback (X := representedSpace T')
            (representedSpaceMap B S hS r)).obj ((quasicoherentDerivedModulePullback
              (representedSpaceMap B S hS s)).obj
                (⟨(smallEtaleDerivedModulePullback B S hS a).obj K,
                  derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a K hK⟩ :
                  QuasicoherentDerivedCategory.{u, u} B S hS (representedSpace T).1
                  (representedSpace T).2))) ((smallEtaleDerivedModulePullbackCompIso B S hS
                  (representedSpaceMap B S hS p) (representedSpaceMap B S hS q)).hom.app
                  (⟨(smallEtaleDerivedModulePullback B S hS a).obj K,
                  derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a K hK⟩ :
                  QuasicoherentDerivedCategory.{u, u} B S hS (representedSpace T).1
                  (representedSpace T).2).obj ≫ (smallEtaleDerivedModulePullbackCongr
                  B S hS hw).hom.app (⟨(smallEtaleDerivedModulePullback B S hS a).obj K,
                  derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a K hK⟩ :
                  QuasicoherentDerivedCategory.{u, u} B S hS (representedSpace T).1
                  (representedSpace T).2).obj ≫ (smallEtaleDerivedModulePullbackCompIso B S hS
                  (representedSpaceMap B S hS r) (representedSpaceMap B S hS s)).inv.app
                  (⟨(smallEtaleDerivedModulePullback B S hS a).obj K,
                  derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a K hK⟩ :
                  QuasicoherentDerivedCategory.{u, u} B S hS (representedSpace T).1
                  (representedSpace T).2).obj) ≫
        ObjectProperty.homMk (X := (quasicoherentDerivedModulePullback
          (representedSpaceMap B S hS r)).obj ((quasicoherentDerivedModulePullback
            (representedSpaceMap B S hS s)).obj
              (⟨(smallEtaleDerivedModulePullback B S hS a).obj K,
                derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a K hK⟩ :
                QuasicoherentDerivedCategory.{u, u} B S hS
                (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS).1
                (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS).2)))
          (Y := (quasicoherentDerivedModulePullback (representedSpaceMap B S hS r)).obj
            (⟨(smallEtaleDerivedModulePullback B S hS a').obj K',
              derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a' K' hK'⟩ :
              QuasicoherentDerivedCategory.{u, u} B S hS
              (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS).1
              (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS).2))
          ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS r)).map
            ((smallEtaleDerivedModulePullbackCompIso B S hS
              (representedSpaceMap B S hS s) a).hom.app K ≫
                (smallEtaleDerivedModulePullbackCongr B S hS ha').hom.app K ≫
                  (smallEtaleDerivedModulePullbackCompIso B S hS a' g').inv.app K ≫
                    (smallEtaleDerivedModulePullback B S hS a').map φ)) ≫
        ObjectProperty.homMk (X := (quasicoherentDerivedModulePullback
          (representedSpaceMap B S hS r)).obj
            (⟨(smallEtaleDerivedModulePullback B S hS a').obj K',
              derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a' K' hK'⟩ :
              QuasicoherentDerivedCategory.{u, u} B S hS
              (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS).1
              (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS).2))
              (Y := (⟨(smallEtaleDerivedModulePullback B S hS
              ((representedSpaceMap B S hS r) ≫ a')).obj K',
              derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _
              ((representedSpaceMap B S hS r) ≫ a') K' hK'⟩ :
              QuasicoherentDerivedCategory.{u, u} B S hS
              (⟨yoneda.obj W', isAlgebraicSpace_yoneda B S hS W'⟩ : AlgebraicSpaces B S hS).1
              (⟨yoneda.obj W', isAlgebraicSpace_yoneda B S hS W'⟩ : AlgebraicSpaces B S hS).2))
              ((smallEtaleDerivedModulePullbackCompIso B S hS
              (representedSpaceMap B S hS r) a').hom.app K') :=
  homMk_comp_eq_of_heq (by heq_congr)
    (smallEtaleDerivedModulePullbackCompIso_transport_coherence _ _ _ _ a a' g' hw ha' hQ K K' φ)
    (by heq_congr)

end CoherenceHomMk

section Chase

/-- A diagram chase for functors `P₀`, `R₀`, `J` into a common category: the listed commuting
squares and equations give `P₀.map (e₁ ≫ e₂) ≫ t₁ = Z ≫ e₁' ≫ J.map ε`. -/
theorem chartQuadruple_transport_chase {𝒜 ℬ 𝒞 𝒮 : Type*} {_ : Category 𝒜} {_ : Category ℬ}
    {_ : Category 𝒞} {_ : Category 𝒮}
    (P₀ : 𝒜 ⥤ 𝒞) (R₀ : ℬ ⥤ 𝒞) (J : 𝒮 ⥤ 𝒞)
    {A₀ A₁ A₂ : 𝒜} {B₀ B₁ B₂ : ℬ} {S₀ S₁ S₂ S₃ S₄ : 𝒮}
    (e₁ : A₀ ⟶ A₁) (e₂ : A₁ ⟶ A₂) (t₁ : P₀.obj A₂ ⟶ J.obj S₁) (mp : P₀.obj A₂ ⟶ J.obj S₀)
    (ξ : S₀ ⟶ S₁) (mp' : P₀.obj A₁ ⟶ J.obj S₂) (y : S₂ ⟶ S₀) (ζ : S₂ ⟶ S₃) (ν : S₃ ⟶ S₄)
    (ε : S₄ ⟶ S₁) (cc : P₀.obj A₀ ⟶ R₀.obj B₀) (ms : B₀ ⟶ B₁) (x : B₁ ⟶ B₂) (t₂ : B₀ ⟶ B₂)
    (mr : R₀.obj B₁ ⟶ J.obj S₃) (e₁' : R₀.obj B₂ ⟶ J.obj S₄) (Z : P₀.obj A₀ ⟶ R₀.obj B₂)
    (ht₁ : t₁ = mp ≫ J.map ξ) (ht₂ : t₂ = ms ≫ x)
    (hnp : P₀.map e₂ ≫ mp = mp' ≫ J.map y)
    {y' : S₂ ⟶ S₀} {ξ' : S₀ ⟶ S₁} {ζ'' : S₂ ⟶ S₃} {ν' : S₃ ⟶ S₄} {ε' : S₄ ⟶ S₁}
    (hS : y' ≫ ξ' = ζ'' ≫ ν' ≫ ε')
    {mp'' : P₀.obj A₁ ⟶ J.obj S₂} {ζ' : S₂ ⟶ S₃} {ms' : B₀ ⟶ B₁} {mr' : R₀.obj B₁ ⟶ J.obj S₃}
    (hC : P₀.map e₁ ≫ mp'' ≫ J.map ζ' = cc ≫ R₀.map ms' ≫ mr')
    (hnr : R₀.map x ≫ e₁' = mr ≫ J.map ν) (hZ : Z = cc ≫ R₀.map t₂)
    (h1 : mp' = mp'') (h2 : ζ = ζ') (h3 : ms = ms') (h4 : mr = mr')
    (g1 : y = y') (g2 : ξ = ξ') (g3 : ζ = ζ'') (g4 : ν = ν') (g5 : ε = ε') :
    P₀.map (e₁ ≫ e₂) ≫ t₁ = Z ≫ e₁' ≫ J.map ε := by
  rw [← g1, ← g2, ← g3, ← g4, ← g5] at hS
  rw [← h1, ← h2, ← h3, ← h4] at hC
  subst ht₁ ht₂ hZ
  rw [P₀.map_comp, Category.assoc, reassoc_of% hnp, ← J.map_comp, hS, J.map_comp, J.map_comp,
    reassoc_of% hC, ← reassoc_of% hnr, R₀.map_comp]
  simp only [Category.assoc]

/-- An equation `key` of morphisms between lifts of functors to full subcategories, read in the
ambient categories through the inclusion `P₂.ι`. -/
theorem chartQuadruple_transport_chase_hom {𝒟₁ 𝒟₂ 𝒟₃ 𝒮₁ 𝒮₂ : Type*} {_ : Category 𝒟₁}
    {_ : Category 𝒟₂} {_ : Category 𝒟₃}
    {_ : Category 𝒮₁} {_ : Category 𝒮₂}
    {P₁ : ObjectProperty 𝒟₁} {P₂ : ObjectProperty 𝒟₂} {P₃ : ObjectProperty 𝒟₃}
    {Q₁ : ObjectProperty 𝒮₁} {Q₂ : ObjectProperty 𝒮₂}
    (F : 𝒟₁ ⥤ 𝒟₂) (hF : ∀ X, P₂ ((P₁.ι ⋙ F).obj X)) (G : 𝒟₃ ⥤ 𝒟₂)
    (hG : ∀ X, P₂ ((P₃.ι ⋙ G).obj X))
    (E₁ : Q₁.FullSubcategory ⥤ P₁.FullSubcategory) (E₂ : Q₂.FullSubcategory ⥤ P₂.FullSubcategory)
    {A : P₁.FullSubcategory} {S₁ S₁' : Q₁.FullSubcategory} {μ₁ : A ≅ E₁.obj S₁}
      {c₁ : S₁.obj ≅ S₁'.obj}
    {S₂ S₂' : Q₂.FullSubcategory} {T₁ : (P₂.lift (P₁.ι ⋙ F) hF).obj (E₁.obj S₁') ⟶ E₂.obj S₂'}
    {B₃ B₃' : P₃.FullSubcategory} {T₂ : B₃ ⟶ B₃'} {μ₂ : (P₂.lift (P₃.ι ⋙ G) hG).obj B₃' ≅ E₂.obj S₂}
    {c₂ : S₂.obj ≅ S₂'.obj} {Y₁ Y₂ : 𝒟₂} {x₁ : F.obj A.obj ⟶ Y₁} {x₂ : Y₁ ⟶ Y₂}
    {x₃ : Y₂ ⟶ G.obj B₃.obj}
    (key : (P₂.lift (P₁.ι ⋙ F) hF).map (μ₁.hom ≫ E₁.map (Q₁.homMk c₁.hom)) ≫ T₁ =
      (P₂.homMk (X := (P₂.lift (P₁.ι ⋙ F) hF).obj A) (Y := (P₂.lift (P₃.ι ⋙ G) hG).obj B₃) (x₁
          ≫ x₂ ≫ x₃) ≫
        (P₂.lift (P₃.ι ⋙ G) hG).map T₂) ≫ μ₂.hom ≫ E₂.map (Q₂.homMk c₂.hom)) :
    F.map ((P₁.ι.mapIso (μ₁ ≪≫ E₁.mapIso (Q₁.isoMk c₁))).hom) ≫ T₁.hom =
      (x₁ ≫ x₂ ≫ x₃ ≫ G.map T₂.hom) ≫ (P₂.ι.mapIso (μ₂ ≪≫ E₂.mapIso (Q₂.isoMk c₂))).hom := by
  have h := P₂.ι.congr_map key
  simp only [Functor.map_comp, Category.assoc, ObjectProperty.ι_map] at h
  simpa [Functor.mapIso_hom, Iso.trans_hom, Functor.map_comp, Category.assoc] using h

end Chase

section CongrDeep

open Lean Meta Elab Tactic

/-- A proof of `HEq a b` for two terms that are the same up to proofs and up to the spelling of
the objects, categories and instances they mention, built by congruence through *every* common
head (unlike `heq_congr_full`, which leaves a whole application to the kernel as soon as one
argument of a non-structural head differs); only the leaves where the two sides have different
heads are left to the kernel by `HEq.refl`. -/
meta partial def heqCongrDeep (cache : IO.Ref (Std.HashMap (Expr × Expr) Expr)) (a b : Expr) :
    MetaM Expr := do
  let refl := fun (x : Expr) => do
    let ty ← inferType x
    return mkApp2 (mkConst ``HEq.refl [← getLevel ty]) ty x
  if a == b then return ← refl a
  if let some r := (← cache.get)[(a, b)]? then return r
  if ← isProof a then
    return mkApp4 (mkConst ``proof_irrel_heq) (← inferType a) (← inferType b) a b
  let fa := a.getAppFn
  let fb := b.getAppFn
  let n := a.getAppNumArgs
  let sameHead := (fa.isConst && fb.isConst && fa.constName! == fb.constName! &&
      fa.constLevels! == fb.constLevels!) || (fa.isFVar && fa == fb)
  let r ← if sameHead && n > 0 && n == b.getAppNumArgs then
    try
      let thm ← mkHCongrWithArity fa n
      let as := a.getAppArgs
      let bs := b.getAppArgs
      let mut pf := thm.proof
      for i in [0:n] do
        match thm.argKinds[i]! with
        | .eq =>
          let ty ← inferType as[i]!
          let h ← heqCongrDeep cache as[i]! bs[i]!
          pf := mkApp3 pf as[i]! bs[i]!
            (mkApp4 (mkConst ``eq_of_heq [← getLevel ty]) ty as[i]! bs[i]! h)
        | .heq => pf := mkApp3 pf as[i]! bs[i]! (← heqCongrDeep cache as[i]! bs[i]!)
        | _ =>
          unless as[i]! == bs[i]! do throwError "fixed argument differs"
          pf := mkApp pf as[i]!
      pure pf
    catch _ => refl a
  else refl a
  cache.modify (·.insert (a, b) r)
  return r

/-- Close a goal `HEq a b` in which `a` and `b` are the same term up to proofs and up to the
spelling of what they mention, by congruence through every common head
(`heqCongrDeep`). The proof is assigned without unifying it with the goal; the kernel checks it
when the declaration is added. -/
elab "heq_congr_deep" : tactic => withMainContext do
  let g ← getMainGoal
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless t.isAppOfArity ``HEq 4 do throwError "the goal is not a heterogeneous equality"
  let cache ← IO.mkRef {}
  g.assign (← heqCongrDeep cache t.getAppArgs[1]! t.getAppArgs[3]!)
  replaceMainGoal []

end CongrDeep

section Statement

attribute [local instance] BaseChangeChart.isOpenImmersion_incU BaseChangeChart.isOpenImmersion_incV
  BaseChangeChart.isOpenImmersion_incV'

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {X X' : AlgebraicSpaces B S hS} (g' : X' ⟶ X)
  {U V U' V' : BigFppfOver B S hS} {f₀ : U ⟶ V} {g₀ : V' ⟶ V} {f₀' : U' ⟶ V'} {g₀' : U' ⟶ U}
  (hpb : IsPullback g₀' f₀' f₀ g₀)
  (ch : BaseChangeChart ((BigFppfOver.toScheme B S hS).map f₀)
      ((BigFppfOver.toScheme B S hS).map g₀)
    ((BigFppfOver.toScheme B S hS).map f₀') ((BigFppfOver.toScheme B S hS).map g₀'))

/-- **Every chart of an étale diagram is the whole chart of an affine quadruple.** For a chart
`ch` of the square of schemes underlying a cartesian square of the site over `g' : X' ⟶ X`, the
comparison of Stacks 0DJ8 (2) on `ch` for the 08GH transport of `φ` is invertible if and only if
the one on the whole chart of the affine quadruple of the site cut out by `ch` is. -/
theorem isIso_comparison_iff_chartQuadruple
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hK : QcohDerived B S hS X K)
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (hK' : QcohDerived B S hS X' K')
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K')
    (a : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ X)
    (a' : (⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ : AlgebraicSpaces B S hS) ⟶ X')
    (ha' : representedSpaceMap B S hS g₀' ≫ a = a' ≫ g') :
    IsIso (ch.comparison
        ((representedDualityQuasicoherentDerivedEquivalence B S hS U).inverse.obj
          ⟨(smallEtaleDerivedModulePullback B S hS (a)).obj K,
            derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ (a) K hK⟩).obj
        ((representedDualityQuasicoherentDerivedEquivalence B S hS U').inverse.obj
          ⟨(smallEtaleDerivedModulePullback B S hS (a')).obj K',
            derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ (a') K' hK'⟩).obj
        (representedQuasicoherentTransport g₀'
          ⟨(smallEtaleDerivedModulePullback B S hS (a)).obj K,
            derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ (a) K hK⟩
          ⟨(smallEtaleDerivedModulePullback B S hS (a')).obj K',
            derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ (a') K' hK'⟩
          (ObjectProperty.homMk
            ((smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS g₀')
                (a)).hom.app K ≫
              (smallEtaleDerivedModulePullbackCongr B S hS (ha')).hom.app K ≫
              (smallEtaleDerivedModulePullbackCompIso B S hS (a') g').inv.app K ≫
              (smallEtaleDerivedModulePullback B S hS (a')).map φ))).hom) ↔
      IsIso ((affineQuadrupleChart (chartQuadrupleF ch) (chartQuadrupleG ch)
          (Limits.pullback.snd (chartQuadrupleF ch) (chartQuadrupleG ch)) (Limits.pullback.fst
            (chartQuadrupleF ch) (chartQuadrupleG ch))
          (IsPullback.of_hasPullback (chartQuadrupleF ch) (chartQuadrupleG ch))).comparison
        ((representedDualityQuasicoherentDerivedEquivalence B S hS
          (chartSiteObject ch.incU)).inverse.obj
          ⟨(smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS
            (chartSiteObjectι ch.incU) ≫ a)).obj K,
            derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ (representedSpaceMap B S hS
              (chartSiteObjectι ch.incU) ≫ a) K hK⟩).obj
        ((representedDualityQuasicoherentDerivedEquivalence B S hS
          (Limits.pullback (chartQuadrupleF ch)
          (chartQuadrupleG ch))).inverse.obj
          ⟨(smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS
            (chartQuadrupleι' ch hpb) ≫ a')).obj K',
            derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ (representedSpaceMap B S hS
              (chartQuadrupleι' ch hpb) ≫ a') K' hK'⟩).obj
        (representedQuasicoherentTransport (Limits.pullback.fst (chartQuadrupleF ch)
          (chartQuadrupleG ch))
          ⟨(smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS
            (chartSiteObjectι ch.incU) ≫ a)).obj K,
            derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ (representedSpaceMap B S hS
              (chartSiteObjectι ch.incU) ≫ a) K hK⟩
          ⟨(smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS
            (chartQuadrupleι' ch hpb) ≫ a')).obj K',
            derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ (representedSpaceMap B S hS
              (chartQuadrupleι' ch hpb) ≫ a') K' hK'⟩
          (ObjectProperty.homMk
            ((smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS
              (Limits.pullback.fst (chartQuadrupleF ch) (chartQuadrupleG ch)))
                (representedSpaceMap B S hS (chartSiteObjectι ch.incU) ≫ a)).hom.app K ≫
              (smallEtaleDerivedModulePullbackCongr B S hS
                (chartQuadruple_ha' ch g' hpb a a' ha')).hom.app K ≫
              (smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS
                (chartQuadrupleι' ch hpb) ≫ a') g').inv.app K ≫
              (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS
                (chartQuadrupleι' ch hpb) ≫ a')).map φ))).hom) := by
  refine (isIso_comparison_iff_chartQuadrupleChart ch hpb _
    (fun n => ((representedDualityQuasicoherentDerivedEquivalence
      B S hS U).inverse.obj _).property n) _
    (fun n => ((representedDualityQuasicoherentDerivedEquivalence
      B S hS U').inverse.obj _).property n) _).trans ?_
  refine (BaseChangeChart.isIso_mapSquare_comparison_iff _ _ _ _ _ _ _ _ _ _ _ _).trans ?_
  refine Exists.elim (?_ : ∃ (e : _ ≅ _) (e' : _ ≅ _), _) fun e h => h.elim fun e' he =>
    BaseChangeChart.isIso_comparison_iff_of_iso _ e e' _ _ he
  refine ⟨(ObjectProperty.ι _).mapIso
      ((representedQuasicoherentInverseSquare
          (chartSiteObjectι ch.incU)).app ⟨(smallEtaleDerivedModulePullback B S hS
            (a)).obj K, derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ (a) K hK⟩ ≪≫
        (representedDualityQuasicoherentDerivedEquivalence B S hS
          (chartSiteObject ch.incU)).inverse.mapIso
          (ObjectProperty.isoMk _
            (Y := ⟨(smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS
              (chartSiteObjectι ch.incU) ≫ a)).obj K,
              derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ (representedSpaceMap B S hS
                (chartSiteObjectι ch.incU) ≫ a) K hK⟩)
            ((smallEtaleDerivedModulePullbackCompIso B S hS
              (representedSpaceMap B S hS (chartSiteObjectι ch.incU)) a).app K))),
    (ObjectProperty.ι _).mapIso
      ((representedQuasicoherentInverseSquare
          (chartQuadrupleι' ch hpb)).app ⟨(smallEtaleDerivedModulePullback B S hS
            (a')).obj K', derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ (a') K' hK'⟩ ≪≫
        (representedDualityQuasicoherentDerivedEquivalence B S hS
          (Limits.pullback (chartQuadrupleF ch)
          (chartQuadrupleG ch))).inverse.mapIso
          (ObjectProperty.isoMk _
            (Y := ⟨(smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS
              (chartQuadrupleι' ch hpb) ≫ a')).obj K',
              derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ (representedSpaceMap B S hS
                (chartQuadrupleι' ch hpb) ≫ a') K' hK'⟩)
            ((smallEtaleDerivedModulePullbackCompIso B S hS
              (representedSpaceMap B S hS (chartQuadrupleι' ch hpb)) a').app K'))), ?_⟩
  have w : (Limits.pullback.fst (chartQuadrupleF ch) (chartQuadrupleG ch))
      ≫ chartSiteObjectι ch.incU = chartQuadrupleι' ch hpb ≫ g₀' :=
    (hpb.lift_fst _ _ _).symm
  have hw : representedSpaceMap B S hS (Limits.pullback.fst (chartQuadrupleF ch)
      (chartQuadrupleG ch)) ≫ representedSpaceMap B S hS (chartSiteObjectι ch.incU) =
      representedSpaceMap B S hS (chartQuadrupleι' ch hpb) ≫ representedSpaceMap B S hS g₀' := by
    rw [representedSpaceMap_comp, representedSpaceMap_comp, w]
  have w₀ : B.inclusion.map (Limits.pullback.fst (chartQuadrupleF ch) (chartQuadrupleG ch)).left
      ≫ B.inclusion.map (chartSiteObjectι ch.incU).left =
      B.inclusion.map (chartQuadrupleι' ch hpb).left ≫ B.inclusion.map g₀'.left := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Over.comp_left, ← Over.comp_left, w]
  have hSc := smallEtaleDerivedModulePullbackCompIso_transport_coherence_homMk
      (Limits.pullback.fst (chartQuadrupleF ch) (chartQuadrupleG ch)) (chartSiteObjectι ch.incU)
          (chartQuadrupleι' ch hpb) g₀' a a' g' hw ha'
            (chartQuadruple_ha' ch g' hpb a a' ha') K hK K' hK' φ
  have hnp := (representedQuasicoherentInverseSquare (Limits.pullback.fst (chartQuadrupleF ch)
      (chartQuadrupleG ch))).hom.naturality
    (ObjectProperty.homMk (X := (quasicoherentDerivedModulePullback (representedSpaceMap B S hS
        (chartSiteObjectι ch.incU))).obj
          (⟨(smallEtaleDerivedModulePullback B S hS a).obj K,
            derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a K hK⟩ :
            QuasicoherentDerivedCategory.{u, u} B S hS (representedSpace U).1
            (representedSpace U).2)) (Y := (⟨(smallEtaleDerivedModulePullback B S hS
            ((representedSpaceMap B S hS (chartSiteObjectι ch.incU)) ≫ a)).obj K,
            derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _
            ((representedSpaceMap B S hS (chartSiteObjectι ch.incU)) ≫ a) K hK⟩ :
            QuasicoherentDerivedCategory.{u, u} B S hS
            (representedSpace (chartSiteObject ch.incU)).1
            (representedSpace (chartSiteObject ch.incU)).2))
            ((smallEtaleDerivedModulePullbackCompIso B S hS
            (representedSpaceMap B S hS (chartSiteObjectι ch.incU)) a).hom.app K))
  have hnr := (representedQuasicoherentInverseSquare (chartQuadrupleι' ch hpb)).hom.naturality
    (ObjectProperty.homMk (X := (quasicoherentDerivedModulePullback
        (representedSpaceMap B S hS g₀')).obj
          (⟨(smallEtaleDerivedModulePullback B S hS a).obj K,
            derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a K hK⟩ :
            QuasicoherentDerivedCategory.{u, u} B S hS (representedSpace U).1
            (representedSpace U).2)) (Y := (⟨(smallEtaleDerivedModulePullback B S hS a').obj K',
            derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a' K' hK'⟩ :
            QuasicoherentDerivedCategory.{u, u} B S hS (representedSpace U').1
            (representedSpace U').2)) ((smallEtaleDerivedModulePullbackCompIso B S hS
            (representedSpaceMap B S hS g₀') a).hom.app K ≫
            (smallEtaleDerivedModulePullbackCongr B S hS ha').hom.app K ≫
            (smallEtaleDerivedModulePullbackCompIso B S hS a' g').inv.app K ≫
            (smallEtaleDerivedModulePullback B S hS a').map φ))
  have ht₁ := representedQuasicoherentTransport_eq (Limits.pullback.fst (chartQuadrupleF ch)
      (chartQuadrupleG ch))
    (⟨(smallEtaleDerivedModulePullback B S hS
        ((representedSpaceMap B S hS (chartSiteObjectι ch.incU)) ≫ a)).obj K,
      derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _
        ((representedSpaceMap B S hS (chartSiteObjectι ch.incU)) ≫ a) K hK⟩ :
      QuasicoherentDerivedCategory.{u, u} B S hS (representedSpace
        (chartSiteObject ch.incU)).1 (representedSpace (chartSiteObject ch.incU)).2)
    (⟨(smallEtaleDerivedModulePullback B S hS
        ((representedSpaceMap B S hS (chartQuadrupleι' ch hpb)) ≫ a')).obj K',
      derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _
        ((representedSpaceMap B S hS (chartQuadrupleι' ch hpb)) ≫ a') K' hK'⟩ :
      QuasicoherentDerivedCategory.{u, u} B S hS
        (representedSpace (Limits.pullback (chartQuadrupleF ch) (chartQuadrupleG ch))).1
        (representedSpace (Limits.pullback (chartQuadrupleF ch) (chartQuadrupleG ch))).2)
    (ObjectProperty.homMk
      ((smallEtaleDerivedModulePullbackCompIso B S hS
          (representedSpaceMap B S hS (Limits.pullback.fst (chartQuadrupleF ch)
            (chartQuadrupleG ch)))
          ((representedSpaceMap B S hS (chartSiteObjectι ch.incU)) ≫ a)).hom.app K ≫
        (smallEtaleDerivedModulePullbackCongr B S hS
          (chartQuadruple_ha' ch g' hpb a a' ha')).hom.app K ≫
        (smallEtaleDerivedModulePullbackCompIso B S hS
          ((representedSpaceMap B S hS (chartQuadrupleι' ch hpb)) ≫ a') g').inv.app K ≫
        (smallEtaleDerivedModulePullback B S hS
          ((representedSpaceMap B S hS (chartQuadrupleι' ch hpb)) ≫ a')).map φ))
  have ht₂ := representedQuasicoherentTransport_eq g₀'
      (⟨(smallEtaleDerivedModulePullback B S hS a).obj K,
        derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a K hK⟩ :
        QuasicoherentDerivedCategory.{u, u} B S hS (representedSpace U).1 (representedSpace U).2)
        (⟨(smallEtaleDerivedModulePullback B S hS a').obj K',
        derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a' K' hK'⟩ :
        QuasicoherentDerivedCategory.{u, u} B S hS (representedSpace U').1 (representedSpace U').2)
        (ObjectProperty.homMk ((smallEtaleDerivedModulePullbackCompIso B S hS
        (representedSpaceMap B S hS g₀') a).hom.app K ≫
        (smallEtaleDerivedModulePullbackCongr B S hS ha').hom.app K ≫
        (smallEtaleDerivedModulePullbackCompIso B S hS a' g').inv.app K ≫
        (smallEtaleDerivedModulePullback B S hS a').map φ))
  have hC := representedQuasicoherentInverseSquare_cube (Limits.pullback.fst (chartQuadrupleF ch)
      (chartQuadrupleG ch)) (chartSiteObjectι ch.incU) (chartQuadrupleι' ch hpb) g₀' hw w₀
          (⟨(smallEtaleDerivedModulePullback B S hS a).obj K,
            derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a K hK⟩ :
            QuasicoherentDerivedCategory.{u, u} B S hS (representedSpace U).1
            (representedSpace U).2)
  have key := chartQuadruple_transport_chase
    (Stacks.Duality.quasiCoherentDerivedPullback' (B.inclusion.map (Limits.pullback.fst
        (chartQuadrupleF ch) (chartQuadrupleG ch)).left))
    (Stacks.Duality.quasiCoherentDerivedPullback' (B.inclusion.map (chartQuadrupleι' ch hpb).left))
    (representedDualityQuasicoherentDerivedEquivalence B S hS (Limits.pullback (chartQuadrupleF ch)
        (chartQuadrupleG ch))).inverse
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ht₁ ht₂ hnp hSc hC hnr rfl
    rfl rfl rfl rfl
    (quasicoherentDerivedModulePullback_map_homMk _ _)
    -- by congruence: `rfl` here sends the kernel unfolding the two spellings of the `homMk`
    (eq_of_heq (by heq_congr_deep)) rfl
        (quasicoherentDerivedModulePullback_map_homMk _ _) rfl
  have fin := chartQuadruple_transport_chase_hom (Stacks.Duality.derivedPullback (B.inclusion.map
      (Limits.pullback.fst (chartQuadrupleF ch) (chartQuadrupleG ch)).left)) _
    (Stacks.Duality.derivedPullback (B.inclusion.map (chartQuadrupleι' ch hpb).left)) _
    (representedDualityQuasicoherentDerivedEquivalence B S hS (chartSiteObject ch.incU)).inverse
    (representedDualityQuasicoherentDerivedEquivalence B S hS (Limits.pullback (chartQuadrupleF ch)
        (chartQuadrupleG ch))).inverse
    (S₁' := (⟨(smallEtaleDerivedModulePullback B S hS ((representedSpaceMap B S hS
        (chartSiteObjectι ch.incU))
          ≫ a)).obj K, derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _
            ((representedSpaceMap B S hS (chartSiteObjectι ch.incU))
              ≫ a) K hK⟩ : QuasicoherentDerivedCategory.{u, u} B S hS (representedSpace
                (chartSiteObject ch.incU)).1 (representedSpace
                  (chartSiteObject ch.incU)).2)) (S₂' :=
                    (⟨(smallEtaleDerivedModulePullback B S hS ((representedSpaceMap B S hS
                      (chartQuadrupleι' ch hpb))
                        ≫ a')).obj K', derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _
                          ((representedSpaceMap B S hS (chartQuadrupleι' ch hpb))
                            ≫ a') K' hK'⟩ : QuasicoherentDerivedCategory.{u, u} B S hS
                              (representedSpace (Limits.pullback (chartQuadrupleF ch)
                                (chartQuadrupleG ch))).1 (representedSpace
                                  (Limits.pullback (chartQuadrupleF ch) (chartQuadrupleG ch))).2))
    (μ₁ := (representedQuasicoherentInverseSquare (chartSiteObjectι ch.incU)).app
        (⟨(smallEtaleDerivedModulePullback B S hS a).obj K,
          derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a K hK⟩ :
          QuasicoherentDerivedCategory.{u, u} B S hS (representedSpace U).1 (representedSpace U).2))
          (c₁ := (smallEtaleDerivedModulePullbackCompIso B S hS
          (representedSpaceMap B S hS (chartSiteObjectι ch.incU)) a).app K)
    (μ₂ := (representedQuasicoherentInverseSquare (chartQuadrupleι' ch hpb)).app
        (⟨(smallEtaleDerivedModulePullback B S hS a').obj K',
          derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a' K' hK'⟩ :
          QuasicoherentDerivedCategory.{u, u} B S hS (representedSpace U').1
          (representedSpace U').2)) (c₂ := (smallEtaleDerivedModulePullbackCompIso B S hS
          (representedSpaceMap B S hS (chartQuadrupleι' ch hpb)) a').app K')
    key
  exact eq_of_heq (HEq.trans (by heq_congr_full) (HEq.trans (heq_of_eq fin) (by heq_congr_full)))

end Statement

end AlgebraicGeometry.Space
