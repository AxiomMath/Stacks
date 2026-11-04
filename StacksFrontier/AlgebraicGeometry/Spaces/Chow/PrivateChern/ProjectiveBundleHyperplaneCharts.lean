module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ProjectiveBundleTopSegre
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.HyperplaneChainTopSegre
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.RepresentedZeroSchemeIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernClasses
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleFlat
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.HyperplaneChainBundle
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsolutelyQuasiSeparatedAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackIdentity
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.DifferenceDivisorSheafFlatPullback
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionFormalObjectOpenLocus

/-!
# The étale charts of a projective bundle on which the top Segre identity is computed

Let `X/B` be good and `ℰ` a finite locally free `𝒪_X`-module of rank `d + 1` with projective
bundle `(π : P = 𝐏(ℰ) ⟶ X, 𝒪_P(1))`. For every base change `q : Q = Y ×_X P ⟶ Y` along a
morphism of good algebraic spaces and every point `y ∈ |Y|` there is an affine étale chart
`g : W ⟶ Y` through `y`, mapping to the presenting chart `U` of `X` inside an affine open
`V ⊆ U` on which the reading of `ℰ` is free; over it `Q_W = W ×_U 𝐏(ℰ_U)` is the scheme
`ℙ^d_W`, and the zero schemes of the pulled-back coordinates `T_{d-1}, …, T₀` of `𝒪(1)` form a
hyperplane chain (`Stacks.Chow.IsHyperplaneChain`). Read on the represented algebraic space
`h_{Q_W}` through the dictionary between closed subspaces of `h_T` and ideal sheaves of `T`
(`AlgebraicGeometry.Space.PrivateChern.schemeSpaceIdeal_zeroScheme`), this is the input of
`AlgebraicGeometry.Space.PrivateChern.rationallyEquivalentOn_topSegreCycle_of_isHyperplaneChain`,
and so the top Segre identity holds on every chart. By
`AlgebraicGeometry.Space.PrivateChern.hasInjectiveChowBaseChange_of_charts` the flat pullback
along `π` is injective on Chow groups after every base change (the injectivity half of
Stacks 0ERV).

## Main results

* `AlgebraicGeometry.Space.PrivateChern.representedRestrictionPullbackIso`: the restriction to
  the scheme of an inverse image along a morphism of represented spaces.
* `AlgebraicGeometry.Space.PrivateChern.hasInjectiveChowBaseChange_projectiveBundleDatum`:
  **injectivity of the flat pullback along a projective bundle after every base change.**

## References

* [Stacks Project, Tag 0ERU](https://stacks.math.columbia.edu/tag/0ERU)
* [Stacks Project, Tag 0ERV](https://stacks.math.columbia.edu/tag/0ERV)
* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space.PrivateChern

attribute [local instance] pointTopology

section Restriction

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The restriction to the scheme of an inverse image along a morphism of represented spaces**
is the scheme-theoretic inverse image of the restriction, for a quasi-coherent module. -/
def representedRestrictionPullbackIso {T P : BigFppfOver B S hS} (φ : T ⟶ P)
    (M : Modules.{u, u} B S hS (yoneda.obj P) (isAlgebraicSpace_yoneda B S hS P))
    (hM : M.IsQuasicoherentOnSite) :
    representedRestriction B S hS T ((modulePullback B S hS (representedSpaceMap B S hS φ)).obj M) ≅
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map φ)).obj
        (representedZariskiModule B S hS P M) :=
  restrictToChartSchemeIdEtaleChartIso B S hS T _ ≪≫
    (representedZariskiModulePullbackIso B S hS φ (relativelyRepresentable_yoneda_map B S hS φ)
      M hM).symm

end Restriction

section Charts

variable (D : BaseSpaceDimensionSituation.{u}) {X : D.Ambient} {sX : X ⟶ D.space}
  {hX : D.IsGood sX} (E : Modules.{u, u} D.site D.base D.base_mem X hX.1)

/-- An affine scheme étale over a good algebraic space is good. -/
theorem isGood_of_isEtale_of_isAffine {Y : D.Ambient} (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    {W : BigFppfOver D.site D.base D.base_mem}
    (hW : IsAffine ((BigFppfOver.toScheme D.site D.base D.base_mem).obj W))
    (g : yoneda.obj W ⟶ Y) (hg : IsEtale D.site D.base D.base_mem g) :
    D.IsGood (g ≫ sY) :=
  ⟨isAlgebraicSpace_yoneda D.site D.base D.base_mem W,
    isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source D.site D.base D.base_mem
      D.terminal_mem (isAlgebraicSpace_yoneda D.site D.base D.base_mem W)
      (isAbsolutelyQuasiSeparated_yoneda_of_isAffine D.site D.base D.base_mem D.terminal_mem W hW)
      _,
    isLocallyOfFiniteType_comp' D.site D.base D.base_mem g sY hY.1 D.isAlgebraicSpace
      (isLocallyOfFiniteType_of_isEtale' D.site D.base D.base_mem g hg) hY.2.2⟩

/-- **An affine étale chart through a point, over a free affine open of the presenting chart.**
Every point of a good `Y` over `X` lies in the image of an étale morphism `g : W ⟶ Y` from an
affine scheme whose composite to `X` factors through the presenting chart `U` of `X`, landing in
an affine open `V ⊆ U` over which every base change of the chart projective bundle `𝐏(ℰ_U)`
carries a hyperplane chain of sections of `𝒪(1)`. -/
theorem exists_affine_etale_chart_hyperplaneChain [E.IsQuasicoherentOnSite] (d : ℕ)
    (hr : IsFiniteLocallyFreeOfRank D sX hX E (d + 1)) {Y : D.Ambient} (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (f : Y ⟶ X) (y : points D.site D.base D.base_mem Y) :
    ∃ (Wst : BigFppfOver D.site D.base D.base_mem) (g : yoneda.obj Wst ⟶ Y)
      (α : Wst ⟶ (bundleBaseChart (goodSpace hX)).obj.left)
      (V0 : (chartScheme (bundleBaseChart (goodSpace hX))).Opens)
      (w0 : (BigFppfOver.toScheme D.site D.base D.base_mem).obj Wst ⟶ V0.toScheme),
      IsAffine ((BigFppfOver.toScheme D.site D.base D.base_mem).obj Wst) ∧
      IsEtale D.site D.base D.base_mem g ∧
      y ∈ Set.range (pointsMap D.site D.base D.base_mem (yoneda.obj Wst) g) ∧
      yoneda.map α ≫ (bundleBaseChart (goodSpace hX)).obj.hom = g ≫ f ∧
      w0 ≫ V0.ι = (BigFppfOver.toScheme D.site D.base D.base_mem).map α ∧
      ∀ (Q : Scheme.{u}) (c : Q ⟶ chartBundle (X := goodSpace hX) E (bundleBaseChart (goodSpace
          hX)))
        (q' : Q ⟶ V0.toScheme)
        (_ : IsPullback c q' (chartBundleToChart (X := goodSpace hX) E (bundleBaseChart (goodSpace
            hX))) V0.ι),
        Stacks.Chow.HasHyperplaneChain d q'
          ((Scheme.Modules.pullback c).obj (chartBundleTwist (X := goodSpace hX) E (bundleBaseChart
              (goodSpace hX)))) := by
  let 𝒯 := BigFppfOver.toScheme D.site D.base D.base_mem
  let U0 := bundleBaseChart (goodSpace hX)
  -- an affine étale chart of `Y` through `y`
  obtain ⟨Wy, ψ, y1, hWy, hψ, hy1⟩ :=
    exists_affine_etale_chart_of_point D.site D.base D.base_mem Y hY.1 y
  have hψe : IsEtale D.site D.base D.base_mem ψ :=
    (isEtale_iff_presheaf_of_yoneda D.site D.base D.base_mem ψ).2 hψ
  -- its base change along the presenting chart of `X`
  let f' := ψ ≫ f
  have hU0e := (projectiveBundlePresentation (goodSpace hX)).etale
  have hU0s := (projectiveBundlePresentation (goodSpace hX)).surjective
  let V := hU0e.rep.pullback f'
  let a : V ⟶ U0.obj.left := hU0e.rep.fst' f'
  let b : V ⟶ Wy := hU0e.rep.snd f'
  have hsqV : yoneda.map a ≫ U0.obj.hom = yoneda.map b ≫ f' := (hU0e.rep.isPullback' f').w
  have hpb := hU0e.rep.isPullback f'
  have hbs : Surjective (𝒯.map b) := hU0s.property f' _ _ hpb
  have hbe : Etale (𝒯.map b) := hU0e.property f' _ _ hpb
  have := hbe
  -- a point of `V` over `y1`
  obtain ⟨v1, hv1⟩ := (surjective_iff_surjective_pointsMap D.site D.base D.base_mem (yoneda.obj Wy)
    (isAlgebraicSpace_yoneda D.site D.base D.base_mem Wy) V (yoneda.map b)).1
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff D.site D.base D.base_mem
      (@Surjective) b).2 hbs) y1
  let v := pointsEquivScheme D.site D.base D.base_mem V v1
  -- an affine open of the chart over which the projective bundle has a hyperplane chain
  have := isFiniteLocallyFreeOfRank_chartBundleModule (X := goodSpace hX) E d hr U0
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (chartBundleModule (X := goodSpace hX) E U0) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ (d + 1)
  have : (chartBundleModule (X := goodSpace hX) E U0).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree _
  obtain ⟨V0, hV0, hu, hchainV0⟩ :=
    Stacks.Chow.exists_isAffineOpen_hasHyperplaneChain_projectiveBundle
      d (chartBundleModule (X := goodSpace hX) E U0) (𝒯.map a v)
  obtain ⟨W, hW, hvW, hWle⟩ :=
    exists_isAffineOpen_mem_and_subset (x := v) (U := 𝒯.map a ⁻¹ᵁ V0) hu
  let Wst := openSub V W
  let j := openSubHom V W
  have hj : 𝒯.map j = W.ι := toScheme_map_openSubHom _ _ _ V W
  let g : yoneda.obj Wst ⟶ Y := yoneda.map (j ≫ b) ≫ ψ
  have hge : IsEtale D.site D.base D.base_mem g := by
    refine isEtale_comp D.site D.base D.base_mem ?_ hψe
    refine (isEtale_iff_presheaf_of_yoneda D.site D.base D.base_mem _).2
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff D.site D.base D.base_mem (@Etale)
        (j ≫ b)).2 ?_)
    rw [Functor.map_comp, hj]
    exact MorphismProperty.comp_mem _ _ _ (inferInstance : Etale W.ι) hbe
  have hWa : IsAffine (𝒯.obj Wst) := hW
  have hWg : D.IsGood (g ≫ sY) := isGood_of_isEtale_of_isAffine D sY hY hWa g hge
  -- the morphism `W ⟶ V0`
  have hrange : Set.range (W.ι ≫ 𝒯.map a) ⊆ Set.range V0.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hWle x.2
  let w0 : W.toScheme ⟶ V0.toScheme := IsOpenImmersion.lift V0.ι (W.ι ≫ 𝒯.map a) hrange
  have hw0 : w0 ≫ V0.ι = W.ι ≫ 𝒯.map a := IsOpenImmersion.lift_fac _ _ _
  have hbot : yoneda.map (j ≫ a) ≫ U0.obj.hom = g ≫ f := by
    simp only [g, f', Functor.map_comp, Category.assoc] at hsqV ⊢
    rw [hsqV]
  refine ⟨Wst, g, j ≫ a, V0, w0, hWa, hge,
    ⟨(pointsEquivScheme D.site D.base D.base_mem Wst).symm ⟨v, hvW⟩, ?_⟩, hbot,
    hw0.trans ((congrArg (· ≫ 𝒯.map a) hj.symm).trans (𝒯.map_comp j a).symm), hchainV0⟩
  have h1 := pointsMap_yoneda_map_pointsEquivScheme_symm (j ≫ b) ⟨v, hvW⟩
  have h2 := pointsMap_yoneda_map_pointsEquivScheme_symm b v
  have hv1' : (pointsEquivScheme D.site D.base D.base_mem V).symm v = v1 :=
    Equiv.symm_apply_apply _ _
  have h3 : 𝒯.map (j ≫ b) ⟨v, hvW⟩ = 𝒯.map b v := by
    rw [Functor.map_comp, hj]
    rfl
  show pointsMap D.site D.base D.base_mem _ (yoneda.map (j ≫ b) ≫ ψ) _ = y
  rw [pointsMap_comp, Function.comp_apply, h1, h3, ← h2, hv1', hv1, hy1]

/-- **The base change of the projective bundle to a chart over the presenting chart.** For an
étale `g : h_W ⟶ Y` whose composite to `X` factors through the presenting chart `U` by `α`, the
represented space of `T = W ×_U 𝐏(ℰ_U)` is the base change of `Q = Y ×_X 𝐏(ℰ)` along `g`. -/
theorem exists_isPullback_chartBundle [E.IsQuasicoherentOnSite]
    [HasPullbacks (BigFppfOver D.site D.base D.base_mem)]
    (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E) {Y : D.Ambient} (f : Y ⟶ X)
    {Wst : BigFppfOver D.site D.base D.base_mem} (g : yoneda.obj Wst ⟶ Y)
    (α : Wst ⟶ (bundleBaseChart (goodSpace hX)).obj.left)
    (hα : yoneda.map α ≫ (bundleBaseChart (goodSpace hX)).obj.hom = g ≫ f) :
    ∃ g' : yoneda.obj (pullback α ((projectiveBundleChartFamily (X := goodSpace hX) E
        hfree).siteToChart
        (bundleBaseChart (goodSpace hX)))) ⟶
        pullback f (projectiveBundleProj (X := goodSpace hX) E hfree).hom,
      IsPullback g' (yoneda.map (pullback.fst _ _))
        (pullback.fst f (projectiveBundleProj (X := goodSpace hX) E hfree).hom) g ∧
      g' ≫ pullback.snd f (projectiveBundleProj (X := goodSpace hX) E hfree).hom =
        yoneda.map (pullback.snd _ _) ≫ projectiveBundleChart (X := goodSpace hX) E hfree := by
  have hsqT := (IsPullback.of_hasPullback α ((projectiveBundleChartFamily (X := goodSpace hX) E
    hfree).siteToChart (bundleBaseChart (goodSpace hX)))).flip.map yoneda
  have hbig := hsqT.paste_horiz (isPullback_projectiveBundleProj (X := goodSpace hX) E hfree)
  rw [hα] at hbig
  refine ⟨pullback.lift (yoneda.map (pullback.fst _ _) ≫ g) _
    (by rw [Category.assoc]; exact hbig.w.symm), ?_, pullback.lift_snd _ _ _⟩
  refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback f (projectiveBundleProj (X := goodSpace hX) E hfree).hom).flip
  rw [pullback.lift_snd]
  exact hbig

/-- **The hyperplane chain on a chart of the projective bundle.** On `T = W ×_U 𝐏(ℰ_U)`, for a
chart `W ⟶ U` landing in an affine open `V ⊆ U` over which the chart bundle has a hyperplane
chain, the restriction to `T` of any module isomorphic to the inverse image of `𝒪_P(1)` has a
hyperplane chain of sections over `W`. -/
theorem hasHyperplaneChain_representedRestriction [E.IsQuasicoherentOnSite]
    [HasPullbacks (BigFppfOver D.site D.base D.base_mem)]
    (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E) (d : ℕ)
    {Wst : BigFppfOver D.site D.base D.base_mem} (α : Wst ⟶ (bundleBaseChart (goodSpace
        hX)).obj.left)
    (V0 : (chartScheme (bundleBaseChart (goodSpace hX))).Opens)
    (w0 : (BigFppfOver.toScheme D.site D.base D.base_mem).obj Wst ⟶ V0.toScheme)
    (hw0 : w0 ≫ V0.ι = (BigFppfOver.toScheme D.site D.base D.base_mem).map α)
    (hV0 : ∀ (Q : Scheme.{u}) (c : Q ⟶ chartBundle (X := goodSpace hX) E (bundleBaseChart (goodSpace
        hX)))
        (q' : Q ⟶ V0.toScheme)
        (_ : IsPullback c q' (chartBundleToChart (X := goodSpace hX) E (bundleBaseChart (goodSpace
            hX)))
          V0.ι),
        Stacks.Chow.HasHyperplaneChain d q'
          ((Scheme.Modules.pullback c).obj
            (chartBundleTwist (X := goodSpace hX) E (bundleBaseChart (goodSpace hX)))))
    (N : Modules.{u, u} D.site D.base D.base_mem (yoneda.obj (pullback α
      ((projectiveBundleChartFamily (X := goodSpace hX) E hfree).siteToChart (bundleBaseChart
          (goodSpace hX)))))
      (isAlgebraicSpace_yoneda _ _ _ _))
    (e : N ≅ (modulePullback D.site D.base D.base_mem (representedSpaceMap D.site D.base D.base_mem
      (pullback.snd α ((projectiveBundleChartFamily (X := goodSpace hX) E hfree).siteToChart
        (bundleBaseChart (goodSpace hX)))))).obj
      ((modulePullback D.site D.base D.base_mem
          (projectiveBundleAtlas (X := goodSpace hX) E hfree)).obj
        (projectiveBundleTwist (X := goodSpace hX) E hfree).obj)) :
    Stacks.Chow.HasHyperplaneChain d
      ((BigFppfOver.toScheme D.site D.base D.base_mem).map (pullback.fst α
        ((projectiveBundleChartFamily (X := goodSpace hX) E hfree).siteToChart (bundleBaseChart
            (goodSpace hX)))))
      (representedRestriction D.site D.base D.base_mem _ N) := by
  let 𝒯 := BigFppfOver.toScheme D.site D.base D.base_mem
  let c0 := (projectiveBundleChartFamily (X := goodSpace hX) E hfree).siteToChart (bundleBaseChart
      (goodSpace hX))
  have hT : IsPullback (𝒯.map (pullback.snd α c0)) (𝒯.map (pullback.fst α c0)) (𝒯.map c0)
      (𝒯.map α) :=
    (IsPullback.of_hasPullback α c0).flip.map 𝒯
  have hQ := IsPullback.of_hasPullback
    (chartBundleToChart (X := goodSpace hX) E (bundleBaseChart (goodSpace hX))) V0.ι
  let ψT : 𝒯.obj (pullback α c0) ⟶ pullback
      (chartBundleToChart (X := goodSpace hX) E (bundleBaseChart (goodSpace hX))) V0.ι :=
    pullback.lift (𝒯.map (pullback.snd α c0)) (𝒯.map (pullback.fst α c0) ≫ w0)
      (by rw [Category.assoc, hw0]; exact hT.w)
  have hψ₁ : ψT ≫ pullback.fst _ _ = 𝒯.map (pullback.snd α c0) := pullback.lift_fst _ _ _
  have hleft : IsPullback ψT (𝒯.map (pullback.fst α c0)) (pullback.snd _ _) w0 := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) hQ
    rw [hψ₁, hw0]
    exact hT
  have hM : ((modulePullback D.site D.base D.base_mem (projectiveBundleAtlas (X := goodSpace hX) E
      hfree)).obj (projectiveBundleTwist (X := goodSpace hX) E hfree).obj).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite D.site D.base D.base_mem _ _
      (projectiveBundleTwist (X := goodSpace hX) E hfree).property
  refine (hV0 _ _ _ hQ).of_isPullback hleft ?_
  exact restrictToChartSchemeIdEtaleChartIso D.site D.base D.base_mem _ N ≪≫
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite D.site)
      (𝒯.obj (pullback α c0)) (pullback α c0).left.property).mapIso
      ((representedSmallEtaleModuleEquivalence D.site D.base D.base_mem _).inverse.mapIso e) ≪≫
    (representedZariskiModulePullbackIso D.site D.base D.base_mem (pullback.snd α c0)
      (relativelyRepresentable_yoneda_map D.site D.base D.base_mem _) _ hM).symm ≪≫
    (Scheme.Modules.pullback (𝒯.map (pullback.snd α c0))).mapIso
      (projectiveBundleTwistChartReadingIso (X := goodSpace hX) E hfree) ≪≫
    (Scheme.Modules.pullbackCongr hψ₁.symm).app _ ≪≫
    ((Scheme.Modules.pullbackComp ψT (pullback.fst _ _)).app _).symm

/-- **The top Segre identity on a chart of the projective bundle.** -/
theorem rationallyEquivalentOn_topSegreCycle_chartBundle [E.IsQuasicoherentOnSite]
    [HasPullbacks (BigFppfOver D.site D.base D.base_mem)]
    (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E) (d : ℕ)
    {Wst : BigFppfOver D.site D.base D.base_mem} (α : Wst ⟶ (bundleBaseChart (goodSpace
        hX)).obj.left)
    (V0 : (chartScheme (bundleBaseChart (goodSpace hX))).Opens)
    (w0 : (BigFppfOver.toScheme D.site D.base D.base_mem).obj Wst ⟶ V0.toScheme)
    (hw0 : w0 ≫ V0.ι = (BigFppfOver.toScheme D.site D.base D.base_mem).map α)
    (hV0 : ∀ (Q : Scheme.{u}) (c : Q ⟶ chartBundle (X := goodSpace hX) E (bundleBaseChart (goodSpace
        hX)))
        (q' : Q ⟶ V0.toScheme)
        (_ : IsPullback c q' (chartBundleToChart (X := goodSpace hX) E (bundleBaseChart (goodSpace
            hX)))
          V0.ι),
        Stacks.Chow.HasHyperplaneChain d q'
          ((Scheme.Modules.pullback c).obj
            (chartBundleTwist (X := goodSpace hX) E (bundleBaseChart (goodSpace hX)))))
    (sW : yoneda.obj Wst ⟶ D.space) (hW : D.IsGood sW)
    (sQ : yoneda.obj (pullback α ((projectiveBundleChartFamily (X := goodSpace hX) E
        hfree).siteToChart
      (bundleBaseChart (goodSpace hX)))) ⟶ D.space) (hQ : D.IsGood sQ)
    (hq : yoneda.map (pullback.fst _ _) ≫ sW = sQ)
    (hqp : IsProper D.site D.base D.base_mem (yoneda.map (pullback.fst α
      ((projectiveBundleChartFamily (X := goodSpace hX) E hfree).siteToChart (bundleBaseChart
          (goodSpace hX))))))
    (hqf : IsFlat D.site D.base D.base_mem (yoneda.map (pullback.fst α
      ((projectiveBundleChartFamily (X := goodSpace hX) E hfree).siteToChart (bundleBaseChart
          (goodSpace hX))))))
    (hqd : HasRelativeDimension d D.site D.base D.base_mem (yoneda.map (pullback.fst α
      ((projectiveBundleChartFamily (X := goodSpace hX) E hfree).siteToChart (bundleBaseChart
          (goodSpace hX))))))
    (N : Modules.{u, u} D.site D.base D.base_mem _ hQ.1)
    (hN : IsInvertibleModule (⟨_, hQ.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)
    (e : N ≅ (modulePullback D.site D.base D.base_mem (representedSpaceMap D.site D.base D.base_mem
      (pullback.snd α ((projectiveBundleChartFamily (X := goodSpace hX) E hfree).siteToChart
        (bundleBaseChart (goodSpace hX)))))).obj
      ((modulePullback D.site D.base D.base_mem
          (projectiveBundleAtlas (X := goodSpace hX) E hfree)).obj
        (projectiveBundleTwist (X := goodSpace hX) E hfree).obj))
    (k : ℤ) (Z' : IntegralClosedSubspace D.site D.base D.base_mem (yoneda.obj Wst))
    (hZ' : deltaDimension D sW Z' = k) :
    RationallyEquivalentOn.{u + 1} D sW hW k
      (subspacePointSet D.site D.base D.base_mem (yoneda.obj Wst) Z'.subspace)
      (topSegreCycle D sQ hQ sW hW hq hqp.2.1.2 N hN d k (k + d) rfl
        (flatPullbackMap D sQ hQ sW hW _ hq d hqf hqd k (k + d) rfl (integralCycle D sW k Z' hZ')))
      (integralCycle D sW k Z' hZ') := by
  obtain ⟨hR, σ, hσ⟩ :=
    hasHyperplaneChain_representedRestriction D E hfree d α V0 w0 hw0 hV0 N e
  choose τ hτ using fun j =>
    exists_representedRestrictionSection_eq D.site D.base D.base_mem _ N (σ j)
  have hinv := isInvertible_of_isInvertibleModule D.site D.base D.base_mem ⟨_, hQ.1⟩ N hN
  refine rationallyEquivalentOn_topSegreCycle_of_isHyperplaneChain D _ sQ hQ sW hW hq hqp d hqf hqd
    N hN hinv τ ?_ k Z' hZ'
  have hfun : (fun j => Stacks.Divisors.zeroScheme _
      (representedRestriction D.site D.base D.base_mem _ N) (σ j)) =
      fun j => schemeSpaceIdeal D.site D.base D.base_mem _ (vanishingLocus D sQ hQ N (τ j)) := by
    funext j
    rw [← hτ j]
    exact (schemeSpaceIdeal_zeroScheme D.site D.base D.base_mem _ N hinv (τ j)).symm
  rw [← hfun]
  exact hσ

include hX in
/-- The properties of a chart of a base change of a proper flat morphism, read off the cartesian
square. -/
theorem chart_properties {Y P : D.Ambient} {sP : P ⟶ D.space} (hP : D.IsGood sP) {π : P ⟶ X}
    (hπ : π ≫ sX = sP) (hπp : IsProper D.site D.base D.base_mem π) (d : ℕ)
    (hπf : IsFlat D.site D.base D.base_mem π)
    (hπd : HasRelativeDimension d D.site D.base D.base_mem π) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (f : Y ⟶ X) (hQ : D.IsGood (pullback.fst f π ≫ sY))
    {Wst : BigFppfOver D.site D.base D.base_mem}
    (hWa : IsAffine ((BigFppfOver.toScheme D.site D.base D.base_mem).obj Wst))
    (g : yoneda.obj Wst ⟶ Y) (hge : IsEtale D.site D.base D.base_mem g) {QW : D.Ambient}
    (hQW : IsAlgebraicSpace D.site D.base D.base_mem QW) (g' : QW ⟶ pullback f π)
    (qW : QW ⟶ yoneda.obj Wst) (hsq : IsPullback g' qW (pullback.fst f π) g) :
    ∃ (hW : D.IsGood (g ≫ sY)) (hQW' : D.IsGood (qW ≫ g ≫ sY)),
      IsProper D.site D.base D.base_mem qW ∧ IsFlat D.site D.base D.base_mem qW ∧
      HasRelativeDimension d D.site D.base D.base_mem qW ∧ IsFlat D.site D.base D.base_mem g' ∧
      HasRelativeDimension 0 D.site D.base D.base_mem g' := by
  have hWg := isGood_of_isEtale_of_isAffine D sY hY hWa g hge
  have hqp : IsProper D.site D.base D.base_mem (pullback.fst f π) :=
    isProper_of_isPullback D.site D.base D.base_mem hQ.1 hP.1 hY.1 hX.1
      (IsPullback.of_hasPullback f π).flip hπp
  have hqWp : IsProper D.site D.base D.base_mem qW :=
    isProper_of_isPullback D.site D.base D.base_mem hQW hQ.1 hWg.1 hY.1 hsq hqp
  have hQWg : D.IsGood (qW ≫ g ≫ sY) :=
    ⟨hQW, isQuasiSeparated_comp D.site D.base D.base_mem hQW hWg.1 _ _
        (isQuasiSeparated_of_isSeparated D.site D.base D.base_mem hqWp.1) hWg.2.1,
      isLocallyOfFiniteType_comp' D.site D.base D.base_mem _ _ hWg.1 D.isAlgebraicSpace
        hqWp.2.1.1 hWg.2.2⟩
  obtain ⟨-, hfq, hdq⟩ := isFlat_and_hasRelativeDimension_of_isPullback D _ hQ sY hY _ hP sX hX
    rfl hπ (IsPullback.of_hasPullback f π) d hπf hπd
  obtain ⟨-, hfqW, hdqW⟩ := isFlat_and_hasRelativeDimension_of_isPullback D _ hQWg _ hWg _ hQ _ hY
    rfl rfl hsq.flip d hfq hdq
  have hg'e : IsEtale D.site D.base D.base_mem g' :=
    isEtale_of_isPullback D.site D.base D.base_mem _ _ _ _
      (isPullback_homMk D.site D.base D.base_mem hWg.1 hQ.1 hY.1 hQW hsq.flip) hge
  exact ⟨hWg, hQWg, hqWp, hfqW, hdqW, isFlat_of_isEtale D.site D.base D.base_mem hg'e,
    hasRelativeDimension_zero_of_isEtale D.site D.base D.base_mem g' hQ.1 hg'e⟩

/-- **Injectivity of the flat pullback along a projective bundle after every base change** (the
injectivity half of Stacks 0ERV). For the projective bundle `(π : P = 𝐏(ℰ) ⟶ X, 𝒪_P(1))` of a
module of rank `d + 1` on a good `X`, the hypothesis of
`AlgebraicGeometry.Space.PrivateChern.hasInjectiveChowBaseChange_of_charts` holds on the charts
`W ×_U 𝐏(ℰ_U)` of
`AlgebraicGeometry.Space.PrivateChern.exists_affine_etale_chart_hyperplaneChain`. -/
theorem hasInjectiveChowBaseChange_projectiveBundleDatum (d : ℕ)
    (hr : IsFiniteLocallyFreeOfRank D sX hX E (d + 1)) :
    HasInjectiveChowBaseChange.{u + 1} D sX (projectiveBundleDatum E d hr).proj d := by
  let := isQuasicoherentOnSite_of_rank E hr
  have hfree := isFiniteLocallyFreeOnSite_of_rank E hr
  have := hasPullbacks_bigFppfOver D.site D.base D.base_mem
  refine hasInjectiveChowBaseChange_of_charts D (projectiveBundleDatum E d hr) ?_
  intro Y sY hY f hf hQ y p
  obtain ⟨Wst, g, α, V0, w0, hWa, hge, hy, hα, hw0, hV0⟩ :=
    exists_affine_etale_chart_hyperplaneChain D E d hr sY hY f y
  obtain ⟨g', hsq, hg's⟩ := exists_isPullback_chartBundle D E hfree f g α hα
  let c0 := (projectiveBundleChartFamily (X := goodSpace hX) E hfree).siteToChart (bundleBaseChart
      (goodSpace hX))
  obtain ⟨hWg, hQWg, hqWp, hfqW, hdqW, hg'f, hg'd⟩ := chart_properties D (hX := hX)
    (projectiveBundleDatum E d hr).isGood (projectiveBundleDatum E d hr).proj_comp
    (projectiveBundleDatum E d hr).isProper d (projectiveBundleDatum E d hr).isFlat
    (projectiveBundleDatum E d hr).hasRelativeDimension sY hY f hQ hWa g hge
    (isAlgebraicSpace_yoneda _ _ _ _) g' (yoneda.map (pullback.fst α c0)) hsq
  refine ⟨yoneda.obj Wst, yoneda.obj (pullback α c0), g ≫ sY, hWg,
    yoneda.map (pullback.fst α c0) ≫ g ≫ sY, hQWg, g, g', yoneda.map (pullback.fst α c0), hsq,
    rfl, rfl,
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ sY) hsq.w).trans (Category.assoc _ _ _)),
    hge, hy, hqWp, hfqW, hdqW, hg'f, hg'd, ?_⟩
  intro k n hkn Z' hZ'
  subst hkn
  have hcomp : (ObjectProperty.homMk g' : (⟨yoneda.obj (pullback α c0), hQWg.1⟩ :
      AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨pullback f (projectiveBundleDatum E d hr).proj,
        hQ.1⟩) ≫ p =
      representedSpaceMap D.site D.base D.base_mem (pullback.snd α c0) ≫
        projectiveBundleAtlas (X := goodSpace hX) E hfree :=
    ObjectProperty.hom_ext _ hg's
  exact rationallyEquivalentOn_topSegreCycle_chartBundle D E hfree d α V0 w0 hw0 hV0 (g ≫ sY) hWg _
    hQWg rfl hqWp hfqW hdqW _ _
    ((modulePullbackCompIso D.site D.base D.base_mem _ p).app _ ≪≫
      eqToIso (congrArg (fun φ => (modulePullback D.site D.base D.base_mem φ).obj
        (projectiveBundleTwist (X := goodSpace hX) E hfree).obj) hcomp) ≪≫
      ((modulePullbackCompIso D.site D.base D.base_mem _ _).app _).symm) k Z' hZ'

end Charts

end AlgebraicGeometry.Space.PrivateChern

end
