module

public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianChartFamilyMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleTwistDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeReadingModulePullback

/-!
# The projective bundle of an inverse image is the base change of the projective bundle

Let `g : X' ⟶ X` be a morphism of algebraic spaces over `S`, `ℰ` a finite locally free
`𝒪_X`-module and `π : P = 𝐏(ℰ) ⟶ X` its projective bundle. This file proves that the projective
bundle `𝐏(g^*ℰ) ⟶ X'` of the inverse image is the base change `P ×_X X' ⟶ X'`.

Both bundles are glued from projective bundles of schemes over étale charts. Over a chart `V`
of `X'` and a morphism `n : V ⟶ C` of schemes to a chart `C` of `X`, lying over `g`, the
readings of `g^*ℰ` on `V` and of `ℰ` on `C` are identified along `n`
(`AlgebraicGeometry.Space.chartBundleModulePullbackIso`, from the compatibility of readings with
inverse images of `AlgebraicGeometry.Space.schemeReadingModulePullbackIso`), so the chart bundle
`𝐏(g^*ℰ|_V)` is the base change of `𝐏(ℰ|_C)` along `n` (Stacks 01O3,
`AlgebraicGeometry.Space.chartBundlePullbackMap`). These comparison maps are compatible with the
morphisms of chart bundles on either side.

The chart `W = U' ×_X U` of `X'`, for `U'` and `U` the presenting charts of `X'` and `X`, maps to
`U`, so `𝐏(g^*ℰ|_W) ⟶ 𝐏(ℰ|_U) ⟶ P` is defined; it identifies the two morphisms from the bundle
over the kernel pair of `W`, and exhibits `𝐏(g^*ℰ|_W)` as `P ×_X W`. The isomorphism criterion of
`StacksFrontier.AlgebraicGeometry.Spaces.CartesianChartFamilyMorphisms` then identifies `P ×_X X'`
with the bundle of `g^*ℰ` glued over `W`, which is `𝐏(g^*ℰ)`.

## Main definitions

* `AlgebraicGeometry.Space.chartBundleModulePullbackIso`: `(g^*ℰ)|_V ≅ n^*(ℰ|_C)`.
* `AlgebraicGeometry.Space.chartBundlePullbackMap`: the comparison `𝐏(g^*ℰ|_V) ⟶ 𝐏(ℰ|_C)`.

## Main results

* `AlgebraicGeometry.Space.isPullback_chartBundlePullbackMap`: it is a base change.
* `AlgebraicGeometry.Space.chartBundleMap_comp_chartBundlePullbackMap` and
  `AlgebraicGeometry.Space.chartBundlePullbackMap_comp_chartBundleMap`: its compatibility with the
  morphisms of chart bundles.

## References

* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 0ERT](https://stacks.math.columbia.edu/tag/0ERT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X X' : AlgebraicSpaces B S hS}
  (g : X' ⟶ X) (E : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]

/-- The inverse image of a quasi-coherent module is quasi-coherent. -/
instance isQuasicoherentOnSite_modulePullback_obj_instance :
    ((modulePullback B S hS g).obj E).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_obj_of_isQuasicoherentOnSite g E hE

/-! ### The chart modules of the inverse image along a morphism of charts over `g` -/

section ChartComparison

variable {V : SmallEtale B S hS X'.1} {C : SmallEtale B S hS X.1}

/-- The morphism of chart schemes underlying a morphism of the site between the objects of two
charts, in the spelling of the chart schemes. -/
abbrev chartSiteSchemeHom {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V : SmallEtale B S hS F}
    {C : SmallEtale B S hS G}
    (n : (SmallEtale.toOver B S hS F).obj V ⟶ (SmallEtale.toOver B S hS G).obj C) :
    chartScheme V ⟶ chartScheme C :=
  _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) n.left

/-- **The chart module of `g^*ℰ` on a chart `V` of `X'` is the pullback of the chart module of
`ℰ` on a chart `C` of `X`** along a morphism `n : V ⟶ C` of the site lying over `g`. -/
def chartBundleModulePullbackIso
    (n : (SmallEtale.toOver B S hS X'.1).obj V ⟶ (SmallEtale.toOver B S hS X.1).obj C)
    (w : representedSpaceMap B S hS n ≫ chartToSpace B S hS X C = chartToSpace B S hS X' V ≫ g) :
    chartBundleModule ((modulePullback B S hS g).obj E) V ≅
      (Scheme.Modules.pullback (chartSiteSchemeHom n)).obj (chartBundleModule E C) :=
  schemeReadingModulePullbackIso g E (chartToSpace B S hS X' V) ≪≫
    (schemeReadingPullbackIso E hE n w).symm

/-- **The comparison `𝐏(g^*ℰ|_V) ⟶ 𝐏(ℰ|_C)`** of chart bundles over a morphism `n : V ⟶ C` of
the site lying over `g`: the base change comparison of projective bundles of Stacks 01O3 along
`n`, for the identification of `AlgebraicGeometry.Space.chartBundleModulePullbackIso`. -/
def chartBundlePullbackMap
    (n : (SmallEtale.toOver B S hS X'.1).obj V ⟶ (SmallEtale.toOver B S hS X.1).obj C)
    (w : representedSpaceMap B S hS n ≫ chartToSpace B S hS X C = chartToSpace B S hS X' V ≫ g) :
    chartBundle ((modulePullback B S hS g).obj E) V ⟶ chartBundle E C :=
  Stacks.RelativeProj.projectiveBundleBaseChange (chartSiteSchemeHom n) (chartBundleModule E C)
    (chartBundleModule ((modulePullback B S hS g).obj E) V)
    (chartBundleModulePullbackIso g E n w)

/-- **`𝐏(g^*ℰ|_V) = 𝐏(ℰ|_C) ×_C V`** (Stacks 01O3). -/
theorem isPullback_chartBundlePullbackMap
    (n : (SmallEtale.toOver B S hS X'.1).obj V ⟶ (SmallEtale.toOver B S hS X.1).obj C)
    (w : representedSpaceMap B S hS n ≫ chartToSpace B S hS X C = chartToSpace B S hS X' V ≫ g) :
    IsPullback (chartBundlePullbackMap g E n w)
      (chartBundleToChart ((modulePullback B S hS g).obj E) V) (chartBundleToChart E C)
      (chartSiteSchemeHom n) :=
  Stacks.RelativeProj.isPullback_projectiveBundleBaseChange _ _ _ _

/-- The structure morphisms to `X` of a chart `V'` of `X'` with a morphism `q : V' ⟶ V`, read
through `g`. -/
theorem representedSpaceMap_toOver_map_comp_chartToSpace_comp {V' : SmallEtale B S hS X'.1}
    (q : V' ⟶ V) :
    representedSpaceMap B S hS ((SmallEtale.toOver B S hS X'.1).map q) ≫
        (chartToSpace B S hS X' V ≫ g) = chartToSpace B S hS X' V' ≫ g :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ g) (representedSpaceMap_toOver_map_comp_chartToSpace q))

/-- The abstract shape of the compatibility with the morphisms of chart bundles of `g^*ℰ`. -/
private theorem shape_comp_left {C₀ D₀ : Type*} [Category C₀] [Category D₀] (Φ : C₀ ⥤ D₀)
    {x₀ y₀ z₀ : C₀} {c d f : D₀} (P₀ : x₀ ≅ y₀) (M₀ : z₀ ≅ y₀) (Q : Φ.obj y₀ ≅ d)
    (K : Φ.obj x₀ ≅ c) (L : c ≅ d) (N : Φ.obj z₀ ≅ f) (O : f ≅ d)
    (hcomp : Φ.mapIso P₀ ≪≫ Q = K ≪≫ L) (hnat : Φ.mapIso M₀ ≪≫ Q = N ≪≫ O) :
    K.hom ≫ (O ≪≫ L.symm).inv = Φ.map (M₀ ≪≫ P₀.symm).inv ≫ N.hom := by
  have h₁ := congrArg Iso.hom hcomp
  have h₂ := congrArg Iso.hom hnat
  simp only [Iso.trans_hom, Functor.mapIso_hom] at h₁ h₂
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.map_comp]
  rw [← Category.assoc, ← h₁, Category.assoc, Category.assoc]
  congr 1
  rw [← cancel_epi (Φ.map M₀.hom), ← Category.assoc, h₂, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, ← Category.assoc, ← Φ.map_comp, Iso.hom_inv_id, Φ.map_id, Category.id_comp]

/-- **The comparisons are compatible with the morphisms of chart bundles of `g^*ℰ`**: along a
morphism `q : V' ⟶ V` of charts of `X'`, `𝐏(g^*ℰ|_{V'}) ⟶ 𝐏(g^*ℰ|_V) ⟶ 𝐏(ℰ|_C)` is the
comparison over `V' ⟶ V ⟶ C`. -/
theorem chartBundleMap_comp_chartBundlePullbackMap {V' : SmallEtale B S hS X'.1} (q : V' ⟶ V)
    (n : (SmallEtale.toOver B S hS X'.1).obj V ⟶ (SmallEtale.toOver B S hS X.1).obj C)
    (w : representedSpaceMap B S hS n ≫ chartToSpace B S hS X C = chartToSpace B S hS X' V ≫ g)
    (w' : representedSpaceMap B S hS ((SmallEtale.toOver B S hS X'.1).map q ≫ n) ≫
        chartToSpace B S hS X C = chartToSpace B S hS X' V' ≫ g) :
    chartBundleMap ((modulePullback B S hS g).obj E) q ≫ chartBundlePullbackMap g E n w =
      chartBundlePullbackMap g E ((SmallEtale.toOver B S hS X'.1).map q ≫ n) w' := by
  refine Stacks.RelativeProj.projectiveBundleBaseChange_comp _ _ _ _ _ _ _ _ ?_
  -- the composition law of the readings of `ℰ`, and the compatibility of the readings of `g^*ℰ`
  -- and `ℰ`
  exact shape_comp_left _ _ _ _ _ _ _ _
    (schemeReadingPullbackIso_comp E hE ((SmallEtale.toOver B S hS X'.1).map q) n w
      (representedSpaceMap_toOver_map_comp_chartToSpace_comp g q) w')
    (schemeReadingModulePullbackIso_naturality g E hE
      ((SmallEtale.toOver B S hS X'.1).map q) (representedSpaceMap_toOver_map_comp_chartToSpace q)
      (representedSpaceMap_toOver_map_comp_chartToSpace_comp g q))

/-- The abstract shape of the compatibility with the morphisms of chart bundles of `ℰ`. -/
private theorem shape_comp_right {C₀ D₀ : Type*} [Category C₀] [Category D₀] (Φ : C₀ ⥤ D₀)
    {x₀ y₀ : C₀} {c d f : D₀} (Q₀ : x₀ ≅ y₀) (P : Φ.obj y₀ ≅ d) (K : Φ.obj x₀ ≅ c)
    (L : c ≅ d) (O : f ≅ d) (hcomp : Φ.mapIso Q₀ ≪≫ P = K ≪≫ L) :
    K.hom ≫ (O ≪≫ L.symm).inv = Φ.map Q₀.hom ≫ (O ≪≫ P.symm).inv := by
  have h₁ := congrArg Iso.hom hcomp
  simp only [Iso.trans_hom, Functor.mapIso_hom] at h₁
  simp only [Iso.trans_inv, Iso.symm_inv]
  rw [← Category.assoc, ← h₁, Category.assoc]

/-- **The comparisons are compatible with the morphisms of chart bundles of `ℰ`**: along a
morphism `c : C ⟶ C'` of charts of `X`, `𝐏(g^*ℰ|_V) ⟶ 𝐏(ℰ|_C) ⟶ 𝐏(ℰ|_{C'})` is the comparison
over `V ⟶ C ⟶ C'`. -/
theorem chartBundlePullbackMap_comp_chartBundleMap {C' : SmallEtale B S hS X.1} (c : C ⟶ C')
    (n : (SmallEtale.toOver B S hS X'.1).obj V ⟶ (SmallEtale.toOver B S hS X.1).obj C)
    (w : representedSpaceMap B S hS n ≫ chartToSpace B S hS X C = chartToSpace B S hS X' V ≫ g)
    (w' : representedSpaceMap B S hS (n ≫ (SmallEtale.toOver B S hS X.1).map c) ≫
        chartToSpace B S hS X C' = chartToSpace B S hS X' V ≫ g) :
    chartBundlePullbackMap g E n w ≫ chartBundleMap E c =
      chartBundlePullbackMap g E (n ≫ (SmallEtale.toOver B S hS X.1).map c) w' := by
  refine Stacks.RelativeProj.projectiveBundleBaseChange_comp _ _ _ _ _ _ _ _ ?_
  exact shape_comp_right _ _ _ _ _ _
    (schemeReadingPullbackIso_comp E hE n ((SmallEtale.toOver B S hS X.1).map c)
      (representedSpaceMap_toOver_map_comp_chartToSpace c) w w')

end ChartComparison

/-! ### The comparison maps in the site -/

section Site

variable (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)

include hfree in
/-- The inverse image of a finite locally free module is finite locally free. -/
theorem isFiniteLocallyFreeOnSite_modulePullback_obj :
    SheafOfModules.IsFiniteLocallyFreeOnSite ((modulePullback B S hS g).obj E) :=
  isFiniteLocallyFreeOnSite_modulePullback B S hS g E hE hfree

variable {V : SmallEtale B S hS X'.1} {C : SmallEtale B S hS X.1}

/-- **The comparison `𝐏(g^*ℰ|_V) ⟶ 𝐏(ℰ|_C)` as a morphism of the site**, between the objects of
the two cartesian chart families. -/
def chartBundlePullbackSiteMap
    (n : (SmallEtale.toOver B S hS X'.1).obj V ⟶ (SmallEtale.toOver B S hS X.1).obj C)
    (w : representedSpaceMap B S hS n ≫ chartToSpace B S hS X C = chartToSpace B S hS X' V ≫ g) :
    (projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).site V ⟶
      (projectiveBundleChartFamily E hfree).site C :=
  Over.homMk (ObjectProperty.homMk (chartBundlePullbackMap g E n w)) (by
    apply ObjectProperty.hom_ext
    change chartBundlePullbackMap g E n w ≫ chartBundleToChart E C ≫
        B.inclusion.map ((SmallEtale.toOver B S hS X.1).obj C).hom =
      chartBundleToChart ((modulePullback B S hS g).obj E) V ≫
        B.inclusion.map ((SmallEtale.toOver B S hS X'.1).obj V).hom
    rw [← Category.assoc, (isPullback_chartBundlePullbackMap g E n w).w, Category.assoc]
    congr 1
    change B.inclusion.map n.left ≫ B.inclusion.map ((SmallEtale.toOver B S hS X.1).obj C).hom =
      B.inclusion.map ((SmallEtale.toOver B S hS X'.1).obj V).hom
    rw [← B.inclusion.map_comp, Over.w])

/-- **The square of the comparison over `n`, read in the site, is cartesian.** -/
theorem isPullback_chartBundlePullbackSiteMap
    (n : (SmallEtale.toOver B S hS X'.1).obj V ⟶ (SmallEtale.toOver B S hS X.1).obj C)
    (w : representedSpaceMap B S hS n ≫ chartToSpace B S hS X C = chartToSpace B S hS X' V ≫ g) :
    IsPullback (chartBundlePullbackSiteMap g E hfree n w)
      ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteToChart V)
      ((projectiveBundleChartFamily E hfree).siteToChart C) n :=
  IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS)
    (isPullback_chartBundlePullbackMap g E n w)

/-- The comparison in the site depends on the morphism `n` only. -/
theorem chartBundlePullbackSiteMap_congr
    {n n' : (SmallEtale.toOver B S hS X'.1).obj V ⟶ (SmallEtale.toOver B S hS X.1).obj C}
    (h : n = n')
    (w : representedSpaceMap B S hS n ≫ chartToSpace B S hS X C = chartToSpace B S hS X' V ≫ g)
    (w' : representedSpaceMap B S hS n' ≫ chartToSpace B S hS X C =
      chartToSpace B S hS X' V ≫ g) :
    chartBundlePullbackSiteMap g E hfree n w = chartBundlePullbackSiteMap g E hfree n' w' := by
  subst h
  rfl

/-- The compatibility with the morphisms of chart bundles of `g^*ℰ`, in the site. -/
theorem siteMap_comp_chartBundlePullbackSiteMap {V' : SmallEtale B S hS X'.1} (q : V' ⟶ V)
    (n : (SmallEtale.toOver B S hS X'.1).obj V ⟶ (SmallEtale.toOver B S hS X.1).obj C)
    (w : representedSpaceMap B S hS n ≫ chartToSpace B S hS X C = chartToSpace B S hS X' V ≫ g)
    (w' : representedSpaceMap B S hS ((SmallEtale.toOver B S hS X'.1).map q ≫ n) ≫
        chartToSpace B S hS X C = chartToSpace B S hS X' V' ≫ g) :
    (projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteMap q ≫
        chartBundlePullbackSiteMap g E hfree n w =
      chartBundlePullbackSiteMap g E hfree ((SmallEtale.toOver B S hS X'.1).map q ≫ n) w' :=
  Over.OverMorphism.ext
    (ObjectProperty.hom_ext _ (chartBundleMap_comp_chartBundlePullbackMap g E q n w w'))

/-- The compatibility with the morphisms of chart bundles of `ℰ`, in the site. -/
theorem chartBundlePullbackSiteMap_comp_siteMap {C' : SmallEtale B S hS X.1} (c : C ⟶ C')
    (n : (SmallEtale.toOver B S hS X'.1).obj V ⟶ (SmallEtale.toOver B S hS X.1).obj C)
    (w : representedSpaceMap B S hS n ≫ chartToSpace B S hS X C = chartToSpace B S hS X' V ≫ g)
    (w' : representedSpaceMap B S hS (n ≫ (SmallEtale.toOver B S hS X.1).map c) ≫
        chartToSpace B S hS X C' = chartToSpace B S hS X' V ≫ g) :
    chartBundlePullbackSiteMap g E hfree n w ≫ (projectiveBundleChartFamily E hfree).siteMap c =
      chartBundlePullbackSiteMap g E hfree (n ≫ (SmallEtale.toOver B S hS X.1).map c) w' :=
  Over.OverMorphism.ext
    (ObjectProperty.hom_ext _ (chartBundlePullbackMap_comp_chartBundleMap g E c n w w'))

/-- The condition that `n` lies over `g`, after precomposition with a morphism of charts of
`X'`. -/
theorem chartToSpace_comp_of_toOver_map_comp {V' : SmallEtale B S hS X'.1} (q : V' ⟶ V)
    (n : (SmallEtale.toOver B S hS X'.1).obj V ⟶ (SmallEtale.toOver B S hS X.1).obj C)
    (w : representedSpaceMap B S hS n ≫ chartToSpace B S hS X C = chartToSpace B S hS X' V ≫ g) :
    representedSpaceMap B S hS ((SmallEtale.toOver B S hS X'.1).map q ≫ n) ≫
      chartToSpace B S hS X C = chartToSpace B S hS X' V' ≫ g := by
  refine ObjectProperty.hom_ext _ ?_
  have hw : yoneda.map n ≫ C.obj.hom = V.obj.hom ≫ g.hom := congrArg (fun m => m.hom) w
  show yoneda.map ((SmallEtale.toOver B S hS X'.1).map q ≫ n) ≫ C.obj.hom = V'.obj.hom ≫ g.hom
  rw [Functor.map_comp, Category.assoc, hw, ← Category.assoc, yoneda_map_toOver_map_comp_hom]

end Site

/-! ### The chart `U' ×_X U` of `X'` -/

section BaseChangeChart

/-- The presenting chart of `X'` followed by `g`. -/
abbrev presentingFiberChartMap : yoneda.obj (bundleBaseChart X').obj.left ⟶ X.1 :=
  (bundleBaseChart X').obj.hom ≫ g.hom

/-- The object of the site representing `U' ×_X U`. -/
abbrev presentingFiberChartObj : BigFppfOver B S hS :=
  (bundleBaseChart X).property.1.pullback (presentingFiberChartMap g)

/-- The projection `U' ×_X U ⟶ U'`. -/
abbrev presentingFiberChartSnd : presentingFiberChartObj g ⟶ (bundleBaseChart X').obj.left :=
  (bundleBaseChart X).property.1.snd (presentingFiberChartMap g)

/-- The projection `U' ×_X U ⟶ U`. -/
abbrev presentingFiberChartFst : presentingFiberChartObj g ⟶ (bundleBaseChart X).obj.left :=
  yoneda.preimage ((bundleBaseChart X).property.1.fst (presentingFiberChartMap g))

/-- The square of `U' ×_X U`. -/
theorem isPullback_presentingFiberChart :
    IsPullback (yoneda.map (presentingFiberChartFst g)) (yoneda.map (presentingFiberChartSnd g))
      (bundleBaseChart X).obj.hom (presentingFiberChartMap g) := by
  simpa [presentingFiberChartFst, presentingFiberChartSnd] using
    (bundleBaseChart X).property.1.isPullback (presentingFiberChartMap g)

/-- The projection `U' ×_X U ⟶ U'` is étale, as a base change of the étale chart `U ⟶ X`. -/
theorem etale_presentingFiberChartSnd :
    Etale ((BigFppfOver.toScheme B S hS).map (presentingFiberChartSnd g)) :=
  (bundleBaseChart X).property.2 (presentingFiberChartMap g) _ _
    ((bundleBaseChart X).property.1.isPullback (presentingFiberChartMap g))

/-- The projection `U' ×_X U ⟶ U'` is surjective, as a base change of the surjective chart
`U ⟶ X`. -/
theorem surjective_presentingFiberChartSnd :
    Surjective ((BigFppfOver.toScheme B S hS).map (presentingFiberChartSnd g)) :=
  (surjective_projectiveBundlePresentation X).2 (presentingFiberChartMap g) _ _
    ((bundleBaseChart X).property.1.isPullback (presentingFiberChartMap g))

/-- **The étale chart `W = U' ×_X U` of `X'`.** -/
def presentingFiberChart : SmallEtale B S hS X'.1 :=
  ⟨CostructuredArrow.mk (yoneda.map (presentingFiberChartSnd g) ≫ (bundleBaseChart X').obj.hom),
    etale_comp_of_scheme B S hS _ _ (etale_presentingFiberChartSnd g) (bundleBaseChart X').property⟩

/-- The morphism of charts `W ⟶ U'`. -/
def presentingFiberChartHom : presentingFiberChart g ⟶ bundleBaseChart X' :=
  ObjectProperty.homMk (CostructuredArrow.homMk (presentingFiberChartSnd g) rfl)

/-- **The chart `W` is surjective**: `W ⟶ U'` is a base change of the surjective `U ⟶ X`, and
`U' ⟶ X'` is surjective. -/
theorem surjective_presentingFiberChart :
    MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
      (presentingFiberChart g).obj.hom := by
  have := inverseImage_isStableUnderBaseChange B S hS
    (inferInstance : MorphismProperty.IsStableUnderBaseChange (@Surjective.{u}))
  have := inverseImage_isStableUnderComposition B S hS surjective_isStableUnderComposition.{u}
  exact MorphismProperty.comp_mem _ _ _
    ((presheaf_yoneda_map_iff B S hS inferInstance (presentingFiberChartSnd g)).2
      (surjective_presentingFiberChartSnd g))
    (surjective_projectiveBundlePresentation X')

/-- The projection `W ⟶ U`, between the objects of the two charts. -/
abbrev presentingFiberChartFstOver :
    (SmallEtale.toOver B S hS X'.1).obj (presentingFiberChart g) ⟶
      (SmallEtale.toOver B S hS X.1).obj (bundleBaseChart X) :=
  presentingFiberChartFst g

/-- **`W ⟶ U` lies over `g`.** -/
theorem presentingFiberChartFst_w :
    representedSpaceMap B S hS (presentingFiberChartFstOver g) ≫
        chartToSpace B S hS X (bundleBaseChart X) =
      chartToSpace B S hS X' (presentingFiberChart g) ≫ g := by
  refine ObjectProperty.hom_ext _ ?_
  show yoneda.map (presentingFiberChartFst g) ≫ (bundleBaseChart X).obj.hom =
    (yoneda.map (presentingFiberChartSnd g) ≫ (bundleBaseChart X').obj.hom) ≫ g.hom
  rw [(isPullback_presentingFiberChart g).w, Category.assoc]

end BaseChangeChart

/-! ### The morphism from the chart bundle over `W` to the projective bundle -/

section ToBundle

variable (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)

/-- The cartesian chart family of the projective bundle of `g^*ℰ`. -/
abbrev pullbackChartFamily : CartesianChartFamily X' :=
  projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
    (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)

/-- **The morphism `𝐏(g^*ℰ|_W) ⟶ 𝐏(ℰ|_U) ⟶ P`.** -/
abbrev presentingFiberChartToBundle :
    yoneda.obj ((pullbackChartFamily g E hfree).site (presentingFiberChart g)) ⟶
      (projectiveBundle E hfree).1 :=
  yoneda.map (chartBundlePullbackSiteMap g E hfree (presentingFiberChartFstOver g)
    (presentingFiberChartFst_w g)) ≫
    projectiveBundleChart E hfree

/-- The morphism `𝐏(g^*ℰ|_W) ⟶ P` lies over `W ⟶ X' ⟶ X`. -/
theorem presentingFiberChartToBundle_comp :
    presentingFiberChartToBundle g E hfree ≫ (projectiveBundleProj E hfree).hom =
      yoneda.map ((pullbackChartFamily g E hfree).siteToChart (presentingFiberChart g)) ≫
        (presentingFiberChart g).obj.hom ≫ g.hom := by
  rw [Category.assoc, ← projectiveBundleChart_comm E hfree, ← Category.assoc, ← Functor.map_comp,
    (isPullback_chartBundlePullbackSiteMap g E hfree _ (presentingFiberChartFst_w g)).w,
    Functor.map_comp, Category.assoc]
  exact congrArg (_ ≫ ·) ((isPullback_presentingFiberChart g).w.trans (Category.assoc _ _ _).symm)

/-- **`𝐏(g^*ℰ|_W) = P ×_X W`**: the comparison square over `W ⟶ U` pasted with `P_U = P ×_X U`. -/
theorem isPullback_presentingFiberChartToBundle :
    IsPullback (presentingFiberChartToBundle g E hfree)
      (yoneda.map ((pullbackChartFamily g E hfree).siteToChart (presentingFiberChart g)))
      (projectiveBundleProj E hfree).hom ((presentingFiberChart g).obj.hom ≫ g.hom) := by
  have h₁ := (isPullback_chartBundlePullbackSiteMap g E hfree (presentingFiberChartFstOver g)
    (presentingFiberChartFst_w g)).map yoneda
  have h₂ := isPullback_projectiveBundleProj E hfree
  have hb : yoneda.map (presentingFiberChartFstOver g) ≫ (bundleBaseChart X).obj.hom =
      (presentingFiberChart g).obj.hom ≫ g.hom :=
    (isPullback_presentingFiberChart g).w.trans (Category.assoc _ _ _).symm
  exact hb ▸ h₁.paste_horiz h₂

/-- The condition that `n` lies over `g`, after postcomposition with a morphism of charts of
`X`. -/
theorem chartToSpace_comp_of_comp_toOver_map {V : SmallEtale B S hS X'.1}
    {C C' : SmallEtale B S hS X.1} (c : C ⟶ C')
    (n : (SmallEtale.toOver B S hS X'.1).obj V ⟶ (SmallEtale.toOver B S hS X.1).obj C)
    (w : representedSpaceMap B S hS n ≫ chartToSpace B S hS X C = chartToSpace B S hS X' V ≫ g) :
    representedSpaceMap B S hS (n ≫ (SmallEtale.toOver B S hS X.1).map c) ≫
      chartToSpace B S hS X C' = chartToSpace B S hS X' V ≫ g := by
  refine ObjectProperty.hom_ext _ ?_
  have hw : yoneda.map n ≫ C.obj.hom = V.obj.hom ≫ g.hom := congrArg (fun m => m.hom) w
  show yoneda.map (n ≫ (SmallEtale.toOver B S hS X.1).map c) ≫ C'.obj.hom = V.obj.hom ≫ g.hom
  rw [Functor.map_comp, Category.assoc, yoneda_map_toOver_map_comp_hom, hw]

/-- **The morphism `𝐏(g^*ℰ|_W) ⟶ P` identifies the two morphisms from the bundle over the kernel
pair of `W`**: the two composites `W ×_{X'} W ⇉ W ⟶ U` factor through the relation chart
`R = U ×_X U`, and the atlas `P_U ⟶ P` identifies the two morphisms `P_R ⇉ P_U`. -/
theorem siteMap_comp_presentingFiberChartToBundle :
    yoneda.map ((pullbackChartFamily g E hfree).siteMap
        (chartKernelPairFstHom (presentingFiberChart g))) ≫ presentingFiberChartToBundle g E hfree =
      yoneda.map ((pullbackChartFamily g E hfree).siteMap
          (chartKernelPairSndHom (presentingFiberChart g))) ≫
        presentingFiberChartToBundle g E hfree := by
  set W := presentingFiberChart g with hW
  set W₂ := chartKernelPair W with hW₂
  set q₁ := chartKernelPairFstHom W with hq₁
  set q₂ := chartKernelPairSndHom W with hq₂
  let pr₁ := presentationRelationTargetHom (projectiveBundlePresentation X)
  let pr₂ := presentationRelationSourceHom (projectiveBundlePresentation X)
  have hsq := isPullback_projectiveBundlePresentation X
  let n₁ := (SmallEtale.toOver B S hS X'.1).map q₁ ≫ presentingFiberChartFstOver g
  let n₂ := (SmallEtale.toOver B S hS X'.1).map q₂ ≫ presentingFiberChartFstOver g
  have e : ∀ q : W₂ ⟶ W, yoneda.map ((SmallEtale.toOver B S hS X'.1).map q ≫
      presentingFiberChartFstOver g) ≫ (bundleBaseChart X).obj.hom = W₂.obj.hom ≫ g.hom :=
    fun q => congrArg (fun m => m.hom)
      (chartToSpace_comp_of_toOver_map_comp g q _ (presentingFiberChartFst_w g))
  let l : (SmallEtale.toOver B S hS X'.1).obj W₂ ⟶
      (SmallEtale.toOver B S hS X.1).obj (bundleRelationChart X) :=
    yoneda.preimage (hsq.lift (yoneda.map n₁) (yoneda.map n₂) ((e q₁).trans (e q₂).symm))
  have hl₁ : l ≫ (SmallEtale.toOver B S hS X.1).map pr₁ = n₁ := by
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_preimage, hsq.lift_fst]
  have hl₂ : l ≫ (SmallEtale.toOver B S hS X.1).map pr₂ = n₂ := by
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_preimage, hsq.lift_snd]
  have wl : representedSpaceMap B S hS l ≫ chartToSpace B S hS X (bundleRelationChart X) =
      chartToSpace B S hS X' W₂ ≫ g := by
    refine ObjectProperty.hom_ext _ ?_
    show yoneda.map l ≫ (bundleRelationChart X).obj.hom = W₂.obj.hom ≫ g.hom
    rw [← yoneda_map_toOver_map_comp_hom pr₂, ← Category.assoc, ← Functor.map_comp, hl₂, e q₂]
  have key : ∀ (q : W₂ ⟶ W) (pr : bundleRelationChart X ⟶ bundleBaseChart X)
      (hl : l ≫ (SmallEtale.toOver B S hS X.1).map pr =
        (SmallEtale.toOver B S hS X'.1).map q ≫ presentingFiberChartFstOver g),
      yoneda.map ((pullbackChartFamily g E hfree).siteMap q) ≫
          presentingFiberChartToBundle g E hfree =
        yoneda.map (chartBundlePullbackSiteMap g E hfree l wl) ≫
          yoneda.map ((projectiveBundleChartFamily E hfree).siteMap pr) ≫
            projectiveBundleChart E hfree := by
    intro q pr hl
    rw [← Category.assoc, ← Functor.map_comp, siteMap_comp_chartBundlePullbackSiteMap g E hfree q _
      (presentingFiberChartFst_w g)
      (chartToSpace_comp_of_toOver_map_comp g q _ (presentingFiberChartFst_w g)),
      chartBundlePullbackSiteMap_congr g E hfree hl.symm _
        (chartToSpace_comp_of_comp_toOver_map g pr l wl),
      ← chartBundlePullbackSiteMap_comp_siteMap g E hfree pr l wl, Functor.map_comp,
      Category.assoc]
  rw [key q₁ pr₁ hl₁, key q₂ pr₂ hl₂]
  congr 1
  exact (projectiveBundleChartFamily E hfree).siteMap_comp_quotientChart pr₁ pr₂ hsq

end ToBundle

/-! ### The isomorphism `𝐏(g^*ℰ) ≅ P ×_X X'` -/

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_ProjectiveBundleSpaceBaseChange
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_ProjectiveBundleSpaceBaseChange
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_ProjectiveBundleSpaceBaseChange B S hS).has_limit _

section Iso

variable (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)

/-- **The base change `P ×_X X'` of the projective bundle**, as an algebraic space. -/
abbrev projectiveBundleFiberProduct : AlgebraicSpaces B S hS :=
  AlgebraicSpaces.fiberProduct B S hS (projectiveBundleProj E hfree) g

/-- Its projection to `X'`. -/
abbrev projectiveBundleFiberProductProj : projectiveBundleFiberProduct g E hfree ⟶ X' :=
  ObjectProperty.homMk (pullback.snd (projectiveBundleProj E hfree).hom g.hom)

/-- Its projection to `P`. -/
abbrev projectiveBundleFiberProductFst :
    projectiveBundleFiberProduct g E hfree ⟶ projectiveBundle E hfree :=
  ObjectProperty.homMk (pullback.fst (projectiveBundleProj E hfree).hom g.hom)

/-- The morphism `𝐏(g^*ℰ|_W) ⟶ P ×_X X'`. -/
def presentingFiberChartToFiberProduct :
    yoneda.obj ((pullbackChartFamily g E hfree).site (presentingFiberChart g)) ⟶
      (projectiveBundleFiberProduct g E hfree).1 :=
  pullback.lift (presentingFiberChartToBundle g E hfree)
    (yoneda.map ((pullbackChartFamily g E hfree).siteToChart (presentingFiberChart g)) ≫
      (presentingFiberChart g).obj.hom)
    ((presentingFiberChartToBundle_comp g E hfree).trans (Category.assoc _ _ _).symm)

/-- The composite of `𝐏(g^*ℰ|_W) ⟶ P ×_X X'` with the projection to `P` is
`presentingFiberChartToBundle`. -/
@[reassoc (attr := simp)]
theorem presentingFiberChartToFiberProduct_fst :
    presentingFiberChartToFiberProduct g E hfree ≫
        pullback.fst (projectiveBundleProj E hfree).hom g.hom =
      presentingFiberChartToBundle g E hfree :=
  pullback.lift_fst _ _ _

/-- The composite of `𝐏(g^*ℰ|_W) ⟶ P ×_X X'` with the projection to `X'` is the projection
`𝐏(g^*ℰ|_W) ⟶ W` followed by `W ⟶ X'`. -/
@[reassoc (attr := simp)]
theorem presentingFiberChartToFiberProduct_snd :
    presentingFiberChartToFiberProduct g E hfree ≫
        pullback.snd (projectiveBundleProj E hfree).hom g.hom =
      yoneda.map ((pullbackChartFamily g E hfree).siteToChart (presentingFiberChart g)) ≫
        (presentingFiberChart g).obj.hom :=
  pullback.lift_snd _ _ _

/-- The morphism `𝐏(g^*ℰ|_W) ⟶ P ×_X X'` identifies the two morphisms of the kernel pair. -/
theorem siteMap_comp_presentingFiberChartToFiberProduct :
    yoneda.map ((pullbackChartFamily g E hfree).siteMap
          (chartKernelPairFstHom (presentingFiberChart g))) ≫
        presentingFiberChartToFiberProduct g E hfree =
      yoneda.map ((pullbackChartFamily g E hfree).siteMap
          (chartKernelPairSndHom (presentingFiberChart g))) ≫
        presentingFiberChartToFiberProduct g E hfree := by
  apply pullback.hom_ext
  · refine (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (presentingFiberChartToFiberProduct_fst g E hfree)).trans ?_)
    refine Eq.trans ?_ ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) (presentingFiberChartToFiberProduct_fst g E hfree))).symm
    exact siteMap_comp_presentingFiberChartToBundle g E hfree
  · refine (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (presentingFiberChartToFiberProduct_snd g E hfree)).trans ?_)
    refine Eq.trans ?_ ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) (presentingFiberChartToFiberProduct_snd g E hfree))).symm
    exact ((pullbackChartFamily g E hfree).siteMap_comp_siteToSpace _).trans
      ((pullbackChartFamily g E hfree).siteMap_comp_siteToSpace _).symm

/-- **`𝐏(g^*ℰ|_W) = (P ×_X X') ×_{X'} W`.** -/
theorem isPullback_presentingFiberChartToFiberProduct :
    IsPullback (presentingFiberChartToFiberProduct g E hfree)
      (yoneda.map ((pullbackChartFamily g E hfree).siteToChart (presentingFiberChart g)))
      (pullback.snd (projectiveBundleProj E hfree).hom g.hom) (presentingFiberChart g).obj.hom :=
  IsPullback.of_right
    ((presentingFiberChartToFiberProduct_fst g E hfree).symm ▸
      isPullback_presentingFiberChartToBundle g E hfree)
    (presentingFiberChartToFiberProduct_snd g E hfree)
    (IsPullback.of_hasPullback _ _)

/-- The morphism from the bundle of `g^*ℰ` glued over the kernel pair of `W` to `P ×_X X'`. -/
def projectiveBundleOverChartToFiberProduct :
    (pullbackChartFamily g E hfree).quotient (chartKernelPairFstHom (presentingFiberChart g))
        (chartKernelPairSndHom (presentingFiberChart g)) (isPullback_chartKernelPairHom _) ⟶
      projectiveBundleFiberProduct g E hfree :=
  (pullbackChartFamily g E hfree).quotientDesc _ _ _ _
    (presentingFiberChartToFiberProduct g E hfree)
    (siteMap_comp_presentingFiberChartToFiberProduct g E hfree)

/-- **The bundle of `g^*ℰ` glued over the kernel pair of `W` is `P ×_X X'`.** -/
instance isIso_projectiveBundleOverChartToFiberProduct_hom :
    IsIso (projectiveBundleOverChartToFiberProduct g E hfree).hom :=
  (pullbackChartFamily g E hfree).isIso_quotientDesc_hom _ _ _ _ _ _
    (projectiveBundleFiberProductProj g E hfree)
    (isPullback_presentingFiberChartToFiberProduct g E hfree) (surjective_presentingFiberChart g)

/-- The morphism from the bundle of `g^*ℰ` glued over the kernel pair of `W` to the projective
bundle of `g^*ℰ`, glued over the presentation of `X'`. -/
def projectiveBundleOverChartToProjectiveBundle :
    (pullbackChartFamily g E hfree).quotient (chartKernelPairFstHom (presentingFiberChart g))
        (chartKernelPairSndHom (presentingFiberChart g)) (isPullback_chartKernelPairHom _) ⟶
      projectiveBundle ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree) :=
  (pullbackChartFamily g E hfree).quotientDesc _ _ _ _
    ((pullbackChartFamily g E hfree).quotientChartOfHom _ _
      (isPullback_projectiveBundlePresentation X') (presentingFiberChartHom g))
    ((pullbackChartFamily g E hfree).siteMap_comp_quotientChartOfHom _ _ _ _ _
      (presentingFiberChartHom g))

/-- **The bundle of `g^*ℰ` does not depend on the chart it is glued over.** -/
instance isIso_projectiveBundleOverChartToProjectiveBundle_hom :
    IsIso (projectiveBundleOverChartToProjectiveBundle g E hfree).hom :=
  (pullbackChartFamily g E hfree).isIso_quotientDesc_quotientChartOfHom _ _ _ _ _ _
    (presentingFiberChartHom g) (surjective_projectiveBundlePresentation X')
    (surjective_presentingFiberChart g)

/-- The morphism from the bundle of `g^*ℰ` glued over the kernel pair of `W` to `P ×_X X'` is an
isomorphism of algebraic spaces. -/
instance isIso_projectiveBundleOverChartToFiberProduct :
    IsIso (projectiveBundleOverChartToFiberProduct g E hfree) :=
  have : IsIso ((ObjectProperty.ι _).map (projectiveBundleOverChartToFiberProduct g E hfree)) :=
    isIso_projectiveBundleOverChartToFiberProduct_hom g E hfree
  isIso_of_reflects_iso _ (ObjectProperty.ι _)

/-- The morphism from the bundle of `g^*ℰ` glued over the kernel pair of `W` to the projective
bundle of `g^*ℰ` is an isomorphism of algebraic spaces. -/
instance isIso_projectiveBundleOverChartToProjectiveBundle :
    IsIso (projectiveBundleOverChartToProjectiveBundle g E hfree) :=
  have : IsIso ((ObjectProperty.ι _).map (projectiveBundleOverChartToProjectiveBundle g E hfree)) :=
    isIso_projectiveBundleOverChartToProjectiveBundle_hom g E hfree
  isIso_of_reflects_iso _ (ObjectProperty.ι _)

/-- **The projective bundle of `g^*ℰ` is the base change of the projective bundle of `ℰ`**:
`𝐏(g^*ℰ) ≅ 𝐏(ℰ) ×_X X'`. -/
def projectiveBundlePullbackIso :
    projectiveBundle ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree) ≅
      projectiveBundleFiberProduct g E hfree :=
  (asIso (projectiveBundleOverChartToProjectiveBundle g E hfree)).symm ≪≫
    asIso (projectiveBundleOverChartToFiberProduct g E hfree)

/-- **The isomorphism `𝐏(g^*ℰ) ≅ P ×_X X'` lies over `X'`.** -/
theorem projectiveBundlePullbackIso_hom_comp_proj :
    (projectiveBundlePullbackIso g E hfree).hom ≫ projectiveBundleFiberProductProj g E hfree =
      projectiveBundleProj ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree) := by
  have h₁ := (pullbackChartFamily g E hfree).quotientDesc_comp
    (chartKernelPairFstHom (presentingFiberChart g))
    (chartKernelPairSndHom (presentingFiberChart g)) (isPullback_chartKernelPairHom _) _ _
    (siteMap_comp_presentingFiberChartToFiberProduct g E hfree)
    (projectiveBundleFiberProductProj g E hfree) (presentingFiberChartToFiberProduct_snd g E hfree)
  have h₂ := (pullbackChartFamily g E hfree).quotientDesc_comp
    (chartKernelPairFstHom (presentingFiberChart g))
    (chartKernelPairSndHom (presentingFiberChart g)) (isPullback_chartKernelPairHom _) _ _
    ((pullbackChartFamily g E hfree).siteMap_comp_quotientChartOfHom _ _ _ _ _
      (presentingFiberChartHom g))
    (projectiveBundleProj ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      ((pullbackChartFamily g E hfree).quotientChart_comp_quotientHom _ _ _)).trans
        ((pullbackChartFamily g E hfree).siteMap_comp_siteToSpace (presentingFiberChartHom g))))
  rw [projectiveBundlePullbackIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom,
    Category.assoc]
  show inv (projectiveBundleOverChartToProjectiveBundle g E hfree) ≫
      (projectiveBundleOverChartToFiberProduct g E hfree ≫
        projectiveBundleFiberProductProj g E hfree) = _
  rw [IsIso.inv_comp_eq]
  exact h₁.trans h₂.symm

end Iso

end AlgebraicGeometry.Space

end
