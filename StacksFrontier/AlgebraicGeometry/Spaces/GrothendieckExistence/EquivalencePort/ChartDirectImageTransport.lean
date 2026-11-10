module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageCartesianChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicFunctionsPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperRepresentableDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafDataComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.InverseImageIdealCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.DirectImageCompletionComparison
public import StacksFrontier.AlgebraicGeometry.Groupoids.IdealSheafComap
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Equivalence

namespace Stacks.Scheme.C1573
end Stacks.Scheme.C1573
namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# Reading the direct image along a representable morphism on the chart schemes

Let `f : X ⟶ Y` be a representable morphism of algebraic spaces over a scheme `S`, let `V` be an
étale chart of `Y` and `U = V ×_Y X` the base-changed chart of `X`, with
`f_V : U ⟶ V` the morphism of chart schemes underlying the cartesian projection.  For an
`𝒪_X`-module `N`, write `N|_U` for its restriction to the Zariski site of the chart scheme of
`U` (`AlgebraicGeometry.Space.C1573.chartZariskiModule`, the direct image along the comparison
functor of the chart; its sections over a Zariski open `W` are the sections of `N` over the
étale chart `W` cuts out).  This file identifies the sections of `f_*N` over `V` with the global
sections of `N|_U`, that is, with the sections over `V` of the direct image of `N|_U` along the
morphism of schemes `f_V`:

`(f_*N)(V) ≅ Γ(U, N|_U) = Γ(V, f_{V*}(N|_U))`,

naturally in `N` and linearly over `𝒪_Y(V) = Γ(V, 𝒪_V)`.

## Main definitions

* `AlgebraicGeometry.Space.C1573.chartZariskiModule`: the restriction of `𝒪_X`-modules to the
  Zariski site of a chart scheme, as a functor.
* `AlgebraicGeometry.Space.C1573.chartBaseChangeSchemeHom`: the morphism of chart schemes `f_V`.
* `AlgebraicGeometry.Space.C1573.baseChangeOpenChartDiagram`: for a Zariski open `W` of the
  chart scheme of `U`, the diagram of étale charts formed by the chart `W` cuts out and `V`.
* `AlgebraicGeometry.Space.C1573.chartBaseChangeSectionsEquiv`: the linear identification
  `(f_*N)(V) ≅ Γ(V, f_{V*}(N|_U))`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 08BD](https://stacks.math.columbia.edu/tag/08BD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-- Restricting `g^♯` on global sections to an open `W` and then further, or restricting it from
`⊤`, give the same map. -/
theorem Stacks.Scheme.C1573.appLE_top_comp_map {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y)
    (W : X.Opens) {U₁ : X.Opens} (i : op W ⟶ op U₁) (j : op ⊤ ⟶ op U₁) :
    g.appLE ⊤ W (le_top : W ≤ (TopologicalSpace.Opens.map g.base).obj ⊤) ≫ X.presheaf.map i =
      g.app ⊤ ≫ X.presheaf.map j :=
  (Category.assoc _ _ _).trans (congrArg (g.app ⊤ ≫ ·)
    ((X.presheaf.map_comp _ _).symm.trans (congrArg X.presheaf.map (Subsingleton.elim _ _))))

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.Space.C1573
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Chart

variable (X : AlgebraicSpaces B S hS)

/-- **The restriction of `𝒪_X`-modules to the Zariski site of the scheme of an étale chart**, as
a functor: the direct image along the comparison functor of the chart, whose sections over a
Zariski open `W` are the sections over the étale chart `W` cuts out. -/
abbrev C1573.chartZariskiModule (A : SmallEtale B S hS X.1) :
    SheafOfModules.{u} (structureRingSheaf B S hS X) ⥤ (chartScheme A).Modules :=
  SheafOfModules.pushforward.{u} (chartComparisonRingMap B S hS X A)

/-- The morphism of étale charts from the chart cut out by a Zariski open of a chart scheme to the
chart; its underlying morphism of schemes is the open immersion. -/
abbrev C1573.openChartOfComparisonToChart (A : SmallEtale B S hS X.1) (W : (chartScheme A).Opens) :
    openChartOfComparison B S hS X A W ⟶ A :=
  ((SmallEtale.chartLocalizationEquivalence B S hS X.1 A).functor.obj
    ((representedSmallEtaleEquivalence B S hS (chartFppfObject B S hS X A)).inverse.obj
      (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property W))).hom

/-- The morphism of schemes underlying `openChartOfComparisonToChart` is the open immersion
`W.ι`. -/
theorem C1573.toScheme_map_openChartOfComparisonToChart (A : SmallEtale B S hS X.1)
    (W : (chartScheme A).Opens) :
    (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map
      (openChartOfComparisonToChart B S hS X A W)) = W.ι := rfl

/-- The chart cut out by `⊤` maps isomorphically onto the chart. -/
instance C1573.isIso_openChartOfComparisonToChart_top (A : SmallEtale B S hS X.1) :
    IsIso (openChartOfComparisonToChart B S hS X A ⊤) := by
  have h : (openChartOfComparisonTopIso B S hS X A).hom =
      openChartOfComparisonToChart B S hS X A ⊤ :=
    (Category.comp_id _).symm.trans (Over.w _)
  rw [← h]
  infer_instance

end Chart

section BaseChange

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
  (V : SmallEtale B S hS Y.1)

/-- **The morphism of chart schemes `f_V : V ×_Y X ⟶ V`** underlying the cartesian projection of
the base change of an étale chart `V` of `Y` along a representable morphism `f`. -/
abbrev C1573.chartBaseChangeSchemeHom :
    chartScheme ((smallBaseChange B S hS f hf).obj V) ⟶ chartScheme V :=
  (BigFppfOver.toScheme B S hS).map ((smallBaseChangeProjection B S hS f hf).app V)

/-- The chart diagram formed by the étale chart of `X` which a Zariski open `W` of the chart
scheme of `V ×_Y X` cuts out, the chart `V`, and the composite of the open immersion with
`f_V`. -/
def C1573.baseChangeOpenChartDiagram
    (W : (chartScheme ((smallBaseChange B S hS f hf).obj V)).Opens) :
    ChartDiagram B S hS X.1 Y.1 f.hom where
  U := openChartOfComparison B S hS X ((smallBaseChange B S hS f hf).obj V) W
  V := V
  g := (SmallEtale.toOver B S hS X.1).map (openChartOfComparisonToChart B S hS X _ W) ≫
    (smallBaseChangeProjection B S hS f hf).app V
  comm := by
    have h1 := CostructuredArrow.w (openChartOfComparisonToChart B S hS X _ W).hom
    have h2 : ((smallBaseChange B S hS f hf).obj V).1.hom ≫ f.hom =
        yoneda.map ((smallBaseChangeProjection B S hS f hf).app V) ≫ V.1.hom := hf.w V.1.hom
    calc _ = (yoneda.map (openChartOfComparisonToChart B S hS X _ W).hom.left ≫
          ((smallBaseChange B S hS f hf).obj V).1.hom) ≫ f.hom := by rw [h1]
      _ = yoneda.map (openChartOfComparisonToChart B S hS X _ W).hom.left ≫
          (yoneda.map ((smallBaseChangeProjection B S hS f hf).app V) ≫ V.1.hom) := by
        rw [Category.assoc, h2]
      _ = _ := by rw [← Category.assoc, ← Functor.map_comp]; rfl

/-- The morphism of schemes underlying the morphism of charts of `baseChangeOpenChartDiagram` is
the open immersion `W.ι` followed by `f_V`. -/
theorem C1573.toScheme_map_openChartDiagram_g
    (W : (chartScheme ((smallBaseChange B S hS f hf).obj V)).Opens) :
    (BigFppfOver.toScheme B S hS).map (baseChangeOpenChartDiagram B S hS f hf V W).g =
      W.ι ≫ chartBaseChangeSchemeHom B S hS f hf V :=
  Functor.map_comp _ _ _

/-- **The pullback of functions along the chart diagram of an open `W` is the pullback along
`f_V` restricted to `W`**, read through `Γ(V ×_Y X, W) ≅ Γ(W, ⊤)`. -/
theorem C1573.chartSectionsRingHom_appLE
    (W : (chartScheme ((smallBaseChange B S hS f hf).obj V)).Opens) (r : Γ(chartScheme V, ⊤)) :
    chartSectionsRingHom B S hS X ((smallBaseChange B S hS f hf).obj V) W
        ((chartBaseChangeSchemeHom B S hS f hf V).appLE ⊤ W le_top r) =
      chartDiagramPullback B S hS f (baseChangeOpenChartDiagram B S hS f hf V W) r := by
  have e1 : chartDiagramPullback B S hS f (baseChangeOpenChartDiagram B S hS f hf V W) r =
      (W.ι ≫ chartBaseChangeSchemeHom B S hS f hf V).appTop r := by
    change (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      (baseChangeOpenChartDiagram B S hS f hf V W).g).op) r = _
    rw [toScheme_map_openChartDiagram_g]
    rfl
  rw [e1, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Scheme.Opens.ι_appTop]
  change (Scheme.Opens.topIso W).inv
    ((chartBaseChangeSchemeHom B S hS f hf V).appLE ⊤ W le_top r) = _
  rw [Scheme.Opens.topIso_inv]
  exact ConcreteCategory.congr_hom (Stacks.Scheme.C1573.appLE_top_comp_map _ W _ _) r

/-- The canonical map of sections `(f_*N)(V) ⟶ N(V ×_Y X)` is bijective, the base-changed chart
representing `V ×_Y X`. -/
theorem C1573.bijective_modulePushforwardCounitApp_baseChangeChartDiagram
    (N : Modules.{u, u} B S hS X.1 X.2) :
    Function.Bijective
      (modulePushforwardCounitApp B S hS f N (baseChangeChartDiagram B S hS f hf V)) :=
  bijective_modulePushforwardCounitApp_of_isPullback B S hS f N _ (hf.isPullback V.1.hom)

/-- The map of sections `(f_*N)(V) ⟶ Γ(V ×_Y X, N|_{V ×_Y X})`. -/
def C1573.chartBaseChangeSectionsMap (N : Modules.{u, u} B S hS X.1 X.2)
    (x : ((modulePushforward B S hS f).obj N).val.obj (op V)) :
    Γ((chartZariskiModule B S hS X ((smallBaseChange B S hS f hf).obj V)).obj N, ⊤) :=
  N.val.map (openChartOfComparisonToChart B S hS X _ ⊤).op
    (modulePushforwardCounitApp B S hS f N (baseChangeChartDiagram B S hS f hf V) x)

/-- The map of sections `(f_*N)(V) ⟶ Γ(V ×_Y X, N|_{V ×_Y X})` is bijective. -/
theorem C1573.bijective_chartBaseChangeSectionsMap (N : Modules.{u, u} B S hS X.1 X.2) :
    Function.Bijective (chartBaseChangeSectionsMap B S hS f hf V N) :=
  (ConcreteCategory.bijective_of_isIso
    (N.val.presheaf.mapIso (asIso (openChartOfComparisonToChart B S hS X
      ((smallBaseChange B S hS f hf).obj V) ⊤)).op).hom).comp
    (bijective_modulePushforwardCounitApp_baseChangeChartDiagram B S hS f hf V N)

/-- The canonical map of sections into the global sections of the chart restriction is natural in
the module. -/
theorem C1573.chartBaseChangeSectionsMap_naturality {N N' : Modules.{u, u} B S hS X.1 X.2}
    (φ : N ⟶ N')
    (x : ((modulePushforward B S hS f).obj N).val.obj (op V)) :
    chartBaseChangeSectionsMap B S hS f hf V N'
        (((modulePushforward B S hS f).map φ).val.app (op V) x) =
      ((chartZariskiModule B S hS X ((smallBaseChange B S hS f hf).obj V)).map φ).app ⊤
        (chartBaseChangeSectionsMap B S hS f hf V N x) := by
  have h1 := modulePushforwardCounitApp_map B S hS f φ (baseChangeChartDiagram B S hS f hf V) x
  have h2 := PresheafOfModules.naturality_apply φ.val
    (openChartOfComparisonToChart B S hS X ((smallBaseChange B S hS f hf).obj V) ⊤).op
    (modulePushforwardCounitApp B S hS f N (baseChangeChartDiagram B S hS f hf V) x)
  exact (congrArg (N'.val.map (openChartOfComparisonToChart B S hS X
    ((smallBaseChange B S hS f hf).obj V) ⊤).op) h1).trans h2.symm

/-- The canonical map of sections into the global sections of the chart restriction is
additive. -/
theorem C1573.chartBaseChangeSectionsMap_add (N : Modules.{u, u} B S hS X.1 X.2)
    (x y : ((modulePushforward B S hS f).obj N).val.obj (op V)) :
    chartBaseChangeSectionsMap B S hS f hf V N (x + y) =
      chartBaseChangeSectionsMap B S hS f hf V N x +
        chartBaseChangeSectionsMap B S hS f hf V N y :=
  (congrArg (N.val.restrictₛₗ (openChartOfComparisonToChart B S hS X
    ((smallBaseChange B S hS f hf).obj V) ⊤).op)
    (modulePushforwardCounitApp_add B S hS f N (baseChangeChartDiagram B S hS f hf V) x y)).trans
    (map_add _ _ _)

/-- The pullback of a function on `V` to the chart cut out by `⊤` along the chart diagram of the
base change is its pullback along `f_V`, read through `Γ(⊤, ⊤) ≅ Γ(V ×_Y X, ⊤)`. -/
theorem C1573.chartRestrict_chartDiagramPullback_baseChangeChartDiagram
    (r : chartRing B S hS Y.1 Y.2 V) :
    chartRestrict (hF := X.2) (openChartOfComparisonToChart B S hS X
        ((smallBaseChange B S hS f hf).obj V) ⊤)
      (chartDiagramPullback B S hS f (baseChangeChartDiagram B S hS f hf V) r) =
    chartSectionsRingHom B S hS X ((smallBaseChange B S hS f hf).obj V) ⊤
      ((chartBaseChangeSchemeHom B S hS f hf V).appTop r) := by
  have h : (⊤ : (chartScheme ((smallBaseChange B S hS f hf).obj V)).Opens).ι.appTop =
      (⊤ : (chartScheme ((smallBaseChange B S hS f hf).obj V)).Opens).topIso.inv := by
    rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv]
    exact congrArg (fun k => (chartScheme ((smallBaseChange B S hS f hf).obj V)).presheaf.map
      (Quiver.Hom.op k)) (Subsingleton.elim _ _)
  exact congrArg (fun k => k.hom ((chartBaseChangeSchemeHom B S hS f hf V).appTop r)) h

/-- The canonical map of sections into the global sections of the chart restriction is
semilinear along pullback of functions by `f_V`. -/
theorem C1573.chartBaseChangeSectionsMap_smul (N : Modules.{u, u} B S hS X.1 X.2)
    (r : chartRing B S hS Y.1 Y.2 V)
    (x : ((modulePushforward B S hS f).obj N).val.obj (op V)) :
    chartBaseChangeSectionsMap B S hS f hf V N (r • x) =
      (chartBaseChangeSchemeHom B S hS f hf V).appTop r •
        chartBaseChangeSectionsMap B S hS f hf V N x := by
  refine (congrArg (N.val.restrictₛₗ (openChartOfComparisonToChart B S hS X
    ((smallBaseChange B S hS f hf).obj V) ⊤).op)
    (modulePushforwardCounitApp_smul B S hS f N (baseChangeChartDiagram B S hS f hf V) r x)).trans
    ?_
  refine (LinearMap.map_smulₛₗ _ _ _).trans ?_
  exact congrArg (· • _) (chartRestrict_chartDiagramPullback_baseChangeChartDiagram B S hS f hf V r)

/-- The ring of functions on an étale chart, read as the ring of global functions on its scheme;
this is the identity. -/
abbrev C1573.chartRingOfTop {Z : AlgebraicSpaces B S hS} (A : SmallEtale B S hS Z.1) :
    Γ(chartScheme A, ⊤) →+* chartRing B S hS Z.1 Z.2 A :=
  RingHom.id _

/-- The sections of an `𝒪_Z`-module over an étale chart, as a module over the global functions
of the chart scheme. -/
abbrev C1573.chartSectionsTop {Z : AlgebraicSpaces B S hS} (A : SmallEtale B S hS Z.1) :
    Modules.{u, u} B S hS Z.1 Z.2 ⥤ ModuleCat.{u} Γ(chartScheme A, ⊤) :=
  SheafOfModules.evaluation _ (op A) ⋙ ModuleCat.restrictScalars (chartRingOfTop B S hS A)

/-- **The sections of `f_*N` over `V` are the global sections of the direct image along `f_V` of
the chart restriction of `N` to `V ×_Y X`**, linearly over `Γ(V, 𝒪_V)`. -/
def C1573.chartBaseChangeSectionsEquiv (N : Modules.{u, u} B S hS X.1 X.2) :
    (chartSectionsTop B S hS V).obj ((modulePushforward B S hS f).obj N) ≃ₗ[Γ(chartScheme V, ⊤)]
      Γ((Scheme.Modules.pushforward (chartBaseChangeSchemeHom B S hS f hf V)).obj
          ((chartZariskiModule B S hS X ((smallBaseChange B S hS f hf).obj V)).obj N), ⊤) :=
  LinearEquiv.ofBijective
    (({ toFun := chartBaseChangeSectionsMap B S hS f hf V N
        map_add' := chartBaseChangeSectionsMap_add B S hS f hf V N
        map_smul' := fun r x => chartBaseChangeSectionsMap_smul B S hS f hf V N r x } :
      (chartSectionsTop B S hS V).obj ((modulePushforward B S hS f).obj N) →ₗ[Γ(chartScheme V, ⊤)]
        Γ((Scheme.Modules.pushforward (chartBaseChangeSchemeHom B S hS f hf V)).obj
          ((chartZariskiModule B S hS X ((smallBaseChange B S hS f hf).obj V)).obj N), ⊤)))
    (bijective_chartBaseChangeSectionsMap B S hS f hf V N)

/-- The identification `chartBaseChangeSectionsEquiv` is given by
`chartBaseChangeSectionsMap`. -/
theorem C1573.chartBaseChangeSectionsEquiv_apply (N : Modules.{u, u} B S hS X.1 X.2)
    (x : ((modulePushforward B S hS f).obj N).val.obj (op V)) :
    chartBaseChangeSectionsEquiv B S hS f hf V N x =
      chartBaseChangeSectionsMap B S hS f hf V N x :=
  rfl

section Ideal

variable (J : (SheafOfModules.unit
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).Submodule)

/-- The ideal of global functions on the chart scheme of `V` given by the sections of `J` over
`V`. -/
abbrev C1573.chartTopIdeal : Ideal Γ(chartScheme V, ⊤) :=
  chartIdeal B S hS Y J V

/-- The ring map of global functions along the open immersion of `W` followed by `f_V` is the
pullback of functions along the morphism of charts of the chart diagram of `W`. -/
theorem C1573.chartSectionsRestrict_comp_chartIdealPullbackHom
    (W : (chartScheme ((smallBaseChange B S hS f hf).obj V)).Opens)
    (r : chartRing B S hS Y.1 Y.2 V) :
    chartSectionsRestrict B S hS X (openChartOfComparisonToChart B S hS X _ W)
        (chartIdealPullbackHom B S hS f hf V r) =
      (W.ι ≫ chartBaseChangeSchemeHom B S hS f hf V).appTop r := by
  rw [Scheme.Hom.comp_appTop]
  rfl

/-- **The inverse image of the ideal sheaf `J(V)~` along `f_V`, over an affine open `W` of the
chart scheme of `V ×_Y X`, is the ideal of sections of the inverse-image ideal `f⁻¹J · 𝒪_X` over
the étale chart `W` cuts out**, read through `Γ(W, ⊤) ≅ Γ(V ×_Y X, W)`. -/
theorem C1573.map_chartSectionsRingHom_ideal_comap [IsAffine (chartScheme V)]
    (hJ : IsCartesianOnAffineCharts J.toSheafOfModules)
    (W : (chartScheme ((smallBaseChange B S hS f hf).obj V)).Opens) (hW : IsAffineOpen W) :
    Ideal.map (chartSectionsRingHom B S hS X ((smallBaseChange B S hS f hf).obj V) W)
        (((Scheme.IdealSheafData.ofIdealTop (chartTopIdeal B S hS V J)).comap
          (chartBaseChangeSchemeHom B S hS f hf V)).ideal ⟨W, hW⟩) =
      chartIdeal B S hS X (inverseImageIdeal B S hS f hf J)
        (openChartOfComparison B S hS X ((smallBaseChange B S hS f hf).obj V) W) := by
  have : IsAffine W.toScheme := hW
  have h1 := Stacks.IdealSheaf.ideal_comap_ι_top
    ((Scheme.IdealSheafData.ofIdealTop (chartTopIdeal B S hS V J)).comap
      (chartBaseChangeSchemeHom B S hS f hf V)) hW (isAffineOpen_top W.toScheme)
  rw [← Scheme.IdealSheafData.comap_comp,
    Stacks.IdealSheaf.ideal_comap_top_of_isAffine, Stacks.Coherent.ofIdealTop_ideal_top] at h1
  change Ideal.map W.topIso.inv.hom _ = _
  rw [← h1]
  refine Eq.trans ?_ (pullbackIdealSubsheaf_obj_of_isAffine B S hS f hf J hJ V ‹_›
    (openChartOfComparison B S hS X ((smallBaseChange B S hS f hf).obj V) W)
    (openChartOfComparisonToChart B S hS X _ W) hW).symm
  rw [Ideal.map_map]
  exact congrArg (fun φ => Ideal.map φ (chartIdeal B S hS Y J V))
    (RingHom.ext fun r => (chartSectionsRestrict_comp_chartIdealPullbackHom B S hS f hf V W r).symm)

end Ideal

end BaseChange

end AlgebraicGeometry.Space
