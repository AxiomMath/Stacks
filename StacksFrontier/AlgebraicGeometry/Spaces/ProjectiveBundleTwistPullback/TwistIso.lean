module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleQuotientFlatDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleSpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleTwistCharts
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SurjectivePoints
import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleTwistPullback.QuotientReading
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleTwistPullback.PullbackMap

/-!
# The isomorphism `θ^*𝒪_P(1) ≅ 𝒪_Q(1)`

The two tautological quotients of `π'^*g^*ℰ` over the chart `W`, their readings on the chart
bundles (Stacks 01O3), and the isomorphism
`AlgebraicGeometry.Space.projectiveBundleTwistPullbackIso : θ^*𝒪_P(1) ≅ 𝒪_Q(1)` carrying the
inverse image of the tautological quotient of `𝐏(ℰ)` to that of `𝐏(g^*ℰ)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

-- `CategoryTheory.catToReflQuiver` offers a second route from `Category` to `Quiver`, by which an
-- arrow `M ⟶ N` of modules written in a statement would not match the arrows of the inverse-image
-- functors without unfolding them.
attribute [-instance] CategoryTheory.catToReflQuiver

/-! ### The two tautological quotients over the chart `W` -/

section Twist

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X X' : AlgebraicSpaces B S hS}
  (g : X' ⟶ X) (E : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]
  (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)

/-- **The identification `π'^*g^*ℰ ≅ θ^*π^*ℰ`** of iterated inverse images, through
`θ ≫ π = π' ≫ g`. -/
abbrev projectiveBundlePullbackModuleIso :
    (modulePullback B S hS (projectiveBundleProj ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))).obj
        ((modulePullback B S hS g).obj E) ≅
      (modulePullback B S hS (projectiveBundlePullbackMap g E hfree)).obj
        ((modulePullback B S hS (projectiveBundleProj E hfree)).obj E) :=
  (QuasiCoherentDescent.pullbackComparison B S hS
      (projectiveBundleProj ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)) g _ rfl E).symm ≪≫
    QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundlePullbackMap g E hfree)
      (projectiveBundleProj E hfree) _ (projectiveBundlePullbackMap_comp_proj g E hfree) E

/-- The inverse image `θ^*(π^*ℰ ⟶ 𝒪_P(1))` of the tautological quotient of `P`, as a quotient of
`π'^*g^*ℰ`. -/
abbrev projectiveBundlePullbackTautological :
    (modulePullback B S hS (projectiveBundleProj ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))).obj
        ((modulePullback B S hS g).obj E) ⟶
      (modulePullback B S hS (projectiveBundlePullbackMap g E hfree)).obj
        (projectiveBundleTwist E hfree).obj :=
  (projectiveBundlePullbackModuleIso g E hfree).hom ≫
    (modulePullback B S hS (projectiveBundlePullbackMap g E hfree)).map
      (projectiveBundleTautological E hfree).hom

/-- The quotient `π'^*g^*ℰ ⟶ θ^*𝒪_P(1)` is an epimorphism, the inverse image being a left
adjoint. -/
theorem epi_projectiveBundlePullbackTautological :
    Epi (((QuasiCoherentDescent.pullbackComparison B S hS
      (projectiveBundleProj ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)) g _ rfl E).symm ≪≫
        QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundlePullbackMap g E hfree)
          (projectiveBundleProj E hfree) _
          (projectiveBundlePullbackMap_comp_proj g E hfree) E).hom ≫
      (modulePullback B S hS (projectiveBundlePullbackMap g E hfree)).map
        (projectiveBundleTautological E hfree).hom) := by
  have := Functor.preservesEpimorphisms_of_adjunction
    (modulePullbackAdjunction B S hS (projectiveBundlePullbackMap g E hfree))
  exact @epi_comp _ _ _ _ _ _ (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom _)) _
    (Functor.map_epi _ _)

section Chart

variable {V : SmallEtale B S hS X'.1} (m : V ⟶ bundleBaseChart X')
  (n : (SmallEtale.toOver B S hS X'.1).obj V ⟶ (SmallEtale.toOver B S hS X.1).obj
    (bundleBaseChart X))
  (w : representedSpaceMap B S hS n ≫ chartToSpace B S hS X (bundleBaseChart X) =
    chartToSpace B S hS X' V ≫ g)

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite in
/-- **Stacks 01O3 along `n : V ⟶ U` over `g`**, for the comparison `𝐏(g^*ℰ|_V) ⟶ 𝐏(ℰ|_U)`, in the
shape of `AlgebraicGeometry.Space.quotientReadingHyp_modulePullback_of_comp`.  The tautological
quotients, the comparison of twists and the identification of modules are named, so that the
statement is spelled as the hypothesis it is fed to. -/
theorem tautologicalDatumTwistBaseChangeIso_spec_chartBundlePullbackSiteMap
    (univ : (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
        (associatedBigEtaleSite B)
        ((projectiveBundleChartFamily E hfree).siteToChart (bundleBaseChart X)).left)).obj
        (schemeReading E (chartToSpace B S hS X (bundleBaseChart X))) ⟶
      chartBundleTwist E (bundleBaseChart X))
    (hu : univ = chartBundleTautological E (bundleBaseChart X))
    (c : schemeReading ((modulePullback B S hS g).obj E) (chartToSpace B S hS X' V) ≅
      (Scheme.Modules.pullback
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) n.left)).obj
        (schemeReading E (chartToSpace B S hS X (bundleBaseChart X))))
    (hc : c = chartBundleModulePullbackIso g E n w)
    (univ₀ : (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
        (associatedBigEtaleSite B)
          ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
          (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteToChart V).left)).obj
        (schemeReading ((modulePullback B S hS g).obj E) (chartToSpace B S hS X' V)) ⟶
          chartBundleTwist ((modulePullback B S hS g).obj E) V)
    (hu₀ : univ₀ = chartBundleTautological ((modulePullback B S hS g).obj E) V)
    (θ : (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
        (associatedBigEtaleSite B) (chartBundlePullbackSiteMap g E hfree n w).left)).obj
        (chartBundleTwist E (bundleBaseChart X)) ≅ chartBundleTwist
          ((modulePullback B S hS g).obj E) V)
    (hθ : θ = Stacks.RelativeProj.tautologicalDatumTwistBaseChangeIso (chartSiteSchemeHom n)
      (chartBundleModule E (bundleBaseChart X))
        (chartBundleModule ((modulePullback B S hS g).obj E) V)
      (chartBundleModulePullbackIso g E n w)) :
    (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
          (associatedBigEtaleSite B) (chartBundlePullbackSiteMap g E hfree n w).left)).map univ ≫
        θ.hom =
      (Scheme.Modules.pullbackComp
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            (chartBundlePullbackSiteMap g E hfree n w).left)
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            ((projectiveBundleChartFamily E hfree).siteToChart (bundleBaseChart X)).left)).hom.app
          (schemeReading E (chartToSpace B S hS X (bundleBaseChart X))) ≫
        (Scheme.Modules.pullbackCongr (schemeHom_comp_eq_of_eq
          (isPullback_chartBundlePullbackSiteMap g E hfree n w).w)).hom.app
          (schemeReading E (chartToSpace B S hS X (bundleBaseChart X))) ≫
        (Scheme.Modules.pullbackComp
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
              (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteToChart V).left)
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            n.left)).inv.app (schemeReading E (chartToSpace B S hS X (bundleBaseChart X))) ≫
        (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
          (associatedBigEtaleSite B)
            ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
            (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteToChart V).left)).map
          c.inv ≫ univ₀ := by
  subst hu hc hu₀ hθ
  exact Stacks.RelativeProj.tautologicalDatumTwistBaseChangeIso_spec (chartSiteSchemeHom n)
    (chartBundleModule E (bundleBaseChart X))
      (chartBundleModule ((modulePullback B S hS g).obj E) V)
    (chartBundleModulePullbackIso g E n w)

/-- The square `𝐏(g^*ℰ|_V) ⟶ V ⟶ X'` equals `𝐏(g^*ℰ|_V) ⟶ 𝐏(g^*ℰ) ⟶ X'`, for a chart `V` with a
morphism `m : V ⟶ U'`. -/
theorem representedSpaceMap_siteToChart_comp_chartToSpace_of_hom :
    representedSpaceMap B S hS
      ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteToChart V) ≫
        chartToSpace B S hS X' V =
      projectiveBundleChartOfHom ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree) m ≫ projectiveBundleProj
        ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree) :=
  ObjectProperty.hom_ext _
    (isPullback_projectiveBundleChartOfHom ((modulePullback B S hS g).obj E)
    (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree) m).w.symm

/-- The square `𝐏(g^*ℰ|_V) ⟶ V ⟶ X' ⟶ X` equals `𝐏(g^*ℰ|_V) ⟶ 𝐏(g^*ℰ) ⟶ X' ⟶ X`. -/
theorem representedSpaceMap_siteToChart_comp_chartToSpace_comp_of_hom :
    representedSpaceMap B S hS
      ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteToChart V) ≫
        (chartToSpace B S hS X' V ≫ g) =
      (projectiveBundleChartOfHom ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree) m ≫ projectiveBundleProj
        ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)) ≫ g :=
  (Category.assoc _ _ _).symm.trans (congrArg (· ≫ g)
    (representedSpaceMap_siteToChart_comp_chartToSpace_of_hom g E hfree m))

/-- The two morphisms `𝐏(g^*ℰ|_V) ⟶ X` through `𝐏(ℰ|_U) ⟶ 𝐏(ℰ)` and through `𝐏(g^*ℰ) ⟶ X'`
agree, when the chart over `m` followed by `θ` is the morphism through `𝐏(ℰ|_U)`. -/
theorem representedSpaceMap_chartBundlePullbackSiteMap_comp_of_comp_eq
    (hθ : projectiveBundleChartOfHom ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree) m ≫ projectiveBundlePullbackMap g E
      hfree =
      representedSpaceMap B S hS (chartBundlePullbackSiteMap g E hfree n w) ≫
        projectiveBundleAtlas E hfree) :
    representedSpaceMap B S hS (chartBundlePullbackSiteMap g E hfree n w) ≫
        (projectiveBundleAtlas E hfree ≫ projectiveBundleProj E hfree) =
      (projectiveBundleChartOfHom ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree) m ≫ projectiveBundleProj
        ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)) ≫ g :=
  (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ projectiveBundleProj E hfree) hθ.symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (projectiveBundleChartOfHom ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree) m ≫ ·)
      (projectiveBundlePullbackMap_comp_proj g E hfree)).trans (Category.assoc _ _ _).symm)))

/-- **The tautological quotient of `𝐏(g^*ℰ|_{U'})`, pulled back to `𝐏(g^*ℰ|_V)` along `m`, reads
as the tautological quotient of `𝐏(g^*ℰ|_V)`** (Stacks 01O3 along `m`). -/
theorem exists_quotientReadingHyp_siteMap_projectiveBundleChartQuotient :
    ∃ ε : representedZariskiModule B S hS
      ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).site V)
        ((modulePullback B S hS (representedSpaceMap B S hS
          ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
            (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteMap m))).obj
            (projectiveBundleChartTwist ((modulePullback B S hS g).obj E)
            (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))) ≅
        chartBundleTwist ((modulePullback B S hS g).obj E) V,
      QuotientReadingHyp ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_obj_of_isQuasicoherentOnSite g E hE)
        (representedSpaceMap_siteToChart_comp_chartToSpace_of_hom g E hfree m)
        (chartBundleTautological ((modulePullback B S hS g).obj E) V) ε
        ((modulePullback B S hS (representedSpaceMap B S hS
          ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
            (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteMap m))).map
            (projectiveBundleChartQuotient ((modulePullback B S hS g).obj E)
            (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)))
        ((modulePullback B S hS (representedSpaceMap B S hS
            ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
              (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteMap m))).mapIso
          (QuasiCoherentDescent.pullbackComparison B S hS
            (projectiveBundleAtlas ((modulePullback B S hS g).obj E)
            (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))
            (projectiveBundleProj ((modulePullback B S hS g).obj E)
              (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)) _ rfl
              ((modulePullback B S hS g).obj E)).symm ≪≫
          (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS
            ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
              (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteMap m))
            (projectiveBundleAtlas ((modulePullback B S hS g).obj E)
              (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree) ≫ projectiveBundleProj
              ((modulePullback B S hS g).obj E)
              (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))
            (projectiveBundleChartOfHom ((modulePullback B S hS g).obj E)
              (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree) m ≫ projectiveBundleProj
              ((modulePullback B S hS g).obj E)
              (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))
            (Category.assoc _ _ _).symm ((modulePullback B S hS g).obj E)).symm) :=
by
  have h₂ := quotientReadingHyp_modulePullback ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_obj_of_isQuasicoherentOnSite g E hE)
      ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteMap m)
      (ρ := (projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteToChart (bundleBaseChart X'))
      (ρ' := (projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteToChart V)
      (t := (SmallEtale.toOver B S hS X'.1).map m)
        (siteMap_comp_siteToChart ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree) m)
      (ψY := chartToSpace B S hS X' (bundleBaseChart X')) (ψY' := chartToSpace B S hS X' V)
      (ψU := projectiveBundleAtlas ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree) ≫ projectiveBundleProj
        ((modulePullback B S hS g).obj E) (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))
      (ψR := projectiveBundleChartOfHom ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree) m ≫ projectiveBundleProj
        ((modulePullback B S hS g).obj E) (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))
      (representedSpaceMap_projectiveBundleChartProj_comp ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)) (Category.assoc _ _ _).symm
      (representedSpaceMap_toOver_map_comp_chartToSpace m)
      (representedSpaceMap_siteToChart_comp_chartToSpace_of_hom g E hfree m)
      (chartBundleTautological ((modulePullback B S hS g).obj E) (bundleBaseChart X'))
        (chartBundleTautological ((modulePullback B S hS g).obj E) V)
      (chartBundleTwistIso ((modulePullback B S hS g).obj E) m)
        (chartBundleTwistIso_spec ((modulePullback B S hS g).obj E) m)
      (isQuasicoherentOnSite_projectiveBundleChartModule ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))
      (isQuasicoherentOnSite_projectiveBundleChartTwist ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))
      (projectiveBundleChartTwistReadingIso ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))
        (projectiveBundleChartQuotient ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))
      (QuasiCoherentDescent.pullbackComparison B S hS
        (projectiveBundleAtlas ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))
        (projectiveBundleProj ((modulePullback B S hS g).obj E)
          (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)) _ rfl
          ((modulePullback B S hS g).obj E)).symm
      (quotientReadingHyp_projectiveBundle ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))
  exact ⟨_, h₂⟩

/-- **The tautological quotient of `𝐏(ℰ|_U)`, pulled back to `𝐏(g^*ℰ|_V)` along `n`, reads as the
tautological quotient of `𝐏(g^*ℰ|_V)`** (Stacks 01O3 along `n`), as a quotient of the inverse
image of `g^*ℰ`. -/
theorem exists_quotientReadingHyp_chartBundlePullbackSiteMap_projectiveBundleChartQuotient
    (hθ : projectiveBundleChartOfHom ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree) m ≫ projectiveBundlePullbackMap g E
      hfree =
      representedSpaceMap B S hS (chartBundlePullbackSiteMap g E hfree n w) ≫
        projectiveBundleAtlas E hfree) :
    ∃ ε : representedZariskiModule B S hS
      ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).site V)
        ((modulePullback B S hS (representedSpaceMap B S hS
          (chartBundlePullbackSiteMap g E hfree n w))).obj (projectiveBundleChartTwist E hfree)) ≅
        chartBundleTwist ((modulePullback B S hS g).obj E) V,
      QuotientReadingHyp ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_obj_of_isQuasicoherentOnSite g E hE)
        (representedSpaceMap_siteToChart_comp_chartToSpace_of_hom g E hfree m)
        (chartBundleTautological ((modulePullback B S hS g).obj E) V) ε
        ((modulePullback B S hS (representedSpaceMap B S hS
          (chartBundlePullbackSiteMap g E hfree n w))).map (projectiveBundleChartQuotient E hfree))
        (((modulePullback B S hS (representedSpaceMap B S hS
            (chartBundlePullbackSiteMap g E hfree n w))).mapIso
          (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E hfree)
            (projectiveBundleProj E hfree) _ rfl E).symm ≪≫
          (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS
            (chartBundlePullbackSiteMap g E hfree n w))
            (projectiveBundleAtlas E hfree ≫ projectiveBundleProj E hfree)
            ((projectiveBundleChartOfHom ((modulePullback B S hS g).obj E)
              (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree) m ≫ projectiveBundleProj
              ((modulePullback B S hS g).obj E)
              (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)) ≫ g)
            (representedSpaceMap_chartBundlePullbackSiteMap_comp_of_comp_eq g E hfree m n w hθ)
            E).symm) ≪≫
          QuasiCoherentDescent.pullbackComparison B S hS
            (projectiveBundleChartOfHom ((modulePullback B S hS g).obj E)
              (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree) m ≫ projectiveBundleProj
              ((modulePullback B S hS g).obj E)
              (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)) g _ rfl E) :=
  ⟨_, quotientReadingHyp_modulePullback_obj E hE g
    (ρ := (projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteToChart V)
      (ψY := chartToSpace B S hS X' V)
    (ψU := projectiveBundleChartOfHom ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree) m ≫ projectiveBundleProj
      ((modulePullback B S hS g).obj E) (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))
    (representedSpaceMap_siteToChart_comp_chartToSpace_of_hom g E hfree m)
    (representedSpaceMap_siteToChart_comp_chartToSpace_comp_of_hom g E hfree m)
    (chartBundleTautological ((modulePullback B S hS g).obj E) V) _ _ _
    (quotientReadingHyp_modulePullback_of_comp E hE (chartBundlePullbackSiteMap g E hfree n w)
      (ρ := (projectiveBundleChartFamily E hfree).siteToChart (bundleBaseChart X))
      (ρ' := (projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteToChart V) (t := n)
      (isPullback_chartBundlePullbackSiteMap g E hfree n w).w
      (ψY := chartToSpace B S hS X (bundleBaseChart X))
      (ψU := projectiveBundleAtlas E hfree ≫ projectiveBundleProj E hfree)
      (representedSpaceMap_projectiveBundleChartProj_comp E hfree)
      (representedSpaceMap_chartBundlePullbackSiteMap_comp_of_comp_eq g E hfree m n w hθ) w
      (representedSpaceMap_siteToChart_comp_chartToSpace_comp_of_hom g E hfree m)
      (chartBundleTautological E (bundleBaseChart X))
      (schemeReadingModulePullbackIso g E (chartToSpace B S hS X' V)).inv
      (chartBundleModulePullbackIso g E n w) rfl
        (chartBundleTautological ((modulePullback B S hS g).obj E) V)
      (Stacks.RelativeProj.tautologicalDatumTwistBaseChangeIso (chartSiteSchemeHom n)
        (chartBundleModule E (bundleBaseChart X))
          (chartBundleModule ((modulePullback B S hS g).obj E) V)
        (chartBundleModulePullbackIso g E n w))
      (tautologicalDatumTwistBaseChangeIso_spec_chartBundlePullbackSiteMap g E hfree n w
        _ rfl _ rfl _ rfl _ rfl)
      (isQuasicoherentOnSite_projectiveBundleChartModule E hfree)
      (isQuasicoherentOnSite_projectiveBundleChartTwist E hfree)
      (projectiveBundleChartTwistReadingIso E hfree) (projectiveBundleChartQuotient E hfree)
      (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E hfree)
        (projectiveBundleProj E hfree) _ rfl E).symm
      (quotientReadingHyp_projectiveBundle E hfree))⟩

/-- **The two quotients agree on a chart, given an isomorphism of the two readings**: the step
of `AlgebraicGeometry.Space.exists_iso_modulePullback_projectiveBundleChartOfHom` after the
comparison of the readings, as an instance of
`AlgebraicGeometry.Space.exists_iso_modulePullback_comp_of_square`. -/
theorem exists_iso_modulePullback_projectiveBundleChartOfHom_of_iso
    (hθ : (representedSpaceMap B S hS
      ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteMap m) ≫ projectiveBundleAtlas
      ((modulePullback B S hS g).obj E) (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)) ≫
      (projectiveBundlePullbackMap g E hfree) =
      (representedSpaceMap B S hS (chartBundlePullbackSiteMap g E hfree n w)) ≫
      (projectiveBundleAtlas E hfree))
    (γ : (modulePullback B S hS
      (representedSpaceMap B S hS (chartBundlePullbackSiteMap g E hfree n w))).obj
      (projectiveBundleChartTwist E hfree) ≅
      (modulePullback B S hS
        (representedSpaceMap B S hS
        ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteMap m))).obj
        (projectiveBundleChartTwist ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)))
    (hγ : QuotientIsoComp
      ((modulePullback B S hS
      (representedSpaceMap B S hS (chartBundlePullbackSiteMap g E hfree n w))).map
      (projectiveBundleChartQuotient E hfree)) γ
      ((((modulePullback B S hS
        (representedSpaceMap B S hS (chartBundlePullbackSiteMap g E hfree n w))).mapIso
        (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E hfree)
        (projectiveBundleProj E hfree) _ rfl E).symm ≪≫
          (QuasiCoherentDescent.pullbackComparison B S hS
            (representedSpaceMap B S hS (chartBundlePullbackSiteMap g E hfree n w))
            ((projectiveBundleAtlas E hfree) ≫ (projectiveBundleProj E hfree))
            ((projectiveBundleChartOfHom ((modulePullback B S hS g).obj E)
            (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree) m ≫
            (projectiveBundleProj ((modulePullback B S hS g).obj E)
            (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))) ≫ g)
            (representedSpaceMap_chartBundlePullbackSiteMap_comp_of_comp_eq g E hfree m n w hθ)
            E).symm) ≪≫
          QuasiCoherentDescent.pullbackComparison B S hS
            (projectiveBundleChartOfHom ((modulePullback B S hS g).obj E)
            (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree) m ≫
            (projectiveBundleProj ((modulePullback B S hS g).obj E)
            (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))) g _ rfl E) ≪≫
        ((modulePullback B S hS
          (representedSpaceMap B S hS
          ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
          (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteMap m))).mapIso
          (QuasiCoherentDescent.pullbackComparison B S hS
          (projectiveBundleAtlas ((modulePullback B S hS g).obj E)
          (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))
          (projectiveBundleProj ((modulePullback B S hS g).obj E)
          (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)) _ rfl
          ((modulePullback B S hS g).obj E)).symm ≪≫
          (QuasiCoherentDescent.pullbackComparison B S hS
            (representedSpaceMap B S hS
            ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
            (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteMap m))
            ((projectiveBundleAtlas ((modulePullback B S hS g).obj E)
            (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)) ≫
            (projectiveBundleProj ((modulePullback B S hS g).obj E)
            (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)))
            (projectiveBundleChartOfHom ((modulePullback B S hS g).obj E)
            (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree) m ≫
            (projectiveBundleProj ((modulePullback B S hS g).obj E)
            (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))) (Category.assoc _ _ _).symm
            ((modulePullback B S hS g).obj E)).symm).symm)
      ((modulePullback B S hS
        (representedSpaceMap B S hS
        ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteMap m))).map
        (projectiveBundleChartQuotient ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)))) :
    ∃ β : (modulePullback B S hS
      (representedSpaceMap B S hS
      ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteMap m) ≫ projectiveBundleAtlas
      ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))).obj
      ((modulePullback B S hS (projectiveBundlePullbackMap g E hfree)).obj
      (projectiveBundleTwist E hfree).obj) ≅
        (modulePullback B S hS
          (representedSpaceMap B S hS
          ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
          (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteMap m) ≫
          projectiveBundleAtlas ((modulePullback B S hS g).obj E)
          (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))).obj
          (projectiveBundleTwist ((modulePullback B S hS g).obj E)
          (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).obj,
      (modulePullback B S hS
        (representedSpaceMap B S hS
        ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteMap m) ≫ projectiveBundleAtlas
        ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))).map
        (((QuasiCoherentDescent.pullbackComparison B S hS
        (projectiveBundleProj ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)) g _ rfl E).symm ≪≫
        QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundlePullbackMap g E hfree)
        (projectiveBundleProj E hfree) _ (projectiveBundlePullbackMap_comp_proj g E hfree) E).hom ≫
        (modulePullback B S hS (projectiveBundlePullbackMap g E hfree)).map
        (projectiveBundleTautological E hfree).hom) ≫ β.hom =
        (modulePullback B S hS
          (representedSpaceMap B S hS
          ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
          (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteMap m) ≫
          projectiveBundleAtlas ((modulePullback B S hS g).obj E)
          (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))).map
          (X := (modulePullback B S hS
          (projectiveBundleProj ((modulePullback B S hS g).obj E)
          (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))).obj
          ((modulePullback B S hS g).obj E))
          (projectiveBundleTautological ((modulePullback B S hS g).obj E)
            (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).hom :=
by
  have hq₁ : ModulePullbackFactor (projectiveBundleAtlas E hfree)
      (projectiveBundleTautological E hfree).hom (projectiveBundleTwistAtlasIso E hfree)
      (projectiveBundleChartQuotient E hfree) :=
    modulePullback_map_projectiveBundleTautological E hfree
  have hq₂ : ModulePullbackFactor
    (projectiveBundleAtlas ((modulePullback B S hS g).obj E)
    (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))
      (projectiveBundleTautological ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).hom
        (projectiveBundleTwistAtlasIso ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))
      (projectiveBundleChartQuotient ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)) :=
    modulePullback_map_projectiveBundleTautological ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)
  exact
    exists_iso_modulePullback_comp_of_square g (projectiveBundlePullbackMap g E hfree)
    (projectiveBundleProj E hfree)
    (projectiveBundleProj ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))
    (projectiveBundlePullbackMap_comp_proj g E hfree)
    (representedSpaceMap B S hS
      ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteMap m) ≫ projectiveBundleAtlas
      ((modulePullback B S hS g).obj E) (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))
    (representedSpaceMap B S hS (chartBundlePullbackSiteMap g E hfree n w))
      (projectiveBundleAtlas E hfree) hθ
    (representedSpaceMap B S hS
      ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteMap m))
    (projectiveBundleAtlas ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)) rfl
    (projectiveBundleChartOfHom ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree) m ≫ projectiveBundleProj
      ((modulePullback B S hS g).obj E) (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))
    rfl (representedSpaceMap_chartBundlePullbackSiteMap_comp_of_comp_eq g E hfree m n w hθ)
    (Category.assoc _ _ _).symm E (projectiveBundleTautological E hfree).hom
    (projectiveBundleTautological ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).hom
    (projectiveBundleTwistAtlasIso E hfree) (projectiveBundleChartQuotient E hfree)
    hq₁
    (projectiveBundleTwistAtlasIso ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))
    (projectiveBundleChartQuotient ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))
    hq₂
    γ hγ


/-- **The two quotients agree on a chart**: for a chart `V` of `X'` with morphisms `m : V ⟶ U'`
and `n : V ⟶ U` over `g`, such that the chart `a : 𝐏(g^*ℰ|_V) ⟶ 𝐏(g^*ℰ)` over `m` followed by `θ`
is `𝐏(g^*ℰ|_V) ⟶ 𝐏(ℰ|_U) ⟶ 𝐏(ℰ)`, the inverse images along `a` of the inverse image along `θ` of
the tautological quotient of `P` and of the tautological quotient of `Q` are isomorphic
quotients.  Both read on the scheme `𝐏(g^*ℰ|_V)` as its tautological quotient, by Stacks 01O3
along `m` and along `n`. -/
theorem exists_iso_modulePullback_projectiveBundleChartOfHom
    (hθ : (representedSpaceMap B S hS
      ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteMap m) ≫ projectiveBundleAtlas
      ((modulePullback B S hS g).obj E) (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)) ≫
      (projectiveBundlePullbackMap g E hfree) =
      (representedSpaceMap B S hS (chartBundlePullbackSiteMap g E hfree n w)) ≫
      (projectiveBundleAtlas E hfree)) :
    ∃ β : (modulePullback B S hS
      (representedSpaceMap B S hS
      ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteMap m) ≫ projectiveBundleAtlas
      ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))).obj
      ((modulePullback B S hS (projectiveBundlePullbackMap g E hfree)).obj
      (projectiveBundleTwist E hfree).obj) ≅
        (modulePullback B S hS
          (representedSpaceMap B S hS
          ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
          (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteMap m) ≫
          projectiveBundleAtlas ((modulePullback B S hS g).obj E)
          (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))).obj
          (projectiveBundleTwist ((modulePullback B S hS g).obj E)
          (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).obj,
      (modulePullback B S hS
        (representedSpaceMap B S hS
        ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteMap m) ≫ projectiveBundleAtlas
        ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))).map
        (((QuasiCoherentDescent.pullbackComparison B S hS
        (projectiveBundleProj ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)) g _ rfl E).symm ≪≫
        QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundlePullbackMap g E hfree)
        (projectiveBundleProj E hfree) _ (projectiveBundlePullbackMap_comp_proj g E hfree) E).hom ≫
        (modulePullback B S hS (projectiveBundlePullbackMap g E hfree)).map
        (projectiveBundleTautological E hfree).hom) ≫ β.hom =
        (modulePullback B S hS
          (representedSpaceMap B S hS
          ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
          (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteMap m) ≫
          projectiveBundleAtlas ((modulePullback B S hS g).obj E)
          (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))).map
          (X := (modulePullback B S hS
          (projectiveBundleProj ((modulePullback B S hS g).obj E)
          (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))).obj
          ((modulePullback B S hS g).obj E))
          (projectiveBundleTautological ((modulePullback B S hS g).obj E)
            (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).hom := by
  obtain ⟨ε₂, h₂⟩ := exists_quotientReadingHyp_siteMap_projectiveBundleChartQuotient g E hfree m
  obtain ⟨ε₁, h₁⟩ :=
    exists_quotientReadingHyp_chartBundlePullbackSiteMap_projectiveBundleChartQuotient g E hfree m n
      w hθ
  obtain ⟨γ, hγ⟩ := exists_iso_comp_eq_of_quotientReadingHyp ((modulePullback B S hS g).obj E)
    (isQuasicoherentOnSite_modulePullback_obj_of_isQuasicoherentOnSite g E hE)
    (representedSpaceMap_siteToChart_comp_chartToSpace_of_hom g E hfree m)
    (chartBundleTautological ((modulePullback B S hS g).obj E) V) h₁ h₂
    (by
      exact isQuasicoherentOnSite_modulePullback_representedSpaceMap B S hS
        (chartBundlePullbackSiteMap g E hfree n w) (relativelyRepresentable_yoneda_map B S hS _) _
        (isQuasicoherentOnSite_projectiveBundleChartModule E hfree))
    (by
      exact isQuasicoherentOnSite_modulePullback_representedSpaceMap B S hS
        (chartBundlePullbackSiteMap g E hfree n w) (relativelyRepresentable_yoneda_map B S hS _) _
        (isQuasicoherentOnSite_projectiveBundleChartTwist E hfree))
    (by
      exact isQuasicoherentOnSite_modulePullback_representedSpaceMap B S hS
        ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
          (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteMap m)
          (relativelyRepresentable_yoneda_map B S hS _) _
        (isQuasicoherentOnSite_projectiveBundleChartTwist ((modulePullback B S hS g).obj E)
          (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)))
  exact exists_iso_modulePullback_projectiveBundleChartOfHom_of_iso g E hfree m n w hθ γ hγ

end Chart

/-! ### The isomorphism `θ^*𝒪_P(1) ≅ 𝒪_Q(1)` -/

section W

/-- `a ≫ θ` is `𝐏(g^*ℰ|_W) ⟶ 𝐏(ℰ|_U) ⟶ 𝐏(ℰ)`, in the spelling of
`AlgebraicGeometry.Space.exists_iso_modulePullback_projectiveBundleChartOfHom`. -/
theorem projectiveBundleChartAtlas_comp_projectiveBundlePullbackMap_presentingFiberChart :
    (representedSpaceMap B S hS
      ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteMap
      (presentingFiberChartHom g)) ≫
        projectiveBundleAtlas ((modulePullback B S hS g).obj E)
          (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)) ≫
          (projectiveBundlePullbackMap g E hfree) =
      (representedSpaceMap B S hS
        (chartBundlePullbackSiteMap g E hfree (presentingFiberChartFstOver g)
        (presentingFiberChartFst_w g))) ≫ projectiveBundleAtlas E hfree :=
  presentingFiberChartAtlas_comp_projectiveBundlePullbackMap g E hfree

/-- The chart `a : 𝐏(g^*ℰ|_W) ⟶ 𝐏(g^*ℰ)` is flat. -/
theorem isFlat_projectiveBundleChartAtlas_presentingFiberChart :
    IsFlat B S hS (representedSpaceMap B S hS
      ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteMap
      (presentingFiberChartHom g)) ≫
        projectiveBundleAtlas ((modulePullback B S hS g).obj E)
          (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).hom :=
  isFlat_of_isEtale B S hS (isEtale_presentingFiberChartAtlas g E hfree)

/-- The chart `a : 𝐏(g^*ℰ|_W) ⟶ 𝐏(g^*ℰ)` is surjective. -/
theorem isSurjective_projectiveBundleChartAtlas_presentingFiberChart :
    IsSurjective B S hS (representedSpaceMap B S hS
      ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteMap
      (presentingFiberChartHom g)) ≫
        projectiveBundleAtlas ((modulePullback B S hS g).obj E)
          (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).hom :=
  surjective_pointsMap_presentingFiberChartAtlas g E hfree

/-- The compatibility of an isomorphism `e : θ^*𝒪_P(1) ≅ 𝒪_Q(1)` with the tautological quotients:
`π'^*g^*ℰ ≅ θ^*π^*ℰ ⟶ θ^*𝒪_P(1)` followed by `e` is `π'^*g^*ℰ ⟶ 𝒪_Q(1)`.  It is a structure, so
that the isomorphism chosen from `AlgebraicGeometry.Space.exists_projectiveBundleTwistPullbackIso`
mentions only its name. -/
structure IsProjectiveBundleTwistPullbackIso
    (e : (modulePullback B S hS (projectiveBundlePullbackMap g E hfree)).obj
      (projectiveBundleTwist E hfree).obj ≅
      (projectiveBundleTwist ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).obj) : Prop where
  /-- `π'^*g^*ℰ ≅ θ^*π^*ℰ ⟶ θ^*𝒪_P(1) ≅ 𝒪_Q(1)` is the tautological quotient. -/
  comp_hom : (((QuasiCoherentDescent.pullbackComparison B S hS
    (projectiveBundleProj ((modulePullback B S hS g).obj E)
    (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)) g _ rfl E).symm ≪≫
        QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundlePullbackMap g E hfree)
          (projectiveBundleProj E hfree) _
          (projectiveBundlePullbackMap_comp_proj g E hfree) E).hom ≫
      (modulePullback B S hS (projectiveBundlePullbackMap g E hfree)).map
        (projectiveBundleTautological E hfree).hom) ≫ e.hom =
        (projectiveBundleTautological ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).hom

/-- **The inverse image along `θ : 𝐏(g^*ℰ) ⟶ 𝐏(ℰ)` of the twist `𝒪_{𝐏(ℰ)}(1)` is the twist
`𝒪_{𝐏(g^*ℰ)}(1)`, compatibly with the tautological quotients**: the two quotients
`π'^*g^*ℰ ≅ θ^*π^*ℰ ⟶ θ^*𝒪_{𝐏(ℰ)}(1)` and `π'^*g^*ℰ ⟶ 𝒪_{𝐏(g^*ℰ)}(1)` are isomorphic, since they
are after the inverse image along the flat surjective chart `𝐏(g^*ℰ|_W) ⟶ 𝐏(g^*ℰ)`
(`AlgebraicGeometry.Space.exists_iso_modulePullback_projectiveBundleChartOfHom`), and a quotient is
determined by its inverse image along a flat surjection
(`AlgebraicGeometry.Space.quotientIsoOfModulePullbackIsFlatOfSurjective`). -/
theorem exists_projectiveBundleTwistPullbackIso :
    ∃ e : (modulePullback B S hS (projectiveBundlePullbackMap g E hfree)).obj
      (projectiveBundleTwist E hfree).obj ≅
      (projectiveBundleTwist ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).obj,
        IsProjectiveBundleTwistPullbackIso g E hfree e :=
  ⟨_,
    ⟨comp_quotientIsoOfModulePullbackIsFlatOfSurjectiveOfComp_hom
      (projectiveBundlePullbackMap g E hfree)
    (N := (modulePullback B S hS (projectiveBundleProj E hfree)).obj E)
    (projectiveBundleTautological E hfree).hom (epi_projectiveBundleTautological E hfree)
    ((QuasiCoherentDescent.pullbackComparison B S hS
      (projectiveBundleProj ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)) g _ rfl E).symm ≪≫
      QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundlePullbackMap g E hfree)
        (projectiveBundleProj E hfree) _
        (projectiveBundlePullbackMap_comp_proj g E hfree) E)
    (projectiveBundleTautological ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).hom
    (epi_projectiveBundleTautological ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))
    (representedSpaceMap B S hS
      ((projectiveBundleChartFamily ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).siteMap
      (presentingFiberChartHom g)) ≫
        projectiveBundleAtlas ((modulePullback B S hS g).obj E)
          (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree))
    (isFlat_projectiveBundleChartAtlas_presentingFiberChart g E hfree)
    (isSurjective_projectiveBundleChartAtlas_presentingFiberChart g E hfree)
    (exists_iso_modulePullback_projectiveBundleChartOfHom g E hfree (presentingFiberChartHom g)
      (presentingFiberChartFstOver g) (presentingFiberChartFst_w g)
      (projectiveBundleChartAtlas_comp_projectiveBundlePullbackMap_presentingFiberChart g E
        hfree))⟩⟩

/-- **The isomorphism `θ^*𝒪_{𝐏(ℰ)}(1) ≅ 𝒪_{𝐏(g^*ℰ)}(1)`** of
`AlgebraicGeometry.Space.exists_projectiveBundleTwistPullbackIso`. -/
def projectiveBundleTwistPullbackIso :
    (modulePullback B S hS (projectiveBundlePullbackMap g E hfree)).obj
      (projectiveBundleTwist E hfree).obj ≅
      (projectiveBundleTwist ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).obj :=
  (exists_projectiveBundleTwistPullbackIso g E hfree).choose

/-- **`θ^*𝒪_P(1) ≅ 𝒪_Q(1)` carries the inverse image of the tautological quotient to the
tautological quotient**: the composite `π'^*g^*ℰ ≅ θ^*π^*ℰ ⟶ θ^*𝒪_P(1) ≅ 𝒪_Q(1)` is the
tautological quotient `π'^*g^*ℰ ⟶ 𝒪_Q(1)`. -/
@[reassoc]
theorem comp_projectiveBundleTwistPullbackIso_hom :
    (((QuasiCoherentDescent.pullbackComparison B S hS
      (projectiveBundleProj ((modulePullback B S hS g).obj E)
      (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)) g _ rfl E).symm ≪≫
        QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundlePullbackMap g E hfree)
          (projectiveBundleProj E hfree) _
          (projectiveBundlePullbackMap_comp_proj g E hfree) E).hom ≫
      (modulePullback B S hS (projectiveBundlePullbackMap g E hfree)).map
        (projectiveBundleTautological E hfree).hom) ≫
        (projectiveBundleTwistPullbackIso g E hfree).hom =
        (projectiveBundleTautological ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).hom :=
  (exists_projectiveBundleTwistPullbackIso g E hfree).choose_spec.comp_hom

/-- **`Θ^*(g'^*𝒪_P(1)) ≅ 𝒪_Q(1)`** for the identification `Θ : Q = 𝐏(g^*ℰ) ≅ P ×_X X'` of
`AlgebraicGeometry.Space.projectiveBundlePullbackIso` and the projection `g' : P ×_X X' ⟶ P`:
`AlgebraicGeometry.Space.projectiveBundleTwistPullbackIso` through `θ = Θ ≫ g'`. -/
def projectiveBundleTwistFiberProductIso :
    (modulePullback B S hS (projectiveBundlePullbackIso g E hfree).hom).obj
        ((modulePullback B S hS (projectiveBundleFiberProductFst g E hfree)).obj
          (projectiveBundleTwist E hfree).obj) ≅
      (projectiveBundleTwist ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree)).obj :=
  (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundlePullbackIso g E hfree).hom
      (projectiveBundleFiberProductFst g E hfree) (projectiveBundlePullbackMap g E hfree) rfl
      (projectiveBundleTwist E hfree).obj).symm ≪≫
    projectiveBundleTwistPullbackIso g E hfree

end W

end Twist

end AlgebraicGeometry.Space

end
