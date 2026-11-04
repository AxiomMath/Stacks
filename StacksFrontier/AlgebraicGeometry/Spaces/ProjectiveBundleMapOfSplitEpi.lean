module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.EpiClosedImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianChartFamilyHom
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionSectionRegular

/-!
# The closed immersion of projective bundles of a split quotient on an algebraic space

Let `X` be an algebraic space over `S` and `u : ℰ ⟶ ℰ'` a morphism of finite locally free
`𝒪_X`-modules with a section `σ : ℰ' ⟶ ℰ`, `σ ≫ u = 𝟙`. Over every étale chart `V` of `X` the
reading `u_V : ℰ|_V ⟶ ℰ'|_V` is a split epimorphism of quasi-coherent modules on the scheme `V`,
so it gives the closed immersion `𝐏(ℰ'|_V) ⟶ 𝐏(ℰ|_V)` of
`Stacks.RelativeProj.projectiveBundleMapOfEpi`. These commute with the morphisms of chart
bundles (`Stacks.RelativeProj.projectiveBundleMapOfEpi_comp_projectiveBundleBaseChange`), so they
form a morphism of cartesian chart families, which glues to a morphism

`𝐏(ℰ') ⟶ 𝐏(ℰ)`

of algebraic spaces over `X`. Over the presenting chart it is the closed immersion of the chart
bundles, and the square it forms with the two charts is cartesian, so it is a closed immersion.

## Main definitions

* `AlgebraicGeometry.Space.chartModuleMap`: the reading `ℰ|_V ⟶ ℰ'|_V` of `u` on a chart.
* `AlgebraicGeometry.Space.projectiveBundleChartFamilyHomOfSplitEpi`: the morphism of the chart
  families of the two projective bundles.
* `AlgebraicGeometry.Space.projectiveBundleMapOfSplitEpi`: **the morphism `𝐏(ℰ') ⟶ 𝐏(ℰ)`.**

## Main results

* `AlgebraicGeometry.Space.projectiveBundleMapOfSplitEpi_comp_projectiveBundleProj`: it lies over
  `X`.
* `AlgebraicGeometry.Space.isPullback_projectiveBundleMapOfSplitEpi`: over the presenting chart
  it is the closed immersion of the chart bundles, by a cartesian square.
* `AlgebraicGeometry.Space.isClosedImmersion_projectiveBundleMapOfSplitEpi`: **it is a closed
  immersion.**

## References

* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

section ChartModuleMap

variable {E E' : Modules.{u, u} B S hS X.1 X.2}

/-- The reading `ℰ|_V ⟶ ℰ'|_V` on the scheme of an étale chart `V` of a morphism of
`𝒪_X`-modules. -/
abbrev chartModuleMap (u : E ⟶ E') (V : SmallEtale B S hS X.1) :
    chartBundleModule E V ⟶ chartBundleModule E' V :=
  schemeReadingMap (T := (SmallEtale.toOver B S hS X.1).obj V) (chartToSpace B S hS X V) u

/-- The reading on the scheme of `T` of a split epimorphism is an epimorphism: each of the three
functors the reading is composed of carries a split epimorphism to a split epimorphism. -/
theorem epi_schemeReadingMap_of_comp_eq_id {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ X) (u : E ⟶ E') (σ : E' ⟶ E) (hσ : σ ≫ u = 𝟙 E') :
    Epi (schemeReadingMap ψ u) :=
  ((((⟨σ, hσ⟩ : SplitEpi u).map (modulePullback B S hS ψ)).map
    (representedSmallEtaleModuleEquivalence B S hS T).inverse).map
    (SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property)).epi

/-- The reading of a split epimorphism on a chart is an epimorphism. -/
theorem epi_chartModuleMap (u : E ⟶ E') (σ : E' ⟶ E) (hσ : σ ≫ u = 𝟙 E')
    (V : SmallEtale B S hS X.1) : Epi (chartModuleMap u V) :=
  epi_schemeReadingMap_of_comp_eq_id (T := (SmallEtale.toOver B S hS X.1).obj V)
    (chartToSpace B S hS X V) u σ hσ

end ChartModuleMap

variable (E E' : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]
  [hE' : E'.IsQuasicoherentOnSite] (u : E ⟶ E') (σ : E' ⟶ E) (hσ : σ ≫ u = 𝟙 E')

/-- The readings of `u` on two charts are intertwined by the identifications of the chart
modules, in the form `Stacks.RelativeProj.projectiveBundleMapOfEpi_comp_projectiveBundleBaseChange`
consumes. -/
theorem chartModuleMap_comp_chartBundleModuleIso_hom {V V' : SmallEtale B S hS X.1}
    (h : V' ⟶ V) :
    chartModuleMap u V' ≫ (chartBundleModuleIso E' h).hom =
      (chartBundleModuleIso E h).hom ≫
        (Scheme.Modules.pullback (chartSchemeMapOfSite h)).map (chartModuleMap u V) := by
  have nat := schemeReadingPullbackIso_hom_naturality ((SmallEtale.toOver B S hS X.1).map h)
    (representedSpaceMap_toOver_map_comp_chartToSpace h) hE hE' u
  show chartModuleMap u V' ≫ (schemeReadingPullbackIso E' hE' _ _).inv =
    (schemeReadingPullbackIso E hE _ _).inv ≫ _
  rw [Iso.comp_inv_eq, Category.assoc, nat, Iso.inv_hom_id_assoc]

variable (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)
  (hfree' : SheafOfModules.IsFiniteLocallyFreeOnSite E')

/-- **The morphism of chart families of the projective bundles of a split quotient**: over a
chart `V` the closed immersion `𝐏(ℰ'|_V) ⟶ 𝐏(ℰ|_V)` of the reading of `u`. -/
def projectiveBundleChartFamilyHomOfSplitEpi :
    (projectiveBundleChartFamily E' hfree').Hom (projectiveBundleChartFamily E hfree) where
  app V := @Stacks.RelativeProj.projectiveBundleMapOfEpi _ _ _ _ _ (chartModuleMap u V)
    (epi_chartModuleMap u σ hσ V)
  app_toChart V := @Stacks.RelativeProj.projectiveBundleMapOfEpi_comp_toBase _ _ _ _ _
    (chartModuleMap u V) (epi_chartModuleMap u σ hσ V)
  naturality {V V'} h :=
    (@Stacks.RelativeProj.projectiveBundleMapOfEpi_comp_projectiveBundleBaseChange _ _
      (chartSchemeMapOfSite h) _ _ _ _ (chartModuleMap u V) (epi_chartModuleMap u σ hσ V) _ _ _ _
      (chartModuleMap u V') (epi_chartModuleMap u σ hσ V') (chartBundleModuleIso E h)
      (chartBundleModuleIso E' h) (chartModuleMap_comp_chartBundleModuleIso_hom E E' u h)).symm

/-- **The morphism of projective bundles `𝐏(ℰ') ⟶ 𝐏(ℰ)` of a split quotient `u : ℰ ⟶ ℰ'`** of
finite locally free modules on an algebraic space: the closed immersions of the chart bundles,
glued. -/
def projectiveBundleMapOfSplitEpi : projectiveBundle E' hfree' ⟶ projectiveBundle E hfree :=
  (projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').glued
    (presentationRelationTargetHom (projectiveBundlePresentation X))
    (presentationRelationSourceHom (projectiveBundlePresentation X))
    (isPullback_projectiveBundlePresentation X)

/-- **The morphism of projective bundles of a split quotient lies over `X`.** -/
@[reassoc]
theorem projectiveBundleMapOfSplitEpi_comp_projectiveBundleProj :
    projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree' ≫ projectiveBundleProj E hfree =
      projectiveBundleProj E' hfree' :=
  (projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').glued_comp_quotientHom
    _ _ _

/-- The morphism restricts on the presenting chart to the closed immersion of the chart
bundles. -/
@[reassoc]
theorem projectiveBundleChart_comp_projectiveBundleMapOfSplitEpi :
    projectiveBundleChart E' hfree' ≫ (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree').hom =
      yoneda.map ((projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').siteApp
          (presentationChart (projectiveBundlePresentation X))) ≫
        projectiveBundleChart E hfree :=
  (projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').quotientChart_comp_glued
    _ _ _

/-- **Over the presenting chart the morphism is the closed immersion of the chart bundles**: the
square formed with the two charts is cartesian. -/
theorem isPullback_projectiveBundleMapOfSplitEpi :
    IsPullback (projectiveBundleChart E' hfree')
      (yoneda.map ((projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').siteApp
        (presentationChart (projectiveBundlePresentation X))))
      (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree').hom
      (projectiveBundleChart E hfree) :=
  (projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').isPullback_glued
    _ _ _ (surjective_projectiveBundlePresentation X)

/-- **The morphism of projective bundles of a split quotient is a closed immersion.** -/
theorem isClosedImmersion_projectiveBundleMapOfSplitEpi :
    IsClosedImmersion B S hS (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree').hom :=
  (projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').isClosedImmersion_glued
    _ _ _ (surjective_projectiveBundlePresentation X)
    (@Stacks.RelativeProj.isClosedImmersion_projectiveBundleMapOfEpi _ _ _ _ _ _
      (epi_chartModuleMap u σ hσ _))

/-- **The points of the image of `𝐏(ℰ') ⟶ 𝐏(ℰ)` on the presenting chart**: a point
`y : b ⟶ 𝐏(ℰ|_U)` of the chart bundle lands, through the chart, in the image of the closed
immersion exactly when the morphism of schemes `y` factors through the closed immersion of the
chart bundles `𝐏(ℰ'|_U) ⟶ 𝐏(ℰ|_U)`. -/
theorem projectiveBundleChart_app_mem_range_iff {b : BigFppfOver B S hS}
    (y : b ⟶ (projectiveBundleChartFamily E hfree).site
      (presentationChart (projectiveBundlePresentation X))) :
    (projectiveBundleChart E hfree).app (Opposite.op b) y ∈
        (Subfunctor.range (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree').hom).obj
          (Opposite.op b) ↔
      ∃ w : (BigFppfOver.toScheme B S hS).obj b ⟶
          chartBundle E' (presentationChart (projectiveBundlePresentation X)),
        w ≫ (projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').app
            (presentationChart (projectiveBundlePresentation X)) =
          (BigFppfOver.toScheme B S hS).map y := by
  rw [Subfunctor.range_obj]
  constructor
  · rintro ⟨z, hz⟩
    have hpb := isPullback_projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree'
    have hw : yonedaEquiv.symm z ≫ (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree').hom =
        yoneda.map y ≫ projectiveBundleChart E hfree := by
      apply yonedaEquiv.injective
      rwa [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]
    let l := hpb.lift (yonedaEquiv.symm z) (yoneda.map y) hw
    have hl : yoneda.preimage l ≫
        (projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').siteApp
          (presentationChart (projectiveBundlePresentation X)) = y := by
      apply yoneda.map_injective
      rw [Functor.map_comp, Functor.map_preimage]
      exact hpb.lift_snd _ _ hw
    exact ⟨(BigFppfOver.toScheme B S hS).map (yoneda.preimage l),
      ((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans
        (congrArg (BigFppfOver.toScheme B S hS).map hl)⟩
  · rintro ⟨w, hw⟩
    have hwy : ObjectProperty.homMk w ≫
        ((projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').siteApp
          (presentationChart (projectiveBundlePresentation X))).left = y.left := by
      apply ObjectProperty.hom_ext
      exact hw
    let w' : b ⟶ (projectiveBundleChartFamily E' hfree').site
        (presentationChart (projectiveBundlePresentation X)) :=
      Over.homMk (ObjectProperty.homMk w) (by
        rw [← Over.w ((projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').siteApp
          (presentationChart (projectiveBundlePresentation X))), ← Category.assoc, hwy]
        exact Over.w y)
    have hw' : w' ≫ (projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').siteApp
        (presentationChart (projectiveBundlePresentation X)) = y :=
      Over.OverMorphism.ext hwy
    refine ⟨(projectiveBundleChart E' hfree').app (Opposite.op b) w', ?_⟩
    have h := congrArg (fun k => k.app (Opposite.op b) w')
      (projectiveBundleChart_comp_projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree')
    simp only [FunctorToTypes.comp, yoneda_map_app] at h
    exact h.trans (congrArg (fun t => (projectiveBundleChart E hfree).app (Opposite.op b) t) hw')

end AlgebraicGeometry.Space

end
