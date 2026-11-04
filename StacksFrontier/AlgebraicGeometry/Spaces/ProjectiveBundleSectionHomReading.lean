module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionSectionRegular

/-!
# The reading of a hyperplane section of a projective bundle on its presenting chart

Let `X` be an algebraic space, `ℰ` a finite locally free `𝒪_X`-module with projective bundle
`π : P = 𝐏(ℰ) ⟶ X`, and `σ : 𝒪_X ⟶ ℰ` a global section. It gives the morphism
`𝒪_P ≅ π^*𝒪_X ⟶ π^*ℰ ⟶ 𝒪_P(1)`, the hyperplane section of `σ`. This file reads its inverse image
along the atlas `P_U ⟶ P` on the scheme `P_U = 𝐏(ℰ|_U)` of the presenting chart: up to
isomorphisms of source and target it is `ρ^*σ_U ≫ τ_U`, for `ρ : P_U ⟶ U` the projection, `σ_U`
the reading of `σ` on the chart `U` and `τ_U` the tautological quotient of `𝐏(ℰ|_U)`.

This is the chain of identifications of
`AlgebraicGeometry.Space.mono_projectiveBundleSectionHom_of_comp_eq_id`, recorded as an equation
rather than as a transfer of injectivity.

## Main results

* `AlgebraicGeometry.Space.exists_representedZariski_map_projectiveBundleAtlas_sectionHom`.

## References

* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- The chain of identifications of the reading of a hyperplane section, at abstract categories
and functors, so that nothing in it unfolds a module of a projective bundle. -/
theorem _root_.CategoryTheory.Functor.map_map_map_comp_eq_of_chain {C₀ C₁ C₂ D₀ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category D₀] (G₁ : C₀ ⥤ C₁) (G₂ : C₁ ⥤ C₂)
    (G₃ : C₂ ⥤ D₀) {x y z w : C₀} {t v v' : C₁} {d₁ d₂ d₃ : D₀}
    (a : x ≅ y) (b : y ⟶ z) (c : z ⟶ w) (q : G₁.obj z ⟶ t) (κ : G₁.obj w ≅ t)
    (hc : G₁.map c = q ≫ κ.inv) (pc : v ≅ G₁.obj z) (pc' : v' ≅ G₁.obj y) (m : v' ⟶ v)
    (nat : G₁.map b ≫ pc.inv = pc'.inv ≫ m) (srpi : d₁ ≅ G₃.obj (G₂.obj v))
    (srpi' : d₂ ≅ G₃.obj (G₂.obj v')) (ρb : d₂ ⟶ d₁)
    (nat3 : ρb ≫ srpi.hom = srpi'.hom ≫ G₃.map (G₂.map m)) (taut : d₁ ⟶ d₃)
    (ε : G₃.obj (G₂.obj t) ≅ d₃)
    (hq : G₃.map (G₂.map q) = (G₃.mapIso (G₂.mapIso pc.symm)).hom ≫ srpi.inv ≫ taut ≫ ε.inv) :
    G₃.map (G₂.map (G₁.map (a.hom ≫ b ≫ c))) =
      (G₃.mapIso (G₂.mapIso (G₁.mapIso a ≪≫ pc'.symm)) ≪≫ srpi'.symm).hom ≫ ρb ≫ taut ≫
        (ε.symm ≪≫ G₃.mapIso (G₂.mapIso κ.symm)).hom := by
  have natR : G₃.map (G₂.map (G₁.map b)) ≫ G₃.map (G₂.map pc.inv) =
      G₃.map (G₂.map pc'.inv) ≫ G₃.map (G₂.map m) := by
    rw [← G₃.map_comp, ← G₂.map_comp, nat, G₂.map_comp, G₃.map_comp]
  have nat3' : G₃.map (G₂.map m) ≫ srpi.inv = srpi'.inv ≫ ρb := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← nat3, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  simp only [Functor.map_comp, hc, hq, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Category.assoc]
  rw [reassoc_of% natR, reassoc_of% nat3']

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (E : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]
  (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)

/-- **The inverse image of the hyperplane section of `σ` along the atlas `P_U ⟶ P`, read on the
scheme `P_U`**, is `ρ^*σ_U` followed by the tautological quotient of `𝐏(ℰ|_U)`, up to an
isomorphism of the sources and one of the targets. -/
theorem exists_representedZariski_map_projectiveBundleAtlas_sectionHom
    (σ : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O)) ⟶ E) :
    ∃ (A : (SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj (projectiveBundleChartPresentation E hfree).U)
          (projectiveBundleChartPresentation E hfree).U.left.property).obj
        ((representedSmallEtaleModuleEquivalence B S hS
          (projectiveBundleChartPresentation E hfree).U).inverse.obj
          ((modulePullback B S hS (projectiveBundleAtlas E hfree)).obj
            (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS (projectiveBundle E hfree).1
                (projectiveBundle E hfree).2).O))))) ≅
        (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
          (associatedBigEtaleSite B) (projectiveBundleChartProj E hfree).left)).obj
          (schemeReading (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O))) (chartToSpace B S hS X (bundleBaseChart X))))
      (C : chartBundleTwist E (bundleBaseChart X) ≅
        (SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj (projectiveBundleChartPresentation E hfree).U)
          (projectiveBundleChartPresentation E hfree).U.left.property).obj
        ((representedSmallEtaleModuleEquivalence B S hS
          (projectiveBundleChartPresentation E hfree).U).inverse.obj
          ((modulePullback B S hS (projectiveBundleAtlas E hfree)).obj
            (projectiveBundleTwist E hfree).obj))),
      (SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj (projectiveBundleChartPresentation E hfree).U)
          (projectiveBundleChartPresentation E hfree).U.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS
          (projectiveBundleChartPresentation E hfree).U).inverse.map
          ((modulePullback B S hS (projectiveBundleAtlas E hfree)).map
            ((modulePullbackUnitIso B S hS (projectiveBundleProj E hfree)).inv ≫
              (modulePullback B S hS (projectiveBundleProj E hfree)).map σ ≫
                (projectiveBundleTautological E hfree).hom))) =
        A.hom ≫ (Scheme.Modules.pullback (chartBundleToChart E (bundleBaseChart X))).map
          (schemeReadingMap (chartToSpace B S hS X (bundleBaseChart X)) σ) ≫
          chartBundleTautological E (bundleBaseChart X) ≫ C.hom := by
  -- the tautological quotient on the atlas is the chart quotient
  have hc : (modulePullback B S hS (projectiveBundleAtlas E hfree)).map
      (projectiveBundleTautological E hfree).hom =
        projectiveBundleChartQuotient E hfree ≫ (projectiveBundleTwistAtlasIso E hfree).inv := by
    rw [← modulePullback_map_projectiveBundleTautological E hfree, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  -- move `σ` past the comparison of iterated inverse images
  have nat := QuasiCoherentDescent.pullbackComparison_inv_naturality B S hS
    (projectiveBundleAtlas E hfree) (projectiveBundleProj E hfree) _ rfl σ
  -- move `σ` past the comparison of readings
  have nat3 := schemeReadingPullbackIso_hom_naturality (projectiveBundleChartProj E hfree)
    (representedSpaceMap_projectiveBundleChartProj_comp E hfree)
    (SheafOfModules.isQuasicoherentOnSite_unit _) hE σ
  rw [schemeReadingMap_projectiveBundleAtlas_comp_eq] at nat3
  refine ⟨(SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj (projectiveBundleChartPresentation E hfree).U)
      (projectiveBundleChartPresentation E hfree).U.left.property).mapIso
      ((representedSmallEtaleModuleEquivalence B S hS
        (projectiveBundleChartPresentation E hfree).U).inverse.mapIso
        ((modulePullback B S hS (projectiveBundleAtlas E hfree)).mapIso
          (modulePullbackUnitIso B S hS (projectiveBundleProj E hfree)).symm ≪≫
          (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E hfree)
            (projectiveBundleProj E hfree) _ rfl
            (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS X.1 X.2).O)))).symm)) ≪≫
      (schemeReadingPullbackIso (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O))) (SheafOfModules.isQuasicoherentOnSite_unit _)
        (projectiveBundleChartProj E hfree)
        (representedSpaceMap_projectiveBundleChartProj_comp E hfree)).symm,
    (projectiveBundleChartTwistReadingIso E hfree).symm ≪≫
      (SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj (projectiveBundleChartPresentation E hfree).U)
      (projectiveBundleChartPresentation E hfree).U.left.property).mapIso
      ((representedSmallEtaleModuleEquivalence B S hS
        (projectiveBundleChartPresentation E hfree).U).inverse.mapIso
        (projectiveBundleTwistAtlasIso E hfree).symm), ?_⟩
  exact Functor.map_map_map_comp_eq_of_chain
    (modulePullback B S hS (projectiveBundleAtlas E hfree))
    (representedSmallEtaleModuleEquivalence B S hS
      (projectiveBundleChartPresentation E hfree).U).inverse
    (SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj (projectiveBundleChartPresentation E hfree).U)
      (projectiveBundleChartPresentation E hfree).U.left.property)
    (modulePullbackUnitIso B S hS (projectiveBundleProj E hfree)).symm
    ((modulePullback B S hS (projectiveBundleProj E hfree)).map σ)
    (projectiveBundleTautological E hfree).hom
    (projectiveBundleChartQuotient E hfree) (projectiveBundleTwistAtlasIso E hfree) hc
    (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E hfree)
      (projectiveBundleProj E hfree) _ rfl E)
    (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E hfree)
      (projectiveBundleProj E hfree) _ rfl
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O))))
    _ nat
    (schemeReadingPullbackIso E hE (projectiveBundleChartProj E hfree)
      (representedSpaceMap_projectiveBundleChartProj_comp E hfree))
    (schemeReadingPullbackIso (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O))) (SheafOfModules.isQuasicoherentOnSite_unit _)
      (projectiveBundleChartProj E hfree)
      (representedSpaceMap_projectiveBundleChartProj_comp E hfree))
    _ nat3 (chartBundleTautological E (bundleBaseChart X))
    (projectiveBundleChartTwistReadingIso E hfree)
    ((representedZariski_map_projectiveBundleChartQuotient E hfree).trans
      ((projectiveBundleChartQuotientReading_eq_quotientReadingOf E hfree).trans
        (quotientReadingOf_chartBundleTautological_eq E hfree)))

end AlgebraicGeometry.Space

end
