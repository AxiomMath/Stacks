module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleSectionHomReading

/-!
# The reading of `π^*σ₀ ≫ (π^*ℰ ⟶ 𝒪(1))` on the presenting chart, for any source

Let `X` be an algebraic space, `ℰ` a finite locally free `𝒪_X`-module with projective bundle
`π : P = 𝐏(ℰ) ⟶ X`, and `σ₀ : 𝓜 ⟶ ℰ` a morphism from a quasi-coherent module. The composite
`π^*𝓜 ⟶ π^*ℰ ⟶ 𝒪_P(1)` pulled back along the atlas `P_U ⟶ P` reads on the scheme
`P_U = 𝐏(ℰ|_U)` as `ρ^*σ₀_U` followed by the tautological quotient of `𝐏(ℰ|_U)`, up to an
isomorphism of sources depending only on `𝓜` and an isomorphism of targets depending on nothing.

This is `AlgebraicGeometry.Space.exists_representedZariski_map_projectiveBundleAtlas_sectionHom`
for a general source, with both isomorphisms written out, so that two such readings can be
compared through their common target.

## Main results

* `AlgebraicGeometry.Space.exists_projectiveBundleAtlasReading_map_tautological_eq`.

## References

* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- The chain of identifications of the reading of `π^*σ₀ ≫ (π^*ℰ ⟶ 𝒪(1))`, at abstract
categories and functors, for a morphism `b` out of the inverse image of the source. -/
theorem _root_.CategoryTheory.Functor.map_map_map_comp_eq_of_chain_of_hom {C₀ C₁ C₂ D₀ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category D₀] (G₁ : C₀ ⥤ C₁) (G₂ : C₁ ⥤ C₂)
    (G₃ : C₂ ⥤ D₀) {y z w : C₀} {t v v' : C₁} {d₁ d₂ d₃ : D₀}
    (b : y ⟶ z) (c : z ⟶ w) (q : G₁.obj z ⟶ t) (κ : G₁.obj w ≅ t)
    (hc : G₁.map c = q ≫ κ.inv) (pc : v ≅ G₁.obj z) (pc' : v' ≅ G₁.obj y) (m : v' ⟶ v)
    (nat : G₁.map b ≫ pc.inv = pc'.inv ≫ m) (srpi : d₁ ≅ G₃.obj (G₂.obj v))
    (srpi' : d₂ ≅ G₃.obj (G₂.obj v')) (ρb : d₂ ⟶ d₁)
    (nat3 : ρb ≫ srpi.hom = srpi'.hom ≫ G₃.map (G₂.map m)) (taut : d₁ ⟶ d₃)
    (ε : G₃.obj (G₂.obj t) ≅ d₃)
    (hq : G₃.map (G₂.map q) = (G₃.mapIso (G₂.mapIso pc.symm)).hom ≫ srpi.inv ≫ taut ≫ ε.inv) :
    G₃.map (G₂.map (G₁.map (b ≫ c))) =
      (G₃.mapIso (G₂.mapIso pc'.symm) ≪≫ srpi'.symm).hom ≫ ρb ≫ taut ≫
        (ε.symm ≪≫ G₃.mapIso (G₂.mapIso κ.symm)).hom := by
  have h := Functor.map_map_map_comp_eq_of_chain G₁ G₂ G₃ (Iso.refl y) b c q κ hc pc pc' m nat
    srpi srpi' ρb nat3 taut ε hq
  simp only [Iso.refl_hom, Category.id_comp, Iso.trans_hom, Functor.mapIso_hom,
    CategoryTheory.Functor.map_id] at h ⊢
  exact h

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (E : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]
  (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)

/-- **The reading on `P_U` of `π^*σ₀ ≫ (π^*ℰ ⟶ 𝒪(1))`**, for `σ₀ : 𝓜 ⟶ ℰ` out of a quasi-coherent
module: an identification of the sources, `ρ^*σ₀_U`, the tautological quotient of `𝐏(ℰ|_U)` and
the target identification, which does not depend on `σ₀`. -/
theorem exists_projectiveBundleAtlasReading_map_tautological_eq (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (σ₀ : M ⟶ E) :
    ∃ (A : (SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj (projectiveBundleChartPresentation E hfree).U)
          (projectiveBundleChartPresentation E hfree).U.left.property).obj
        ((representedSmallEtaleModuleEquivalence B S hS
          (projectiveBundleChartPresentation E hfree).U).inverse.obj
          ((modulePullback B S hS (projectiveBundleAtlas E hfree)).obj
            ((modulePullback B S hS (projectiveBundleProj E hfree)).obj M))) ≅
        (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
          (associatedBigEtaleSite B) (projectiveBundleChartProj E hfree).left)).obj
          (schemeReading M (chartToSpace B S hS X (bundleBaseChart X)))),
      (SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj (projectiveBundleChartPresentation E hfree).U)
          (projectiveBundleChartPresentation E hfree).U.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS
          (projectiveBundleChartPresentation E hfree).U).inverse.map
          ((modulePullback B S hS (projectiveBundleAtlas E hfree)).map
            ((modulePullback B S hS (projectiveBundleProj E hfree)).map σ₀ ≫
              (projectiveBundleTautological E hfree).hom))) =
        A.hom ≫ (Scheme.Modules.pullback (chartBundleToChart E (bundleBaseChart X))).map
          (schemeReadingMap (chartToSpace B S hS X (bundleBaseChart X)) σ₀) ≫
          chartBundleTautological E (bundleBaseChart X) ≫
          ((projectiveBundleChartTwistReadingIso E hfree).symm ≪≫
            (SmallEtale.restrictModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj (projectiveBundleChartPresentation E hfree).U)
              (projectiveBundleChartPresentation E hfree).U.left.property).mapIso
              ((representedSmallEtaleModuleEquivalence B S hS
                (projectiveBundleChartPresentation E hfree).U).inverse.mapIso
                (projectiveBundleTwistAtlasIso E hfree).symm)).hom := by
  have hc : (modulePullback B S hS (projectiveBundleAtlas E hfree)).map
      (projectiveBundleTautological E hfree).hom =
        projectiveBundleChartQuotient E hfree ≫ (projectiveBundleTwistAtlasIso E hfree).inv := by
    rw [← modulePullback_map_projectiveBundleTautological E hfree, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have nat := QuasiCoherentDescent.pullbackComparison_inv_naturality B S hS
    (projectiveBundleAtlas E hfree) (projectiveBundleProj E hfree) _ rfl σ₀
  have nat3 := schemeReadingPullbackIso_hom_naturality (projectiveBundleChartProj E hfree)
    (representedSpaceMap_projectiveBundleChartProj_comp E hfree) hM hE σ₀
  rw [schemeReadingMap_projectiveBundleAtlas_comp_eq] at nat3
  refine ⟨(SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj (projectiveBundleChartPresentation E hfree).U)
      (projectiveBundleChartPresentation E hfree).U.left.property).mapIso
      ((representedSmallEtaleModuleEquivalence B S hS
        (projectiveBundleChartPresentation E hfree).U).inverse.mapIso
        (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E hfree)
          (projectiveBundleProj E hfree) _ rfl M).symm) ≪≫
      (schemeReadingPullbackIso M hM (projectiveBundleChartProj E hfree)
        (representedSpaceMap_projectiveBundleChartProj_comp E hfree)).symm, ?_⟩
  exact Functor.map_map_map_comp_eq_of_chain_of_hom
    (modulePullback B S hS (projectiveBundleAtlas E hfree))
    (representedSmallEtaleModuleEquivalence B S hS
      (projectiveBundleChartPresentation E hfree).U).inverse
    (SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj (projectiveBundleChartPresentation E hfree).U)
      (projectiveBundleChartPresentation E hfree).U.left.property)
    ((modulePullback B S hS (projectiveBundleProj E hfree)).map σ₀)
    (projectiveBundleTautological E hfree).hom
    (projectiveBundleChartQuotient E hfree) (projectiveBundleTwistAtlasIso E hfree) hc
    (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E hfree)
      (projectiveBundleProj E hfree) _ rfl E)
    (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E hfree)
      (projectiveBundleProj E hfree) _ rfl M)
    _ nat
    (schemeReadingPullbackIso E hE (projectiveBundleChartProj E hfree)
      (representedSpaceMap_projectiveBundleChartProj_comp E hfree))
    (schemeReadingPullbackIso M hM (projectiveBundleChartProj E hfree)
      (representedSpaceMap_projectiveBundleChartProj_comp E hfree))
    _ nat3 (chartBundleTautological E (bundleBaseChart X))
    (projectiveBundleChartTwistReadingIso E hfree)
    ((representedZariski_map_projectiveBundleChartQuotient E hfree).trans
      ((projectiveBundleChartQuotientReading_eq_quotientReadingOf E hfree).trans
        (quotientReadingOf_chartBundleTautological_eq E hfree)))

end AlgebraicGeometry.Space

end
