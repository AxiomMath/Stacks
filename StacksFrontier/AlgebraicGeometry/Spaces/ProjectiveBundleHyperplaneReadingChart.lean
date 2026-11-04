module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalPullbackBaseChangeShape
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleHyperplaneReadingGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleMapOfSplitEpi

/-!
# The reading of `π^*σ₀ ≫ (π^*ℰ ⟶ 𝒪(1))` on an object over a chart bundle

Let `X` be an algebraic space, `ℰ` a finite locally free `𝒪_X`-module with projective bundle
`π : P = 𝐏(ℰ) ⟶ X`, `V` an étale chart of `X` with a morphism `m` to the presenting chart, and
`h : A ⟶ P_V` a morphism of the site into the chart bundle `P_V = 𝐏(ℰ|_V)`, with
`f : A ⟶ 𝐏(ℰ|_V)` its morphism of schemes. For `σ₀ : 𝓜 ⟶ ℰ` out of a quasi-coherent module, the
reading on the scheme `A` of the inverse image of `π^*σ₀ ≫ (π^*ℰ ⟶ 𝒪(1))` along
`A ⟶ P_V ⟶ P_U ⟶ P` is `g^*σ₀_V` followed by the quotient `f^*` of the tautological quotient
of `𝐏(ℰ|_V)` (`Stacks.RelativeProj.TautologicalDatum.overQuotientMap`), up to an isomorphism of
sources and an isomorphism of targets which does not depend on `σ₀`.

## Main results

* `AlgebraicGeometry.Space.exists_schemeReadingMap_chartBundle_tautological_eq`.

## References

* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- The assembly of the identifications of a reading, at an abstract functor `G`: a reading
`R = I ≫ G(P) ≫ I'` with `P = A ≫ Q ≫ C`, `G(Q) = s ≫ W ≫ T` and `N = s₂ ≫ W` is
`N` up to an isomorphism of sources and the isomorphism of targets `T ≫ G(C) ≫ I'`. -/
theorem _root_.CategoryTheory.Functor.eq_iso_comp_comp_iso_of_chain {C₀ C₁ : Type*} [Category C₀]
    [Category C₁] (G : C₀ ⥤ C₁) {x y m₁ m₂ m₃ : C₁} {a b a' c' b' : C₀}
    (P : a ⟶ b) (A₁ : a ≅ a') (Q₁ : a' ⟶ c') (Q₂ : c' ⟶ b') (Cc : b' ≅ b)
    (hA : P = A₁.hom ≫ Q₁ ≫ Q₂ ≫ Cc.hom)
    (R : x ⟶ y) (I : G.obj a ≅ x) (I' : G.obj b ≅ y)
    (h1 : R = I.inv ≫ G.map P ≫ I'.hom)
    (s : G.obj a' ≅ m₁) (W : m₁ ⟶ m₂) (T : m₂ ≅ G.obj b')
    (hBC : G.map (Q₁ ≫ Q₂) = s.hom ≫ W ≫ T.hom) (s₂ : m₃ ≅ m₁) (N : m₃ ⟶ m₂) (hO : N = s₂.hom ≫ W) :
    R = (I.symm ≪≫ G.mapIso A₁ ≪≫ s ≪≫ s₂.symm).hom ≫ N ≫ (T ≪≫ G.mapIso Cc ≪≫ I').hom := by
  subst h1 hA hO
  rw [← Category.assoc Q₁ Q₂ Cc.hom]
  simp only [Functor.map_comp, ← Functor.map_comp_assoc, hBC, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (E : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]
  (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)

/-- The reading on the presenting chart bundle along the atlas, written out. -/
theorem schemeReadingMap_projectiveBundleAtlas_eq
    {N N' : Modules.{u, u} B S hS (projectiveBundle E hfree).1 (projectiveBundle E hfree).2}
    (φ : N ⟶ N') :
    schemeReadingMap (T := (projectiveBundleChartPresentation E hfree).U)
        (projectiveBundleAtlas E hfree) φ =
      (SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj (projectiveBundleChartPresentation E hfree).U)
          (projectiveBundleChartPresentation E hfree).U.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS
          (projectiveBundleChartPresentation E hfree).U).inverse.map
          ((modulePullback B S hS (projectiveBundleAtlas E hfree)).map φ)) := by
  with_reducible rfl

section Spelling

variable {N₁ N₂ : Modules.{u, u} B S hS (projectiveBundle E hfree).1 (projectiveBundle E hfree).2}
  {Z₁ Z₂ :
    ((BigFppfOver.toScheme B S hS).obj (projectiveBundleChartPresentation E hfree).U).Modules}

/-- An isomorphism out of the written-out reading on `P_U`, as one out of the reading. -/
abbrev atlasReadingSourceIso
    (A' : (SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj (projectiveBundleChartPresentation E hfree).U)
          (projectiveBundleChartPresentation E hfree).U.left.property).obj
        ((representedSmallEtaleModuleEquivalence B S hS
          (projectiveBundleChartPresentation E hfree).U).inverse.obj
          ((modulePullback B S hS (projectiveBundleAtlas E hfree)).obj N₁)) ≅ Z₁) :
    schemeReading (T := (projectiveBundleChartPresentation E hfree).U) N₁
      (projectiveBundleAtlas E hfree) ≅ Z₁ := by
  with_reducible exact A'

/-- An isomorphism into the written-out reading on `P_U`, as one into the reading. -/
abbrev atlasReadingTargetIso
    (C' : Z₂ ≅ (SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj (projectiveBundleChartPresentation E hfree).U)
          (projectiveBundleChartPresentation E hfree).U.left.property).obj
        ((representedSmallEtaleModuleEquivalence B S hS
          (projectiveBundleChartPresentation E hfree).U).inverse.obj
          ((modulePullback B S hS (projectiveBundleAtlas E hfree)).obj N₂))) :
    Z₂ ≅ schemeReading (T := (projectiveBundleChartPresentation E hfree).U) N₂
      (projectiveBundleAtlas E hfree) := by
  with_reducible exact C'

/-- An equation for the written-out reading on `P_U`, as one for the reading. -/
theorem schemeReadingMap_projectiveBundleAtlas_eq_of_eq (φ : N₁ ⟶ N₂)
    (A' : (SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj (projectiveBundleChartPresentation E hfree).U)
          (projectiveBundleChartPresentation E hfree).U.left.property).obj
        ((representedSmallEtaleModuleEquivalence B S hS
          (projectiveBundleChartPresentation E hfree).U).inverse.obj
          ((modulePullback B S hS (projectiveBundleAtlas E hfree)).obj N₁)) ≅ Z₁)
    {Z₃ : ((BigFppfOver.toScheme B S hS).obj (projectiveBundleChartPresentation E hfree).U).Modules}
    (Y₁ : Z₁ ⟶ Z₃) (Y₂ : Z₃ ⟶ Z₂)
    (C' : Z₂ ≅ (SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj (projectiveBundleChartPresentation E hfree).U)
          (projectiveBundleChartPresentation E hfree).U.left.property).obj
        ((representedSmallEtaleModuleEquivalence B S hS
          (projectiveBundleChartPresentation E hfree).U).inverse.obj
          ((modulePullback B S hS (projectiveBundleAtlas E hfree)).obj N₂)))
    (h : (SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj (projectiveBundleChartPresentation E hfree).U)
          (projectiveBundleChartPresentation E hfree).U.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS
          (projectiveBundleChartPresentation E hfree).U).inverse.map
          ((modulePullback B S hS (projectiveBundleAtlas E hfree)).map φ)) =
      A'.hom ≫ Y₁ ≫ Y₂ ≫ C'.hom) :
    schemeReadingMap (T := (projectiveBundleChartPresentation E hfree).U)
        (projectiveBundleAtlas E hfree) φ =
      (atlasReadingSourceIso E hfree A').hom ≫ Y₁ ≫ Y₂ ≫
        (atlasReadingTargetIso E hfree C').hom := by
  with_reducible exact h

end Spelling

/-- **The reading on an object over the presenting chart bundle**: for `k : A ⟶ P_U`, the reading
on `A` along `A ⟶ P_U ⟶ P` of a morphism of modules on `P` is the pullback along `k` of its
reading on `P_U`, up to the comparison isomorphisms of readings. -/
theorem schemeReadingMap_comp_projectiveBundleAtlas_eq {A : BigFppfOver B S hS}
    (k : A ⟶ (projectiveBundleChartPresentation E hfree).U)
    {N N' : Modules.{u, u} B S hS (projectiveBundle E hfree).1 (projectiveBundle E hfree).2}
    (hN : N.IsQuasicoherentOnSite) (hN' : N'.IsQuasicoherentOnSite) (φ : N ⟶ N') :
    schemeReadingMap (representedSpaceMap B S hS k ≫ projectiveBundleAtlas E hfree) φ =
      (schemeReadingPullbackIso N hN k (ψ := projectiveBundleAtlas E hfree) rfl).inv ≫
        (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
          (associatedBigEtaleSite B) k.left)).map
          (schemeReadingMap (T := (projectiveBundleChartPresentation E hfree).U)
            (projectiveBundleAtlas E hfree) φ) ≫
        (schemeReadingPullbackIso N' hN' k (ψ := projectiveBundleAtlas E hfree) rfl).hom := by
  have nat := schemeReadingPullbackIso_hom_naturality k (ψ := projectiveBundleAtlas E hfree) rfl
    hN hN' φ
  rw [Iso.eq_inv_comp]
  exact nat.symm

attribute [local implicit_reducible] AlgebraicGeometry.Space.CartesianChartFamily.site
  AlgebraicGeometry.BigFppfOver.siteObjectOver
  AlgebraicGeometry.Space.CartesianChartFamily.siteToChart
  AlgebraicGeometry.BigFppfOver.siteMapOver

variable {V : SmallEtale B S hS X.1} (m : V ⟶ bundleBaseChart X) {A : BigFppfOver B S hS}
  (h : A ⟶ (projectiveBundleChartFamily E hfree).site V)

/-- The morphism of schemes `A ⟶ 𝐏(ℰ|_V)` of `h`. -/
abbrev chartBundleHomOfSite :
    (BigFppfOver.toScheme B S hS).obj A ⟶ chartBundle E V :=
  _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) h.left

/-- The morphism of the site `A ⟶ P_V ⟶ P_U`. -/
abbrev chartBundleHomOfSiteToPresenting : A ⟶ (projectiveBundleChartPresentation E hfree).U :=
  h ≫ (projectiveBundleChartFamily E hfree).siteMap m

/-- The morphism of schemes underlying `A ⟶ P_V ⟶ P_U` is the composite
`A ⟶ 𝐏(ℰ|_V) ⟶ 𝐏(ℰ|_U)`. -/
theorem schemeHom_chartBundleHomOfSiteToPresenting :
    _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        (chartBundleHomOfSiteToPresenting E hfree m h).left =
      chartBundleHomOfSite E hfree h ≫ chartBundleMap E m :=
  rfl

/-- **The reading on `A` of `π^*σ₀ ≫ (π^*ℰ ⟶ 𝒪(1))`**, along `A ⟶ P_V ⟶ P_U ⟶ P`: it is
`g^*σ₀_V` followed by the pulled-back tautological quotient of `𝐏(ℰ|_V)` along `f : A ⟶ 𝐏(ℰ|_V)`,
up to an isomorphism of sources and an isomorphism of targets which does not depend on `σ₀`. -/
theorem exists_schemeReadingMap_chartBundle_tautological_eq :
    ∃ Tgt : (Scheme.Modules.pullback (chartBundleHomOfSite E hfree h)).obj
          (chartBundleTwist E V) ≅
        schemeReading (projectiveBundleTwist E hfree).obj
          (representedSpaceMap B S hS (chartBundleHomOfSiteToPresenting E hfree m h) ≫
            projectiveBundleAtlas E hfree),
      ∀ (M : Modules.{u, u} B S hS X.1 X.2) (_ : M.IsQuasicoherentOnSite) (σ₀ : M ⟶ E),
        ∃ Src : schemeReading ((modulePullback B S hS (projectiveBundleProj E hfree)).obj M)
              (representedSpaceMap B S hS (chartBundleHomOfSiteToPresenting E hfree m h) ≫
                projectiveBundleAtlas E hfree) ≅
            (Scheme.Modules.pullback (chartBundleHomOfSite E hfree h ≫ chartBundleToChart E V)).obj
              (schemeReading M (chartToSpace B S hS X V)),
          schemeReadingMap (representedSpaceMap B S hS
              (chartBundleHomOfSiteToPresenting E hfree m h) ≫ projectiveBundleAtlas E hfree)
              ((modulePullback B S hS (projectiveBundleProj E hfree)).map σ₀ ≫
                (projectiveBundleTautological E hfree).hom) =
            Src.hom ≫ ((Scheme.Modules.pullback
                (chartBundleHomOfSite E hfree h ≫ chartBundleToChart E V)).map
                (schemeReadingMap (chartToSpace B S hS X V) σ₀) ≫
              (Stacks.RelativeProj.tautologicalDatum (chartBundleModule E V)).overQuotientMap
                (chartBundleHomOfSite E hfree h) rfl) ≫ Tgt.hom := by
  refine ⟨((Scheme.Modules.pullback (chartBundleHomOfSite E hfree h)).mapIso
      (chartBundleTwistIso E m).symm ≪≫
      (Scheme.Modules.pullbackComp (chartBundleHomOfSite E hfree h) (chartBundleMap E m)).app
        (chartBundleTwist E (bundleBaseChart X))) ≪≫
    (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
      (associatedBigEtaleSite B) (chartBundleHomOfSiteToPresenting E hfree m h).left)).mapIso
      (atlasReadingTargetIso E hfree ((projectiveBundleChartTwistReadingIso E hfree).symm ≪≫
        (SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj (projectiveBundleChartPresentation E hfree).U)
          (projectiveBundleChartPresentation E hfree).U.left.property).mapIso
          ((representedSmallEtaleModuleEquivalence B S hS
            (projectiveBundleChartPresentation E hfree).U).inverse.mapIso
            (projectiveBundleTwistAtlasIso E hfree).symm))) ≪≫
    schemeReadingPullbackIso (projectiveBundleTwist E hfree).obj
      (projectiveBundleTwist E hfree).property (chartBundleHomOfSiteToPresenting E hfree m h)
      (ψ := projectiveBundleAtlas E hfree) rfl, fun M hM σ₀ => ?_⟩
  have hN := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (projectiveBundleProj E hfree) M hM
  obtain ⟨A₁, hA⟩ := exists_projectiveBundleAtlasReading_map_tautological_eq E hfree M hM σ₀
  have h1 := schemeReadingMap_comp_projectiveBundleAtlas_eq E hfree
    (chartBundleHomOfSiteToPresenting E hfree m h) hN (projectiveBundleTwist E hfree).property
    ((modulePullback B S hS (projectiveBundleProj E hfree)).map σ₀ ≫
      (projectiveBundleTautological E hfree).hom)
  obtain ⟨s₁, hBC⟩ := Stacks.RelativeProj.exists_pullback_comp_map_eq_of_baseChange
    (chartBundleHomOfSite E hfree h) (chartBundleMap E m)
    (Stacks.RelativeProj.projectiveBundleBaseChange_comp_projectiveBundleToBase
      (chartSchemeMapOfSite m) (chartBundleModule E (bundleBaseChart X)) (chartBundleModule E V)
      (chartBundleModuleIso E m))
    (chartBundleModuleIso E m) (@chartBundleModuleIso B S hS X M hM _ _ m)
    (chartBundleTautological E (bundleBaseChart X)) (chartBundleTautological E V)
    (chartBundleTwistIso E m) (chartBundleTwistIso_spec E m)
    (schemeReadingMap (chartToSpace B S hS X (bundleBaseChart X)) σ₀)
    (schemeReadingMap (chartToSpace B S hS X V) σ₀)
    (@chartModuleMap_comp_chartBundleModuleIso_hom B S hS X M E hM hE σ₀ _ _ m)
  have hO := Stacks.RelativeProj.pullback_map_comp_overQuotientMap_eq
    (Stacks.RelativeProj.tautologicalDatum (chartBundleModule E V))
    (schemeReadingMap (chartToSpace B S hS X V) σ₀) (chartBundleHomOfSite E hfree h)
    (g := chartBundleHomOfSite E hfree h ≫ chartBundleToChart E V) rfl
  have hA2 := schemeReadingMap_projectiveBundleAtlas_eq_of_eq E hfree
    ((modulePullback B S hS (projectiveBundleProj E hfree)).map σ₀ ≫
      (projectiveBundleTautological E hfree).hom) A₁ _ _ _ hA
  have hBC' : (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
      (associatedBigEtaleSite B) (chartBundleHomOfSiteToPresenting E hfree m h).left)).map
        ((Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
          (associatedBigEtaleSite B) (projectiveBundleChartProj E hfree).left)).map
          (schemeReadingMap (chartToSpace B S hS X (bundleBaseChart X)) σ₀) ≫
          chartBundleTautological E (bundleBaseChart X)) =
      s₁.hom ≫ (Scheme.Modules.pullback (chartBundleHomOfSite E hfree h)).map
          ((Scheme.Modules.pullback (chartBundleToChart E V)).map
            (schemeReadingMap (chartToSpace B S hS X V) σ₀) ≫ chartBundleTautological E V) ≫
        ((Scheme.Modules.pullback (chartBundleHomOfSite E hfree h)).mapIso
          (chartBundleTwistIso E m).symm ≪≫
          (Scheme.Modules.pullbackComp (chartBundleHomOfSite E hfree h) (chartBundleMap E m)).app
            (chartBundleTwist E (bundleBaseChart X))).hom := hBC
  refine ⟨_, Functor.eq_iso_comp_comp_iso_of_chain
    (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
      (associatedBigEtaleSite B) (chartBundleHomOfSiteToPresenting E hfree m h).left))
    _ _ _ _ _ hA2
    (schemeReadingMap (representedSpaceMap B S hS
      (chartBundleHomOfSiteToPresenting E hfree m h) ≫ projectiveBundleAtlas E hfree)
      ((modulePullback B S hS (projectiveBundleProj E hfree)).map σ₀ ≫
        (projectiveBundleTautological E hfree).hom))
    (schemeReadingPullbackIso ((modulePullback B S hS (projectiveBundleProj E hfree)).obj M) hN
      (chartBundleHomOfSiteToPresenting E hfree m h) (ψ := projectiveBundleAtlas E hfree) rfl)
    (schemeReadingPullbackIso (projectiveBundleTwist E hfree).obj
      (projectiveBundleTwist E hfree).property (chartBundleHomOfSiteToPresenting E hfree m h)
      (ψ := projectiveBundleAtlas E hfree) rfl)
    ?_ s₁
    ((Scheme.Modules.pullback (chartBundleHomOfSite E hfree h)).map
      ((Scheme.Modules.pullback (chartBundleToChart E V)).map
        (schemeReadingMap (chartToSpace B S hS X V) σ₀) ≫ chartBundleTautological E V))
    ((Scheme.Modules.pullback (chartBundleHomOfSite E hfree h)).mapIso
      (chartBundleTwistIso E m).symm ≪≫
      (Scheme.Modules.pullbackComp (chartBundleHomOfSite E hfree h) (chartBundleMap E m)).app
        (chartBundleTwist E (bundleBaseChart X)))
    ?_ ((Scheme.Modules.pullbackCongr (rfl : chartBundleHomOfSite E hfree h ≫
        chartBundleToChart E V = chartBundleHomOfSite E hfree h ≫ chartBundleToChart E V)).symm.app
          (chartBundleModule M V) ≪≫
      ((Scheme.Modules.pullbackComp (chartBundleHomOfSite E hfree h)
        (chartBundleToChart E V)).app (chartBundleModule M V)).symm)
    ((Scheme.Modules.pullback (chartBundleHomOfSite E hfree h ≫ chartBundleToChart E V)).map
        (schemeReadingMap (chartToSpace B S hS X V) σ₀) ≫
      (Stacks.RelativeProj.tautologicalDatum (chartBundleModule E V)).overQuotientMap
        (chartBundleHomOfSite E hfree h) rfl) ?_⟩
  · exact h1
  · exact hBC'
  · exact hO

end AlgebraicGeometry.Space

end
