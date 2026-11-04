module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRestrictionRightExact
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.BundleEmbeddingNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChartFamilyHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ReadingBundle
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleChartPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FamilyPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.HomTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RepresentedZariskiTransitionPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackComparison

/-!
# The projective bundle of a quotient inside the projective bundle

Let `X` be an algebraic space and `q : ℰ ⟶ ℱ` a surjection of finite locally free `𝒪_X`-modules
whose kernel is quasi-coherent. Over every étale chart `V` of `X` the reading `q_V : ℰ_V ⟶ ℱ_V` is
again a surjection, and the closed immersions `𝐏(ℱ_V) ⟶ 𝐏(ℰ_V)` of the chart projective bundles
are compatible with the base-change morphisms between charts. So they form a morphism of the
glueing data of the two projective bundles, and glue to a morphism `𝐏(ℱ) ⟶ 𝐏(ℰ)` over `X`.

## Main definitions

* `AlgebraicGeometry.Space.PrivateChern.moduleReadingMap`: the reading of a morphism of modules
  on a scheme over `X`.
* `AlgebraicGeometry.Space.PrivateChern.chartBundleEmbedding`: the closed immersion
  `𝐏(ℱ_V) ⟶ 𝐏(ℰ_V)` over a chart.
* `AlgebraicGeometry.Space.PrivateChern.projectiveBundleEmbedding`: the glued morphism
  `𝐏(ℱ) ⟶ 𝐏(ℰ)`.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.schemeReadingPullbackIso_naturality`: the comparisons of
  readings are natural in the module.
* `AlgebraicGeometry.Space.PrivateChern.epi_chartModuleMap`: the reading of a surjection with
  quasi-coherent kernel is a surjection (Stacks 03LV and 06VE).
* `AlgebraicGeometry.Space.PrivateChern.projectiveBundleEmbedding_comp_proj`: the glued morphism
  lies over `X`.

## References

* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Space.PrivateChern

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

section Reading

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

variable {E F : Modules.{u, u} B S hS X.1 X.2} (q : E ⟶ F)

/-- The reading `q_ψ : ℰ_ψ ⟶ ℱ_ψ` of a morphism of modules on a scheme over `X`. -/
abbrev moduleReadingMap {T : BigFppfOver B S hS} (ψ : representedAlgebraicSpace B S hS T ⟶ X) :
    schemeReading E ψ ⟶ schemeReading F ψ :=
  (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
    ((representedSmallEtaleModuleEquivalence B S hS T).inverse.map
      ((modulePullback B S hS ψ).map q))

/-- Reading a module on a represented space on its scheme, as a functor. -/
abbrev readingFunctor (T : BigFppfOver B S hS) :
    Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
        (representedAlgebraicSpace B S hS T).2 ⥤ ((BigFppfOver.toScheme B S hS).obj T).Modules :=
  (representedSmallEtaleModuleEquivalence B S hS T).inverse ⋙
    _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property

/-- On morphisms, `readingFunctor T` is the inverse of the small étale module equivalence
followed by restriction of modules to the scheme of `T`. -/
theorem readingFunctor_map {T : BigFppfOver B S hS}
    {M N : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2} (x : M ⟶ N) :
    (readingFunctor T).map x =
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS T).inverse.map x) :=
  rfl

/-- The reading `q_ψ` is the reading functor applied to the pullback `ψ^*q`. -/
theorem moduleReadingMap_eq {T : BigFppfOver B S hS} (ψ : representedAlgebraicSpace B S hS T ⟶ X) :
    moduleReadingMap q ψ = (readingFunctor T).map ((modulePullback B S hS ψ).map q) :=
  rfl

/-- The comparison `g^*ℰ_ψ ≅ ℰ_{ψ'}` is the Zariski pullback comparison followed by the reading
of the inverse of the pullback comparison `g^*ψ^*ℰ ≅ ψ'^*ℰ`. -/
theorem schemeReadingPullbackIso_hom_eq (hE : E.IsQuasicoherentOnSite) {T' T : BigFppfOver B S hS}
    (g : T' ⟶ T) {ψ : representedAlgebraicSpace B S hS T ⟶ X}
    {ψ' : representedAlgebraicSpace B S hS T' ⟶ X} (w : representedSpaceMap B S hS g ≫ ψ = ψ') :
    (schemeReadingPullbackIso E hE g w).hom =
      (representedZariskiModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g)
          ((modulePullback B S hS ψ).obj E) (isQuasicoherentOnSite_modulePullback_schemeReading E hE
              ψ)).hom ≫
        (readingFunctor T').map
          (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS g) ψ ψ' w
            E).inv := by
  rw [schemeReadingPullbackIso_eq, Iso.trans_hom, Functor.mapIso_hom, Functor.mapIso_hom,
    Iso.symm_hom, readingFunctor_map]

/-- **The comparisons `g^*ℰ_ψ ≅ ℰ_{ψ'}` are natural in the module.** -/
theorem schemeReadingPullbackIso_naturality (hE : E.IsQuasicoherentOnSite)
    (hF : F.IsQuasicoherentOnSite) {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    {ψ : representedAlgebraicSpace B S hS T ⟶ X} {ψ' : representedAlgebraicSpace B S hS T' ⟶ X}
    (w : representedSpaceMap B S hS g ≫ ψ = ψ') :
    (Scheme.Modules.pullback (siteSchemeHom g)).map (moduleReadingMap q ψ) ≫
        (schemeReadingPullbackIso F hF g w).hom =
      (schemeReadingPullbackIso E hE g w).hom ≫ moduleReadingMap q ψ' := by
  have h1 := representedZariskiModulePullbackIso_naturality B S hS g
    (relativelyRepresentable_yoneda_map B S hS
        g) (isQuasicoherentOnSite_modulePullback_schemeReading E hE ψ)
    (isQuasicoherentOnSite_modulePullback_schemeReading F hF ψ) ((modulePullback B S hS ψ).map q)
  rw [← readingFunctor_map, ← readingFunctor_map] at h1
  rw [schemeReadingPullbackIso_hom_eq, schemeReadingPullbackIso_hom_eq, moduleReadingMap_eq q ψ',
    moduleReadingMap_eq q ψ, ← Category.assoc, h1, Category.assoc, Category.assoc,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    QuasiCoherentDescent.pullbackComparison_inv_naturality B S hS
      (representedSpaceMap B S hS g) ψ ψ' w q]

/-- **The reading of a surjection with quasi-coherent kernel is a surjection**: the inverse image
along an étale morphism is exact (Stacks 03LV), and the restriction from the small étale site of
a scheme to its small Zariski site is right exact on sequences with quasi-coherent kernel
(Stacks 06VE). -/
theorem epi_moduleReadingMap {L : Modules.{u, u} B S hS X.1 X.2} (i : L ⟶ E) (hiq : i ≫ q = 0)
    (hC : (ShortComplex.mk i q hiq).ShortExact) (hL : L.IsQuasicoherentOnSite)
    {T : BigFppfOver B S hS} (ψ : representedAlgebraicSpace B S hS T ⟶ X)
    (hψ : IsEtale B S hS ψ.hom) : Epi (moduleReadingMap q ψ) := by
  let : Limits.HasZeroMorphisms (SheafOfModules.{u}
      (_root_.AlgebraicGeometry.SmallEtale.structureSheaf (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property)) :=
    Preadditive.preadditiveHasZeroMorphisms
  have hex : exactFunctor (Modules.{u, u} B S hS X.1 X.2)
      (Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
        (representedAlgebraicSpace B S hS T).2) (modulePullback B S hS ψ) :=
    modulePullback_exact B S hS ψ hψ
  obtain ⟨_, _⟩ := (exactFunctor_iff _).mp hex
  have h₁ : ((ShortComplex.mk i q hiq).map (modulePullback B S hS ψ)).ShortExact :=
    hC.map_of_exact (modulePullback B S hS ψ)
  let C' : ShortComplex (SheafOfModules.{u} (representedStructureRingSheaf B S hS T)) :=
    ShortComplex.mk ((modulePullback B S hS ψ).map i) ((modulePullback B S hS ψ).map q)
      (((modulePullback B S hS ψ).map_comp i q).symm.trans
        ((congrArg (modulePullback B S hS ψ).map hiq).trans (Functor.map_zero _ _ _)))
  have h₁' : C'.ShortExact := h₁
  have h₃ := isQuasicoherentOnSite_representedSmallEtaleInverse B S hS T _
      (isQuasicoherentOnSite_modulePullback_schemeReading L hL ψ)
  have hz : (representedSmallEtaleModuleEquivalence B S hS T).inverse.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have hl : PreservesFiniteLimits (representedSmallEtaleModuleEquivalence B S hS T).inverse :=
    inferInstance
  have hc : PreservesFiniteColimits (representedSmallEtaleModuleEquivalence B S hS T).inverse :=
    inferInstance
  refine _root_.AlgebraicGeometry.SmallEtale.epi_restrictModule_map.{u}
    (C := C'.map (representedSmallEtaleModuleEquivalence B S hS T).inverse) ?_ h₃
  exact @ShortComplex.ShortExact.map_of_exact _ _ _ _ _ _ _ h₁'
    (representedSmallEtaleModuleEquivalence B S hS T).inverse _ _ _

end Reading

section Charts

variable {E F : Modules.{u, u} B S hS X.1 X.2} [hE : E.IsQuasicoherentOnSite]
  [hF : F.IsQuasicoherentOnSite] (q : E ⟶ F)

/-- The reading `q_V : ℰ_V ⟶ ℱ_V` of a morphism of modules over an étale chart. -/
abbrev chartModuleMap (V : SmallEtale B S hS X.1) : chartBundleModule E V ⟶ chartBundleModule F V :=
  moduleReadingMap q (chartToSpace B S hS X V)

/-- **The readings over charts commute with the identifications along morphisms of charts.** -/
theorem chartModuleMap_comp_chartModuleIso_hom {V V' : SmallEtale B S hS X.1} (h : V' ⟶ V) :
    chartModuleMap q V' ≫ (chartBundleModuleIso F h).hom =
      (chartBundleModuleIso E h).hom ≫ (Scheme.Modules.pullback (chartSchemeMap h)).map
        (chartModuleMap q V) := by
  have key := schemeReadingPullbackIso_naturality q hE hF ((SmallEtale.toOver B S hS X.1).map h)
    (representedSpaceMap_toOver_map_comp_chartToSpace h)
  rw [chartBundleModuleIso, chartBundleModuleIso, Iso.symm_hom, Iso.symm_hom, Iso.eq_inv_comp,
    ← Category.assoc, ← key, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

omit hE hF in
/-- The reading over a chart of a surjection with quasi-coherent kernel is a surjection. -/
theorem epi_chartModuleMap {L : Modules.{u, u} B S hS X.1 X.2} (i : L ⟶ E) (hiq : i ≫ q = 0)
    (hC : (ShortComplex.mk i q hiq).ShortExact) (hL : L.IsQuasicoherentOnSite)
    (V : SmallEtale B S hS X.1) : Epi (chartModuleMap q V) :=
  epi_moduleReadingMap q i hiq hC hL _ (isEtale_chartToSpace B S hS X V)

end Charts

section Embedding

private theorem embedding_naturality_shape {C : Type*} [Category C]
    {SF' SF SE' SE RF' RF RE' RE : C} {PF' : SF' ≅ RF'} {PF : SF ≅ RF} {PE' : SE' ≅ RE'}
    {PE : SE ≅ RE} {eF' : SF' ⟶ SE'} {eF : SF ⟶ SE} {βE : SE' ⟶ SE} {βF : SF' ⟶ SF}
    {πE : RE' ⟶ RE} {πF : RF' ⟶ RF} (hE : πE ≫ PE.inv = PE'.inv ≫ βE)
    (hF : πF ≫ PF.inv = PF'.inv ≫ βF) (hemb : eF' ≫ βE = βF ≫ eF) :
    πF ≫ PF.inv ≫ eF ≫ PE.hom = (PF'.inv ≫ eF' ≫ PE'.hom) ≫ πE := by
  have hE' : PE'.hom ≫ πE = βE ≫ PE.hom := by
    calc PE'.hom ≫ πE = PE'.hom ≫ (πE ≫ PE.inv) ≫ PE.hom := by
          rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      _ = PE'.hom ≫ (PE'.inv ≫ βE) ≫ PE.hom := by rw [hE]
      _ = βE ≫ PE.hom := by rw [Category.assoc, Iso.hom_inv_id_assoc]
  rw [Category.assoc, Category.assoc, hE', ← Category.assoc eF', hemb, Category.assoc βF,
    ← Category.assoc PF'.inv, ← hF, Category.assoc]

variable {E F : Modules.{u, u} B S hS X.1 X.2} [hE : E.IsQuasicoherentOnSite]
  [hF : F.IsQuasicoherentOnSite] (hfreeE : SheafOfModules.IsFiniteLocallyFreeOnSite E)
  (hfreeF : SheafOfModules.IsFiniteLocallyFreeOnSite F) (q : E ⟶ F)
  (hq : ∀ V : SmallEtale B S hS X.1, Epi (chartModuleMap q V))

/-- **The closed immersion `𝐏(ℱ_V) ⟶ 𝐏(ℰ_V)` over a chart**, induced by the surjection
`q_V : ℰ_V ⟶ ℱ_V`. -/
def chartBundleEmbedding (V : SmallEtale B S hS X.1) : chartBundle F V ⟶ chartBundle E V :=
  haveI := isFiniteLocallyFree_chartBundleModule E hfreeE V
  haveI := isFiniteLocallyFree_chartBundleModule F hfreeF V
  haveI := hq V
  (Stacks.RelativeProj.bundlePresentationIso (chartBundleModule F V)).inv ≫
    Stacks.Chow.GenuineChern.bundleEmbedding (chartModuleMap q V) ≫
      (Stacks.RelativeProj.bundlePresentationIso (chartBundleModule E V)).hom

/-- The closed immersion lies over the chart. -/
theorem chartBundleEmbedding_comp_toChart (V : SmallEtale B S hS X.1) :
    chartBundleEmbedding hfreeE hfreeF q hq V ≫ chartBundleToChart E V =
      chartBundleToChart F V := by
  have := isFiniteLocallyFree_chartBundleModule E hfreeE V
  have := isFiniteLocallyFree_chartBundleModule F hfreeF V
  have := hq V
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans ?_
  refine (congrArg (fun k => _ ≫ Stacks.Chow.GenuineChern.bundleEmbedding (chartModuleMap q V) ≫ k)
    (Stacks.RelativeProj.bundlePresentationIso_hom_comp_toBase (chartBundleModule E V))).trans ?_
  refine (congrArg (_ ≫ ·)
    (Stacks.Chow.GenuineChern.bundleEmbedding_comp_bundleProj (chartModuleMap q V))).trans ?_
  exact Stacks.RelativeProj.bundlePresentationIso_inv_comp_toBase (chartBundleModule F V)

/-- The closed immersions over the charts commute with the base-change morphisms between
charts. -/
theorem chartBundleMap_comp_chartBundleEmbedding {V V' : SmallEtale B S hS X.1} (h : V' ⟶ V) :
    chartBundleMap F h ≫ chartBundleEmbedding hfreeE hfreeF q hq V =
      chartBundleEmbedding hfreeE hfreeF q hq V' ≫ chartBundleMap E h := by
  have := isFiniteLocallyFree_chartBundleModule E hfreeE
  have := isFiniteLocallyFree_chartBundleModule F hfreeF
  have := hq
  have hE := Stacks.RelativeProj.projectiveBundleBaseChange_comp_bundlePresentationIso_inv
    (chartSchemeMap h) (chartBundleModule E V) (chartBundleModule E V') (chartBundleModuleIso E h)
  have hF := Stacks.RelativeProj.projectiveBundleBaseChange_comp_bundlePresentationIso_inv
    (chartSchemeMap h) (chartBundleModule F V) (chartBundleModule F V') (chartBundleModuleIso F h)
  have hemb := bundleEmbedding_comp_baseChangeHom (chartSchemeMap h) (chartModuleMap q V)
    (chartModuleMap q V') (chartBundleModuleIso E h) (chartBundleModuleIso F h)
    (chartModuleMap_comp_chartModuleIso_hom q h)
  exact embedding_naturality_shape hE hF hemb

/-- **The closed immersions over the charts, as a morphism of glueing data.** -/
def projectiveBundleFamilyEmbedding :
    CartesianChartFamily.Hom (projectiveBundleChartFamily F hfreeF) (projectiveBundleChartFamily E
        hfreeE) where
  app := chartBundleEmbedding hfreeE hfreeF q hq
  app_toChart := chartBundleEmbedding_comp_toChart hfreeE hfreeF q hq
  naturality := chartBundleMap_comp_chartBundleEmbedding hfreeE hfreeF q hq

/-- **The morphism `𝐏(ℱ) ⟶ 𝐏(ℰ)` of projective bundles induced by a surjection `ℰ ⟶ ℱ`.** -/
def projectiveBundleEmbedding : projectiveBundle F hfreeF ⟶ projectiveBundle E hfreeE :=
  (projectiveBundleFamilyEmbedding hfreeE hfreeF q hq).glued (presentationRelationTargetHom
      (projectiveBundlePresentation X)) (presentationRelationSourceHom (projectiveBundlePresentation
      X))
    (isPullback_projectiveBundlePresentation X)

/-- **The morphism of projective bundles lies over `X`.** -/
theorem projectiveBundleEmbedding_comp_proj :
    projectiveBundleEmbedding hfreeE hfreeF q hq ≫ projectiveBundleProj E hfreeE =
      projectiveBundleProj F hfreeF :=
  (projectiveBundleFamilyEmbedding hfreeE hfreeF q
      hq).glued_comp_quotientHom (presentationRelationTargetHom (projectiveBundlePresentation X))
    (presentationRelationSourceHom (projectiveBundlePresentation
        X)) (isPullback_projectiveBundlePresentation X)

end Embedding

end AlgebraicGeometry.Space.PrivateChern

end
