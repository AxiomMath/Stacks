module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ProjectiveBundleSubbundle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.SubbundleSchemeLift

/-!
# The points of the presenting chart of `𝐏(ℰ)` on which `π^*ℒ ⟶ 𝒪(1)` vanishes

Let `0 ⟶ ℒ ⟶ ℰ ⟶ ℱ ⟶ 0` be short exact on an algebraic space `X`, with `ℒ` quasi-coherent and
`ℰ`, `ℱ` finite locally free, and `s : π^*ℒ ⟶ 𝒪_{𝐏(ℰ)}(1)` the composite of `π^*ℒ ⟶ π^*ℰ` with the
tautological quotient. **A point `x : T ⟶ 𝐏(ℰ_U)` of the presenting chart along which `s` pulls
back to zero comes from the chart `𝐏(ℱ_U)`** of `𝐏(ℱ)`: read on schemes, the pulled-back `s` is
`π_U^*ℒ_U ⟶ π_U^*ℰ_U ⟶ 𝒪(1)` pulled back along `x`
(`AlgebraicGeometry.Space.PrivateChern.exists_iso_readingMap_comp`), the readings
`ℒ_U ⟶ ℰ_U ⟶ ℱ_U ⟶ 0` are exact
(`AlgebraicGeometry.Space.PrivateChern.shortExact_moduleReadingMap`), and the scheme statement is
`AlgebraicGeometry.Space.PrivateChern.exists_comp_situationEmbedding_eq`.

## Main results

* `exists_comp_chartEmbedding_eq_of_modulePullback_map_eq_zero`: a point of the presenting chart
  of `𝐏(ℰ)` along which `s` vanishes comes from the presenting chart of `𝐏(ℱ)`.
* `AlgebraicGeometry.Space.PrivateChern.pullback_map_readingMap_comp_eq_zero`: the reading on the
  chart of the vanishing of `s`, at variable data.
* `AlgebraicGeometry.Space.PrivateChern.exists_comp_eq_of_siteSchemeHom`: factorizations in the
  site are detected on the underlying schemes.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 0ES8](https://stacks.math.columbia.edu/tag/0ES8)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Space.PrivateChern

attribute [-instance] CategoryTheory.catToReflQuiver

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {E F L : Modules.{u, u} B S hS X.1 X.2}
  [hE : E.IsQuasicoherentOnSite] [hF : F.IsQuasicoherentOnSite]
  (hfreeE : SheafOfModules.IsFiniteLocallyFreeOnSite E)
  (hfreeF : SheafOfModules.IsFiniteLocallyFreeOnSite F) (q : E ⟶ F)
  (hq : ∀ V : SmallEtale B S hS X.1, Epi (chartModuleMap q V)) (i : L ⟶ E)

/-- **At variable data: a morphism `π^*ℒ ⟶ π^*ℰ ⟶ 𝒜` whose inverse image along `x ≫ φ` vanishes
reads, on the chart, as a morphism whose inverse image along `x` vanishes**: the reading of
`φ^*(π^*i ≫ τ)` is `ρ^*i_Y ≫ univ` up to isomorphisms
(`AlgebraicGeometry.Space.PrivateChern.exists_iso_readingMap_comp`), and readings are compatible
with inverse images (`AlgebraicGeometry.Space.PrivateChern.pullback_map_readingMap_eq_zero`). -/
theorem pullback_map_readingMap_comp_eq_zero {X P : AlgebraicSpaces B S hS}
    {L E : Modules.{u, u} B S hS X.1 X.2} (hL : L.IsQuasicoherentOnSite)
    (hE : E.IsQuasicoherentOnSite) (i : L ⟶ E) {U Y : BigFppfOver B S hS} {ρ : U ⟶ Y}
    {ψY : representedAlgebraicSpace B S hS Y ⟶ X} (φ : representedAlgebraicSpace B S hS U ⟶ P)
    (π : P ⟶ X) (wρ : representedSpaceMap B S hS ρ ≫ ψY = φ ≫ π)
    {TU : ((BigFppfOver.toScheme B S hS).obj U).Modules}
    (univ : (Scheme.Modules.pullback (siteSchemeHom ρ)).obj (schemeReading E ψY) ⟶ TU)
    {Lm : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS U).1
      (representedAlgebraicSpace B S hS U).2}
    (εL : representedZariskiModule B S hS U Lm ≅ TU) {A : Modules.{u, u} B S hS P.1 P.2}
    (hA : A.IsQuasicoherentOnSite) (τ : (modulePullback B S hS π).obj E ⟶ A)
    (aI : (modulePullback B S hS φ).obj A ≅ Lm)
    (χ : (modulePullback B S hS φ).obj ((modulePullback B S hS π).obj E) ⟶ Lm)
    (hτ : (modulePullback B S hS φ).map τ ≫ aI.hom = χ)
    (hχ : (SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).map
      ((representedSmallEtaleModuleEquivalence B S hS U).inverse.map χ) =
      quotientReadingOf E hE wρ univ εL
        (QuasiCoherentDescent.pullbackComparison B S hS φ π _ rfl E).symm)
    {T : BigFppfOver B S hS} (x : T ⟶ U)
    (hx : (modulePullback B S hS (representedSpaceMap B S hS x ≫ φ)).map
      ((modulePullback B S hS π).map i ≫ τ) = 0) :
    (Scheme.Modules.pullback (siteSchemeHom x)).map
      ((Scheme.Modules.pullback (siteSchemeHom ρ)).map (moduleReadingMap i ψY) ≫ univ) = 0 := by
  -- the inverse image along `x` of `φ^*(π^*i ≫ τ)` vanishes
  have h1 : (modulePullback B S hS (representedSpaceMap B S hS x)).map
      ((modulePullback B S hS φ).map ((modulePullback B S hS π).map i ≫ τ)) = 0 := by
    have hnat := QuasiCoherentDescent.pullbackComparison_inv_naturality B S hS
      (representedSpaceMap B S hS x) φ _ rfl ((modulePullback B S hS π).map i ≫ τ)
    rw [hx, Limits.comp_zero] at hnat
    have h' := congrArg (fun k => k ≫ (QuasiCoherentDescent.pullbackComparison B S hS
      (representedSpaceMap B S hS x) φ _ rfl A).hom) hnat
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h'
    rw [h']
    exact Limits.zero_comp
  have hM := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS φ _
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS π L hL)
  have hN := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS φ A hA
  have h2 := pullback_map_readingMap_eq_zero x hM hN _ h1
  obtain ⟨θ, hθ⟩ := exists_iso_readingMap_comp hL hE i φ π wρ univ εL τ aI χ hτ hχ
  have h3 : (Scheme.Modules.pullback (siteSchemeHom x)).map
      (pulledBackQuotientReading hL i φ π wρ univ) = 0 := by
    rw [← hθ, Functor.map_comp]
    change (Scheme.Modules.pullback (siteSchemeHom x)).map
      ((SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).map ((readingInverse U).map
          ((modulePullback B S hS φ).map ((modulePullback B S hS π).map i ≫ τ)))) ≫ _ = 0
    rw [h2, Limits.zero_comp]
  unfold pulledBackQuotientReading at h3
  rw [Functor.map_comp, Functor.map_comp] at h3
  rwa [Preadditive.IsIso.comp_left_eq_zero, Preadditive.IsIso.comp_left_eq_zero] at h3

/-- **A morphism of schemes underlying a factorization in the site is one**: if the scheme
morphism of `x : T ⟶ U` factors through that of `j : U' ⟶ U`, then `x` factors through `j`. -/
theorem exists_comp_eq_of_siteSchemeHom {T U' U : BigFppfOver B S hS} (j : U' ⟶ U) (x : T ⟶ U)
    (t' : (BigFppfOver.toScheme B S hS).obj T ⟶ (BigFppfOver.toScheme B S hS).obj U')
    (ht' : t' ≫ siteSchemeHom j = siteSchemeHom x) : ∃ x' : T ⟶ U', x' ≫ j = x := by
  refine ⟨Over.homMk (ObjectProperty.homMk t') ?_, ?_⟩
  · apply ObjectProperty.hom_ext
    have h1 : j.left.hom ≫ U.hom.hom = U'.hom.hom := congrArg (fun k => k.hom) (Over.w j)
    have h2 : x.left.hom ≫ U.hom.hom = T.hom.hom := congrArg (fun k => k.hom) (Over.w x)
    change t' ≫ U'.hom.hom = T.hom.hom
    rw [← h1, ← Category.assoc]
    exact (congrArg (· ≫ U.hom.hom) ht').trans h2
  · exact Over.OverMorphism.ext (ObjectProperty.hom_ext _ ht')

section SchemeLift

variable {X : Scheme.{u}} {M G Q : X.Modules}
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} Q] (g : G ⟶ Q) [Epi g]
  [G.IsQuasicoherent] [Q.IsQuasicoherent] (m : M ⟶ G) (hmg : m ≫ g = 0)
  (hcok : IsColimit (CokernelCofork.ofπ g hmg))

include hcok in
/-- `AlgebraicGeometry.Space.PrivateChern.exists_comp_situationEmbedding_eq` for a projective
bundle, its projection, tautological quotient and embedding given up to equality. -/
theorem exists_comp_eq_of_heq_situationEmbedding {P P' T : Scheme.{u}} (π : P ⟶ X)
    {LP : P.Modules} (u : (Scheme.Modules.pullback π).obj G ⟶ LP) (f : P' ⟶ P) (t : T ⟶ P)
    (hP : P = Stacks.RelativeProj.projectiveBundle X G)
    (hP' : P' = Stacks.RelativeProj.projectiveBundle X Q)
    (hπ : HEq π (Stacks.RelativeProj.projectiveBundleToBase X G))
    (hLP : HEq LP (Stacks.RelativeProj.tautologicalDatumTwist G))
    (hu : HEq u (Stacks.RelativeProj.tautologicalDatumUniv G))
    (hf : HEq f (situationEmbedding g))
    (ht : (Scheme.Modules.pullback t).map ((Scheme.Modules.pullback π).map m ≫ u) = 0) :
    ∃ t' : T ⟶ P', t' ≫ f = t := by
  subst hP hP'
  obtain rfl := eq_of_heq hπ
  obtain rfl := eq_of_heq hLP
  obtain rfl := eq_of_heq hu
  obtain rfl := eq_of_heq hf
  exact exists_comp_situationEmbedding_eq g m hmg hcok t ht

end SchemeLift

/-- **The closed immersion `𝐏(ℱ_U) ⟶ 𝐏(ℰ_U)` of presenting charts**, as a morphism between the
presenting objects of the two presentations. -/
def chartEmbedding :
    (projectiveBundleChartPresentation F hfreeF).U ⟶
      (projectiveBundleChartPresentation E hfreeE).U :=
  (projectiveBundleFamilyEmbedding hfreeE hfreeF q hq).siteApp (bundleBaseChart X)

/-- The scheme morphism of `AlgebraicGeometry.Space.PrivateChern.chartEmbedding` is the closed
immersion of the chart bundles. -/
theorem siteSchemeHom_chartEmbedding :
    haveI := isFiniteLocallyFree_chartBundleModule E hfreeE (bundleBaseChart X)
    haveI := isFiniteLocallyFree_chartBundleModule F hfreeF (bundleBaseChart X)
    haveI := hq (bundleBaseChart X)
    siteSchemeHom (chartEmbedding hfreeE hfreeF q hq) =
      situationEmbedding (chartModuleMap q (bundleBaseChart X)) := by
  have := isFiniteLocallyFree_chartBundleModule E hfreeE (bundleBaseChart X)
  have := isFiniteLocallyFree_chartBundleModule F hfreeF (bundleBaseChart X)
  have := hq (bundleBaseChart X)
  exact (situationEmbedding_eq (chartModuleMap q (bundleBaseChart X))).symm

/-- The presenting chart of `𝐏(ℱ)` followed by `ι` is `chartEmbedding` followed by the presenting
chart of `𝐏(ℰ)`. -/
theorem toSpace_comp_projectiveBundleEmbedding :
    (projectiveBundleChartPresentation F hfreeF).toSpace ≫
        (projectiveBundleEmbedding hfreeE hfreeF q hq).hom =
      yoneda.map (chartEmbedding hfreeE hfreeF q hq) ≫
        (projectiveBundleChartPresentation E hfreeE).toSpace :=
  congrArg (fun m => m.hom)
    (projectiveBundleAtlas_comp_projectiveBundleEmbedding hfreeE hfreeF q hq)

include hE hF in
/-- **A point of the presenting chart of `𝐏(ℰ)` along which `s : π^*ℒ ⟶ 𝒪(1)` vanishes comes
from the presenting chart of `𝐏(ℱ)`.** -/
theorem exists_comp_chartEmbedding_eq_of_modulePullback_map_eq_zero (hiq : i ≫ q = 0)
    (hC : (ShortComplex.mk i q hiq).ShortExact) (hLq : L.IsQuasicoherentOnSite)
    {T : BigFppfOver B S hS} (x : T ⟶ (projectiveBundleChartPresentation E hfreeE).U)
    (hx : (modulePullback B S hS
      (representedSpaceMap B S hS x ≫ projectiveBundleAtlas E hfreeE)).map
        (subbundleMorphism hfreeE i) = 0) :
    ∃ x' : T ⟶ (projectiveBundleChartPresentation F hfreeF).U,
      x' ≫ chartEmbedding hfreeE hfreeF q hq = x := by
  have := isFiniteLocallyFree_chartBundleModule E hfreeE (bundleBaseChart X)
  have := isFiniteLocallyFree_chartBundleModule F hfreeF (bundleBaseChart X)
  have := hq (bundleBaseChart X)
  have h1 := pullback_map_readingMap_comp_eq_zero hLq hE i
    (ρ := projectiveBundleChartProj E hfreeE) (projectiveBundleAtlas E hfreeE)
    (projectiveBundleProj E hfreeE) (representedSpaceMap_projectiveBundleChartProj_comp E hfreeE)
    (chartBundleTautological E (bundleBaseChart X)) (projectiveBundleChartTwistReadingIso E hfreeE)
    (projectiveBundleTwist E hfreeE).property (projectiveBundleTautological E hfreeE).hom
    (projectiveBundleTwistAtlasIso E hfreeE) (projectiveBundleChartQuotient E hfreeE)
    (by convert modulePullback_map_projectiveBundleTautological E hfreeE using 2)
    (representedZariski_map_projectiveBundleChartQuotient E hfreeE) x hx
  have hmg := moduleReadingMap_comp_moduleReadingMap_eq_zero q i hiq
    (chartToSpace B S hS X (bundleBaseChart X))
  have hcok := (shortExact_moduleReadingMap q i hiq hC hLq
    (chartToSpace B S hS X (bundleBaseChart X))
    (isEtale_chartToSpace B S hS X (bundleBaseChart X))).gIsCokernel
  have e := siteSchemeHom_chartEmbedding hfreeE hfreeF q hq
  obtain ⟨t', ht'⟩ : ∃ t' : (BigFppfOver.toScheme B S hS).obj T ⟶
      (BigFppfOver.toScheme B S hS).obj (projectiveBundleChartPresentation F hfreeF).U,
      t' ≫ siteSchemeHom (chartEmbedding hfreeE hfreeF q hq) = siteSchemeHom x :=
    exists_comp_eq_of_heq_situationEmbedding
      (X := chartScheme (bundleBaseChart X)) (M := chartBundleModule L (bundleBaseChart X))
      (G := chartBundleModule E (bundleBaseChart X)) (Q := chartBundleModule F (bundleBaseChart X))
      (chartModuleMap q (bundleBaseChart X)) (chartModuleMap i (bundleBaseChart X)) hmg hcok
      (P := (BigFppfOver.toScheme B S hS).obj (projectiveBundleChartPresentation E hfreeE).U)
      (P' := (BigFppfOver.toScheme B S hS).obj (projectiveBundleChartPresentation F hfreeF).U)
      (siteSchemeHom (projectiveBundleChartProj E hfreeE))
      (LP := chartBundleTwist E (bundleBaseChart X))
      (chartBundleTautological E (bundleBaseChart X))
      (siteSchemeHom (chartEmbedding hfreeE hfreeF q hq))
      (siteSchemeHom x) rfl rfl HEq.rfl HEq.rfl HEq.rfl (heq_of_eq e) h1
  exact exists_comp_eq_of_siteSchemeHom (chartEmbedding hfreeE hfreeF q hq) x t' ht'

end AlgebraicGeometry.Space.PrivateChern

end
