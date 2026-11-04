module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleMapOfSplitEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleTwistPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionChartQuotientReading
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeReadingPullbackIsoId
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionAffinePart

/-!
# The twist `𝒪(1)` along the closed immersion of projective bundles of a split quotient

Let `X` be an algebraic space over `S`, `u : ℰ ⟶ ℰ'` a morphism of finite locally free
quasi-coherent `𝒪_X`-modules with a section `σ : ℰ' ⟶ ℰ`, `σ ≫ u = 𝟙`, and
`i : 𝐏(ℰ') ⟶ 𝐏(ℰ)` the closed immersion of `AlgebraicGeometry.Space.projectiveBundleMapOfSplitEpi`,
lying over `X` (`i ≫ π = π'`). This file proves that **`i` pulls the twist back to the twist**:
there is an isomorphism `i^*𝒪_{𝐏(ℰ)}(1) ≅ 𝒪_{𝐏(ℰ')}(1)` carrying the inverse image of the
tautological quotient `π^*ℰ ⟶ 𝒪_{𝐏(ℰ)}(1)`, read out of `π'^*ℰ ≅ i^*π^*ℰ`, to the composite
`π'^*ℰ ⟶ π'^*ℰ' ⟶ 𝒪_{𝐏(ℰ')}(1)` of `π'^*u` with the tautological quotient of `𝐏(ℰ')`.

## Strategy

Both are quotients of `π'^*ℰ`, so by
`AlgebraicGeometry.Space.quotientIsoOfModulePullbackIsFlatOfSurjectiveOfComp` it suffices to
compare them after the inverse image along the étale surjective atlas `a : 𝐏(ℰ'|_U) ⟶ 𝐏(ℰ')` of
the presenting chart `U` of `X`. The atlas followed by `i` is the closed immersion of chart
bundles `k : 𝐏(ℰ'|_U) ⟶ 𝐏(ℰ|_U)` followed by the atlas of `𝐏(ℰ)`. On the scheme `𝐏(ℰ'|_U)`:

* the inverse image along `k` of the tautological quotient of `𝐏(ℰ|_U)` reads, by the
  scheme-level compatibility `Stacks.RelativeProj.tautologicalDatumTwistMapOfEpiIso_spec`, as
  `u_U` followed by the tautological quotient of `𝐏(ℰ'|_U)`
  (`AlgebraicGeometry.Space.quotientReadingHyp_modulePullback` along `k` over the identity of
  `U`, with the comparison of readings along the identity read by
  `AlgebraicGeometry.Space.schemeReadingPullbackIso_id_hom`);
* the tautological quotient of `𝐏(ℰ'|_U)` precomposed with `u` reads the same way
  (`AlgebraicGeometry.Space.quotientReadingHyp_precomp`).

Two quotients with the same reading are isomorphic
(`AlgebraicGeometry.Space.exists_iso_comp_eq_of_quotientReadingHyp`), and the comparisons of
iterated inverse images around the square `a ≫ i = k ≫ φ` cancel
(`AlgebraicGeometry.Space.pullbackComparison_coherence_of_triangle`).

## Main definitions

* `AlgebraicGeometry.Space.projectiveBundleSplitEpiTwistIso`: **the isomorphism
  `i^*𝒪_{𝐏(ℰ)}(1) ≅ 𝒪_{𝐏(ℰ')}(1)`**.
* `AlgebraicGeometry.Space.projectiveCompletionInfinityTwistIso`: its case at the hyperplane at
  infinity `𝐏(ℰ) ⟶ 𝐏(ℰ ⊕ 𝒪_X)`.

## Main results

* `AlgebraicGeometry.Space.comp_projectiveBundleSplitEpiTwistIso_hom`: **it carries the inverse
  image of the tautological quotient of `𝐏(ℰ)` to `π'^*u` followed by the tautological quotient
  of `𝐏(ℰ')`.**
* `AlgebraicGeometry.Space.pullbackComparison_coherence_of_triangle` and
  `AlgebraicGeometry.Space.exists_iso_modulePullback_comp_of_triangle`: the chase of comparisons
  of iterated inverse images around `a ≫ i = k ≫ φ`, for variable data.
* `AlgebraicGeometry.Space.tautologicalDatumTwistMapOfEpiIso_spec_siteApp`: Stacks 01O3 along the
  closed immersion `k` of the presenting chart bundles, in the shape of the readings.
* `AlgebraicGeometry.Space.exists_quotientIsoComp_siteApp_projectiveBundleChartQuotient`: on the
  presenting chart bundle of `𝐏(ℰ')`, `k^*` of the tautological quotient of `𝐏(ℰ|_U)` and `u`
  followed by the tautological quotient of `𝐏(ℰ'|_U)` are isomorphic quotients.

## Implementation notes

The chase of comparisons is stated and proved for variable spaces and morphisms
(`AlgebraicGeometry.Space.exists_iso_modulePullback_comp_of_triangle`) and only then
instantiated at the projective bundles, with every argument of the readings passed explicitly
in the spelling of the lemma's binders (see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleTwistPullback`).

## References

* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

-- See `StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleTwistPullback`.
attribute [-instance] CategoryTheory.catToReflQuiver

/-! ### The comparisons around a square over the base, for variable data -/

section Comparison

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The coherence of the comparisons of iterated inverse images around a square over the
base.** For `θ ≫ π = π'` and a factorization `a ≫ θ = r₁ ≫ φ`, the identification of
`a^*π'^*ℰ` with `r₁^*φ^*π^*ℰ` through `a^*θ^*π^*ℰ` followed by the one back through
`(a ≫ π')^*ℰ` is the identity. -/
theorem pullbackComparison_coherence_of_triangle {X P Q Pu T : AlgebraicSpaces B S hS}
    (θ : Q ⟶ P) (π : P ⟶ X) (π' : Q ⟶ X) (hθ : θ ≫ π = π') (a : T ⟶ Q) (r₁ : T ⟶ Pu)
    (φ : Pu ⟶ P) (ha : a ≫ θ = r₁ ≫ φ) (ψ : T ⟶ X) (hψ : a ≫ π' = ψ)
    (wk : r₁ ≫ (φ ≫ π) = ψ) (E : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS a).map
        (QuasiCoherentDescent.pullbackComparison B S hS θ π π' hθ E).hom ≫
      (QuasiCoherentDescent.pullbackComparison B S hS a θ (r₁ ≫ φ) ha
        ((modulePullback B S hS π).obj E)).inv ≫
      (QuasiCoherentDescent.pullbackComparison B S hS r₁ φ (r₁ ≫ φ) rfl
        ((modulePullback B S hS π).obj E)).hom ≫
      (modulePullback B S hS r₁).map
        (QuasiCoherentDescent.pullbackComparison B S hS φ π (φ ≫ π) rfl E).inv ≫
      (QuasiCoherentDescent.pullbackComparison B S hS r₁ (φ ≫ π) ψ wk E).inv ≫
      (QuasiCoherentDescent.pullbackComparison B S hS a π' ψ hψ E).hom = 𝟙 _ := by
  have hst : (r₁ ≫ φ) ≫ π = ψ := by rw [Category.assoc, wk]
  have t₁ := QuasiCoherentDescent.pullbackComparison_trans_hom B S hS a θ π π' hθ (r₁ ≫ φ) ha
    ψ hψ hst E
  have t₂ := QuasiCoherentDescent.pullbackComparison_trans_hom B S hS r₁ φ π (φ ≫ π) rfl
    (r₁ ≫ φ) rfl ψ wk hst E
  have t₁' : (modulePullback B S hS a).map
        (QuasiCoherentDescent.pullbackComparison B S hS θ π π' hθ E).hom ≫
      (QuasiCoherentDescent.pullbackComparison B S hS a θ (r₁ ≫ φ) ha
        ((modulePullback B S hS π).obj E)).inv =
      (QuasiCoherentDescent.pullbackComparison B S hS a π' ψ hψ E).inv ≫
        (QuasiCoherentDescent.pullbackComparison B S hS (r₁ ≫ φ) π ψ hst E).hom := by
    rw [Iso.eq_inv_comp, ← Category.assoc, t₁, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have t₂' : (QuasiCoherentDescent.pullbackComparison B S hS (r₁ ≫ φ) π ψ hst E).hom ≫
      (QuasiCoherentDescent.pullbackComparison B S hS r₁ φ (r₁ ≫ φ) rfl
        ((modulePullback B S hS π).obj E)).hom ≫
      (modulePullback B S hS r₁).map
        (QuasiCoherentDescent.pullbackComparison B S hS φ π (φ ≫ π) rfl E).inv ≫
      (QuasiCoherentDescent.pullbackComparison B S hS r₁ (φ ≫ π) ψ wk E).inv = 𝟙 _ := by
    rw [← Category.assoc, ← t₂, Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id]
  rw [← Category.assoc, t₁']
  simp only [Category.assoc]
  rw [reassoc_of% t₂', Iso.inv_hom_id]

/-- **Two quotients over a square over the base, compared on a chart.** For `θ ≫ π = π'` and a
factorization `a ≫ θ = r₁ ≫ φ`, let `τ` be a quotient of `π^*ℰ` written as `q₁` after `φ^*`, and
`τ'` a quotient of `π'^*ℰ'` written as `q₂` after `a^*`. If `r₁^*q₁` is isomorphic, as a quotient
of `a^*π'^*ℰ`, to `a^*π'^*u` followed by `q₂`, then `a^*` of the inverse image `θ^*τ` (read out of
`π'^*ℰ ≅ θ^*π^*ℰ`) and `a^*` of `π'^*u ≫ τ'` are isomorphic quotients. -/
theorem exists_iso_modulePullback_comp_of_triangle {X P Q Pu T : AlgebraicSpaces B S hS}
    (θ : Q ⟶ P) (π : P ⟶ X) (π' : Q ⟶ X) (hθ : θ ≫ π = π') (a : T ⟶ Q) (r₁ : T ⟶ Pu)
    (φ : Pu ⟶ P) (ha : a ≫ θ = r₁ ≫ φ) (ψ : T ⟶ X) (hψ : a ≫ π' = ψ)
    (wk : r₁ ≫ (φ ≫ π) = ψ) {E E' : Modules.{u, u} B S hS X.1 X.2} (u : E ⟶ E')
    {O : Modules.{u, u} B S hS P.1 P.2} (τ : (modulePullback B S hS π).obj E ⟶ O)
    {O' : Modules.{u, u} B S hS Q.1 Q.2} (τ' : (modulePullback B S hS π').obj E' ⟶ O')
    {L₁ : Modules.{u, u} B S hS Pu.1 Pu.2} (e₁ : (modulePullback B S hS φ).obj O ≅ L₁)
    (q₁ : (modulePullback B S hS φ).obj ((modulePullback B S hS π).obj E) ⟶ L₁)
    (hq₁ : ModulePullbackFactor φ τ e₁ q₁)
    {L₂ : Modules.{u, u} B S hS T.1 T.2} (e₂ : (modulePullback B S hS a).obj O' ≅ L₂)
    (q₂ : (modulePullback B S hS a).obj ((modulePullback B S hS π').obj E') ⟶ L₂)
    (hq₂ : ModulePullbackFactor a τ' e₂ q₂)
    (γ : (modulePullback B S hS r₁).obj L₁ ≅ L₂)
    (hγ : QuotientIsoComp ((modulePullback B S hS r₁).map q₁) γ
      (((modulePullback B S hS r₁).mapIso
          (QuasiCoherentDescent.pullbackComparison B S hS φ π (φ ≫ π) rfl E).symm ≪≫
          (QuasiCoherentDescent.pullbackComparison B S hS r₁ (φ ≫ π) ψ wk E).symm) ≪≫
        (QuasiCoherentDescent.pullbackComparison B S hS a π' ψ hψ E).symm.symm)
      ((modulePullback B S hS a).map ((modulePullback B S hS π').map u) ≫ q₂)) :
    ∃ β : (modulePullback B S hS a).obj ((modulePullback B S hS θ).obj O) ≅
        (modulePullback B S hS a).obj O',
      (modulePullback B S hS a).map
          ((QuasiCoherentDescent.pullbackComparison B S hS θ π π' hθ E).hom ≫
            (modulePullback B S hS θ).map τ) ≫ β.hom =
        (modulePullback B S hS a).map ((modulePullback B S hS π').map u ≫ τ') := by
  refine ⟨(QuasiCoherentDescent.pullbackComparison B S hS a θ (r₁ ≫ φ) ha O).symm ≪≫
    QuasiCoherentDescent.pullbackComparison B S hS r₁ φ (r₁ ≫ φ) rfl O ≪≫
    (modulePullback B S hS r₁).mapIso e₁ ≪≫ γ ≪≫ e₂.symm, ?_⟩
  have coh := pullbackComparison_coherence_of_triangle θ π π' hθ a r₁ φ ha ψ hψ wk E
  have n₁ := QuasiCoherentDescent.pullbackComparison_inv_naturality B S hS a θ (r₁ ≫ φ) ha τ
  have n₂ := QuasiCoherentDescent.pullbackComparison_naturality B S hS r₁ φ (r₁ ≫ φ) rfl τ
  have hq₁' : (modulePullback B S hS r₁).map ((modulePullback B S hS φ).map τ) ≫
      (modulePullback B S hS r₁).map e₁.hom = (modulePullback B S hS r₁).map q₁ := by
    rw [← Functor.map_comp]; exact congrArg _ hq₁
  have hq₂' : q₂ ≫ e₂.inv = (modulePullback B S hS a).map τ' := by
    rw [← hq₂, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  unfold QuotientIsoComp at hγ
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom,
    Category.assoc] at hγ
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% n₁, reassoc_of% n₂, reassoc_of% hq₁', reassoc_of% hγ, hq₂']
  simp only [← Category.assoc] at coh ⊢
  rw [coh, Category.id_comp]

end Comparison

/-- A composite of six morphisms, as a regular definition: two such composites whose objects are
spelled differently are compared argument by argument, without unfolding the composition of the
category. -/
private def comp₆ {C₀ : Type*} [Category C₀] {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : C₀} (f₁ : a₀ ⟶ a₁)
    (f₂ : a₁ ⟶ a₂) (f₃ : a₂ ⟶ a₃) (f₄ : a₃ ⟶ a₄) (f₅ : a₄ ⟶ a₅) (f₆ : a₅ ⟶ a₆) : a₀ ⟶ a₆ :=
  f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅ ≫ f₆

/-- An equation `f₁ ≫ f₂ = g₁ ≫ ⋯ ≫ g₆` transported along equalities of its eight pieces: stated
with every piece a variable, so that instantiating it compares two equations piece by piece. -/
private theorem eq_comp₆_of_pieces {C₀ : Type*} [Category C₀] {a₀ a₁ a₂ b₁ b₂ b₃ b₄ b₅ : C₀}
    {f₁ f₁' : a₀ ⟶ a₁} {f₂ f₂' : a₁ ⟶ a₂} {g₁ g₁' : a₀ ⟶ b₁} {g₂ g₂' : b₁ ⟶ b₂}
    {g₃ g₃' : b₂ ⟶ b₃} {g₄ g₄' : b₃ ⟶ b₄} {g₅ g₅' : b₄ ⟶ b₅} {g₆ g₆' : b₅ ⟶ a₂}
    (h : f₁' ≫ f₂' = comp₆ g₁' g₂' g₃' g₄' g₅' g₆') (e₁ : f₁ = f₁') (e₂ : f₂ = f₂')
    (k₁ : g₁ = g₁') (k₂ : g₂ = g₂') (k₃ : g₃ = g₃') (k₄ : g₄ = g₄') (k₅ : g₅ = g₅')
    (k₆ : g₆ = g₆') : f₁ ≫ f₂ = comp₆ g₁ g₂ g₃ g₄ g₅ g₆ := by
  subst e₁ e₂ k₁ k₂ k₃ k₄ k₅ k₆
  exact h

/-- The transport `AlgebraicGeometry.Scheme.Modules.pullbackCongr` at a module, as an `eqToHom`.
Comparing two such transports whose morphisms are spelled differently is cheap for `eqToHom`. -/
private theorem schemeModulesPullbackCongr_hom_app_eq_eqToHom {A B : Scheme.{u}} {p₁ p₂ : A ⟶ B}
    (h : p₁ = p₂) (M : B.Modules) :
    (Scheme.Modules.pullbackCongr h).hom.app M =
      eqToHom (congrArg (fun p => (Scheme.Modules.pullback p).obj M) h) := by
  subst h
  rfl

/-! ### The two quotients on the presenting chart bundle of `𝐏(ℰ')` -/

section Chart

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (E E' : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]
  [hE' : E'.IsQuasicoherentOnSite] (u : E ⟶ E') (σ : E' ⟶ E) (hσ : σ ≫ u = 𝟙 E')
  (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)
  (hfree' : SheafOfModules.IsFiniteLocallyFreeOnSite E')

omit hE hE' in
/-- The square `𝐏(ℰ|_U) ⟶ U ⟶ X` equals `𝐏(ℰ|_U) ⟶ 𝐏(ℰ) ⟶ X`, with the chart bundle spelled as
the object of the chart family. -/
theorem representedSpaceMap_siteToChart_bundleBaseChart_comp
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (hF : SheafOfModules.IsFiniteLocallyFreeOnSite F) :
    representedSpaceMap B S hS ((projectiveBundleChartFamily F hF).siteToChart
      (bundleBaseChart X)) ≫
        chartToSpace B S hS X (bundleBaseChart X) =
      projectiveBundleAtlas F hF ≫ projectiveBundleProj F hF :=
  representedSpaceMap_projectiveBundleChartProj_comp F hF

omit hE hE' in
attribute [local implicit_reducible] AlgebraicGeometry.Space.CartesianChartFamily.site
  AlgebraicGeometry.BigFppfOver.siteObjectOver
  AlgebraicGeometry.Space.CartesianChartFamily.siteToChart
  AlgebraicGeometry.BigFppfOver.siteMapOver in
/-- `AlgebraicGeometry.Space.quotientReadingHyp_projectiveBundle`, with the presenting chart bundle
spelled as the object of the chart family. -/
theorem quotientReadingHyp_projectiveBundle_site (F : Modules.{u, u} B S hS X.1 X.2)
    [hF' : F.IsQuasicoherentOnSite] (hF : SheafOfModules.IsFiniteLocallyFreeOnSite F) :
    QuotientReadingHyp F hF' (ρ := (projectiveBundleChartFamily F hF).siteToChart
      (bundleBaseChart X))
      (representedSpaceMap_siteToChart_bundleBaseChart_comp F hF)
      (chartBundleTautological F (bundleBaseChart X)) (projectiveBundleChartTwistReadingIso F hF)
      (projectiveBundleChartQuotient F hF)
      (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas F hF)
        (projectiveBundleProj F hF) _ rfl F).symm :=
  quotientReadingHyp_projectiveBundle F hF

/-- **The atlas of `𝐏(ℰ')` followed by `i` is the closed immersion of the presenting chart
bundles followed by the atlas of `𝐏(ℰ)`.** -/
theorem projectiveBundleAtlas_comp_projectiveBundleMapOfSplitEpi :
    projectiveBundleAtlas E' hfree' ≫ projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree' =
      representedSpaceMap B S hS
          ((projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').siteApp
          (bundleBaseChart X)) ≫ projectiveBundleAtlas E hfree :=
  ObjectProperty.hom_ext _
    (projectiveBundleChart_comp_projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree')

/-- The closed immersion of the presenting chart bundles followed by `𝐏(ℰ|_U) ⟶ 𝐏(ℰ) ⟶ X` is
`𝐏(ℰ'|_U) ⟶ 𝐏(ℰ') ⟶ X`. -/
theorem representedSpaceMap_siteApp_comp_projectiveBundleAtlas_comp_proj :
    representedSpaceMap B S hS
        ((projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').siteApp
          (bundleBaseChart X)) ≫ (projectiveBundleAtlas E hfree ≫ projectiveBundleProj E hfree) =
      projectiveBundleAtlas E' hfree' ≫ projectiveBundleProj E' hfree' := by
  rw [← Category.assoc, ← projectiveBundleAtlas_comp_projectiveBundleMapOfSplitEpi,
    Category.assoc, projectiveBundleMapOfSplitEpi_comp_projectiveBundleProj]

/-- The closed immersion of the presenting chart bundles lies over the identity of the chart. -/
theorem siteApp_comp_projectiveBundleChartProj :
    ((projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').siteApp
          (bundleBaseChart X)) ≫
        (projectiveBundleChartFamily E hfree).siteToChart (bundleBaseChart X) =
      (projectiveBundleChartFamily E' hfree').siteToChart (bundleBaseChart X) ≫
        𝟙 ((SmallEtale.toOver B S hS X.1).obj (bundleBaseChart X)) :=
  ((projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').siteApp_siteToChart
    (bundleBaseChart X)).trans (Category.comp_id _).symm

omit hE hE' in
/-- The identity of the chart lies over `X`. -/
theorem representedSpaceMap_id_comp_chartToSpace (V : SmallEtale B S hS X.1) :
    representedSpaceMap B S hS (𝟙 ((SmallEtale.toOver B S hS X.1).obj V)) ≫
        chartToSpace B S hS X V = chartToSpace B S hS X V :=
  ObjectProperty.hom_ext _ (by
    change yoneda.map (𝟙 _) ≫ (chartToSpace B S hS X V).hom = _
    rw [yoneda.map_id]
    exact Category.id_comp _)

attribute [local implicit_reducible] AlgebraicGeometry.Space.CartesianChartFamily.site
  AlgebraicGeometry.BigFppfOver.siteObjectOver
  AlgebraicGeometry.Space.CartesianChartFamily.siteToChart
  AlgebraicGeometry.BigFppfOver.siteMapOver in
/-- **Stacks 01O3 along the closed immersion of the presenting chart bundles**, with the closed
immersion spelled as the morphism of the chart families. In the shape of
the hypothesis of `AlgebraicGeometry.Space.quotientReadingHyp_modulePullback` along it over the
identity of the chart: the pulled-back tautological quotient of `𝐏(ℰ|_U)`, followed by the
comparison of twists, is `u_U` followed by the tautological quotient of `𝐏(ℰ'|_U)`. The
tautological quotients and the comparison of twists are named, so that the statement is spelled
as the hypothesis it is fed to. It is
`Stacks.RelativeProj.tautologicalDatumTwistMapOfEpiIso_spec`, read through the comparison of the
readings along the identity
(`AlgebraicGeometry.Space.schemeReadingPullbackIso_id_hom`); the two equations are compared piece
by piece (`AlgebraicGeometry.Space.eq_comp₆_of_pieces`), with the transports along equalities of
morphisms written as `eqToHom`, since comparing two differently spelled transports
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` exhausts the kernel. -/
theorem tautologicalDatumTwistMapOfEpiIso_spec_siteApp
    (univ : (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
        (associatedBigEtaleSite B) ((projectiveBundleChartFamily E hfree).siteToChart
          (bundleBaseChart X)).left)).obj
        (schemeReading E (chartToSpace B S hS X (bundleBaseChart X))) ⟶ chartBundleTwist E
          (bundleBaseChart X))
    (hu : univ = chartBundleTautological E (bundleBaseChart X))
    (univ' : (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
        (associatedBigEtaleSite B) ((projectiveBundleChartFamily E' hfree').siteToChart
          (bundleBaseChart X)).left)).obj
        (schemeReading E (chartToSpace B S hS X (bundleBaseChart X))) ⟶ chartBundleTwist E'
          (bundleBaseChart X))
    (hu' : univ' = (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
        (associatedBigEtaleSite B) ((projectiveBundleChartFamily E' hfree').siteToChart
          (bundleBaseChart X)).left)).map
        (schemeReadingMap (chartToSpace B S hS X (bundleBaseChart X)) u) ≫
          chartBundleTautological E' (bundleBaseChart X))
    (θ : (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
      (associatedBigEtaleSite B)
        ((projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').siteApp
          (bundleBaseChart X)).left)).obj (chartBundleTwist E (bundleBaseChart X)) ≅
            chartBundleTwist E' (bundleBaseChart X))
    (hθ : θ = @Stacks.RelativeProj.tautologicalDatumTwistMapOfEpiIso _ _ _ _ _
      (chartModuleMap u (bundleBaseChart X)) (epi_chartModuleMap u σ hσ (bundleBaseChart X))) :
    (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
      (associatedBigEtaleSite B)
        ((projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').siteApp
          (bundleBaseChart X)).left)).map univ ≫ θ.hom =
      (Scheme.Modules.pullbackComp (_root_.AlgebraicGeometry.SmallEtale.schemeHom
        (associatedBigEtaleSite B)
        ((projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').siteApp
          (bundleBaseChart X)).left)
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            ((projectiveBundleChartFamily E hfree).siteToChart
              (bundleBaseChart X)).left)).hom.app
          (schemeReading E (chartToSpace B S hS X (bundleBaseChart X))) ≫
        (Scheme.Modules.pullbackCongr (schemeHom_comp_eq_of_eq
          (siteApp_comp_projectiveBundleChartProj E E' u σ hσ hfree hfree'))).hom.app
          (schemeReading E (chartToSpace B S hS X (bundleBaseChart X))) ≫
        (Scheme.Modules.pullbackComp
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            ((projectiveBundleChartFamily E' hfree').siteToChart (bundleBaseChart X)).left)
              (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        (𝟙 ((SmallEtale.toOver B S hS X.1).obj (bundleBaseChart X)) :
          (SmallEtale.toOver B S hS X.1).obj (bundleBaseChart X) ⟶
            (SmallEtale.toOver B S hS X.1).obj (bundleBaseChart X)).left)).inv.app (schemeReading E
              (chartToSpace B S hS X (bundleBaseChart X))) ≫
        (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
          (associatedBigEtaleSite B) ((projectiveBundleChartFamily E' hfree').siteToChart
            (bundleBaseChart X)).left)).map
          (schemeReadingPullbackIso E hE
            (𝟙 ((SmallEtale.toOver B S hS X.1).obj (bundleBaseChart X)))
            (representedSpaceMap_id_comp_chartToSpace (bundleBaseChart X))).hom ≫
        univ' := by
  subst hu hu' hθ
  have spec := @Stacks.RelativeProj.tautologicalDatumTwistMapOfEpiIso_spec _ _ _ _ _
    (chartModuleMap u (bundleBaseChart X)) (epi_chartModuleMap u σ hσ (bundleBaseChart X))
  rw [Functor.map_comp, Category.assoc, schemeModulesPullbackCongr_hom_app_eq_eqToHom] at spec
  rw [schemeReadingPullbackIso_id_hom E hE
    (representedSpaceMap_id_comp_chartToSpace (bundleBaseChart X)),
    schemeModulesPullbackCongr_hom_app_eq_eqToHom]
  change _ = comp₆ _ _ _ _ _ _
  have spec' : _ = comp₆ _ _ _ _ _ _ := spec
  exact eq_comp₆_of_pieces spec' rfl rfl rfl rfl rfl rfl rfl rfl


attribute [local implicit_reducible] AlgebraicGeometry.Space.CartesianChartFamily.site
  AlgebraicGeometry.BigFppfOver.siteObjectOver
  AlgebraicGeometry.Space.CartesianChartFamily.siteToChart
  AlgebraicGeometry.BigFppfOver.siteMapOver in
/-- **The tautological quotient of `𝐏(ℰ|_U)`, pulled back to `𝐏(ℰ'|_U)` along the closed immersion
`k` of the presenting chart bundles, reads as `u_U` followed by the tautological quotient of
`𝐏(ℰ'|_U)`** (Stacks 01O3 for `k`,
`Stacks.RelativeProj.tautologicalDatumTwistMapOfEpiIso_spec`). -/
theorem exists_quotientReadingHyp_siteApp_projectiveBundleChartQuotient :
    ∃ ε : representedZariskiModule B S hS (projectiveBundleChartPresentation E' hfree').U
        ((modulePullback B S hS (representedSpaceMap B S hS
          ((projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').siteApp
          (bundleBaseChart X)))).obj (projectiveBundleChartTwist E hfree)) ≅
        chartBundleTwist E' (bundleBaseChart X),
      QuotientReadingHyp E hE (representedSpaceMap_siteToChart_bundleBaseChart_comp E' hfree')
        ((Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
          (associatedBigEtaleSite B) ((projectiveBundleChartFamily E' hfree').siteToChart
            (bundleBaseChart X)).left)).map
          (schemeReadingMap (chartToSpace B S hS X (bundleBaseChart X)) u) ≫
        chartBundleTautological E' (bundleBaseChart X)) ε
        ((modulePullback B S hS (representedSpaceMap B S hS
          ((projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').siteApp
          (bundleBaseChart X)))).map (projectiveBundleChartQuotient E hfree))
        ((modulePullback B S hS (representedSpaceMap B S hS
          ((projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').siteApp
          (bundleBaseChart X)))).mapIso
          (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E hfree)
            (projectiveBundleProj E hfree) _ rfl E).symm ≪≫
          (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS
            ((projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').siteApp
          (bundleBaseChart X)))
            (projectiveBundleAtlas E hfree ≫ projectiveBundleProj E hfree)
            (projectiveBundleAtlas E' hfree' ≫ projectiveBundleProj E' hfree')
            (representedSpaceMap_siteApp_comp_projectiveBundleAtlas_comp_proj E E' u σ hσ hfree
              hfree') E).symm) :=
by
  have h := quotientReadingHyp_modulePullback E hE
    ((projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').siteApp
      (bundleBaseChart X))
    (ρ := (projectiveBundleChartFamily E hfree).siteToChart (bundleBaseChart X))
    (ρ' := (projectiveBundleChartFamily E' hfree').siteToChart (bundleBaseChart X))
    (t := 𝟙 ((SmallEtale.toOver B S hS X.1).obj (bundleBaseChart X)))
    (siteApp_comp_projectiveBundleChartProj E E' u σ hσ hfree hfree')
    (ψY := chartToSpace B S hS X (bundleBaseChart X))
    (ψY' := chartToSpace B S hS X (bundleBaseChart X))
    (ψU := projectiveBundleAtlas E hfree ≫ projectiveBundleProj E hfree)
    (ψR := projectiveBundleAtlas E' hfree' ≫ projectiveBundleProj E' hfree')
    (representedSpaceMap_siteToChart_bundleBaseChart_comp E hfree)
    (representedSpaceMap_siteApp_comp_projectiveBundleAtlas_comp_proj E E' u σ hσ hfree hfree')
    (representedSpaceMap_id_comp_chartToSpace (bundleBaseChart X))
    (representedSpaceMap_siteToChart_bundleBaseChart_comp E' hfree')
    (chartBundleTautological E (bundleBaseChart X)) ((Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom
          (associatedBigEtaleSite B) ((projectiveBundleChartFamily E' hfree').siteToChart
            (bundleBaseChart X)).left)).map
          (schemeReadingMap (chartToSpace B S hS X (bundleBaseChart X)) u) ≫
        chartBundleTautological E' (bundleBaseChart X))
    (@Stacks.RelativeProj.tautologicalDatumTwistMapOfEpiIso _ _ _ _ _
      (chartModuleMap u (bundleBaseChart X)) (epi_chartModuleMap u σ hσ (bundleBaseChart X)))
    (tautologicalDatumTwistMapOfEpiIso_spec_siteApp E E' u σ hσ hfree hfree' _ rfl _ rfl _ rfl)
    (isQuasicoherentOnSite_projectiveBundleChartModule E hfree)
    (isQuasicoherentOnSite_projectiveBundleChartTwist E hfree)
    (projectiveBundleChartTwistReadingIso E hfree) (projectiveBundleChartQuotient E hfree)
    (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E hfree)
      (projectiveBundleProj E hfree) _ rfl E).symm
    (quotientReadingHyp_projectiveBundle_site E hfree)
  exact ⟨_, h⟩

attribute [local implicit_reducible] AlgebraicGeometry.Space.CartesianChartFamily.site
  AlgebraicGeometry.BigFppfOver.siteObjectOver
  AlgebraicGeometry.Space.CartesianChartFamily.siteToChart
  AlgebraicGeometry.BigFppfOver.siteMapOver in
/-- **The tautological quotient of `𝐏(ℰ'|_U)` precomposed with `u` reads as `u_U` followed by the
tautological quotient of `𝐏(ℰ'|_U)`** (`AlgebraicGeometry.Space.quotientReadingHyp_precomp`). -/
theorem exists_quotientReadingHyp_precomp_projectiveBundleChartQuotient :
    ∃ ε : representedZariskiModule B S hS (projectiveBundleChartPresentation E' hfree').U
        (projectiveBundleChartTwist E' hfree') ≅ chartBundleTwist E' (bundleBaseChart X),
      QuotientReadingHyp E hE (representedSpaceMap_siteToChart_bundleBaseChart_comp E' hfree')
        ((Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
          (associatedBigEtaleSite B) ((projectiveBundleChartFamily E' hfree').siteToChart
            (bundleBaseChart X)).left)).map
          (schemeReadingMap (chartToSpace B S hS X (bundleBaseChart X)) u) ≫
        chartBundleTautological E' (bundleBaseChart X)) ε
        ((modulePullback B S hS (projectiveBundleAtlas E' hfree')).map
            ((modulePullback B S hS (projectiveBundleProj E' hfree')).map u) ≫
          projectiveBundleChartQuotient E' hfree')
        (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E' hfree')
          (projectiveBundleProj E' hfree') _ rfl E).symm :=
by
  have h := quotientReadingHyp_precomp E' hE'
    (ρ := (projectiveBundleChartFamily E' hfree').siteToChart (bundleBaseChart X))
    (representedSpaceMap_siteToChart_bundleBaseChart_comp E' hfree')
    (chartBundleTautological E' (bundleBaseChart X))
    (projectiveBundleChartTwistReadingIso E' hfree')
    (projectiveBundleChartQuotient E' hfree')
    (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E' hfree')
      (projectiveBundleProj E' hfree') _ rfl E').symm
    (quotientReadingHyp_projectiveBundle_site E' hfree') E hE u
    ((modulePullback B S hS (projectiveBundleAtlas E' hfree')).map
            ((modulePullback B S hS (projectiveBundleProj E' hfree')).map u) ≫
          projectiveBundleChartQuotient E' hfree')
    (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E' hfree')
      (projectiveBundleProj E' hfree') _ rfl E).symm (Iso.refl _) ?_
  · exact ⟨_, h⟩
  · have nat := QuasiCoherentDescent.pullbackComparison_naturality B S hS
      (projectiveBundleAtlas E' hfree') (projectiveBundleProj E' hfree')
      (projectiveBundleAtlas E' hfree' ≫ projectiveBundleProj E' hfree') rfl u
    rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.symm_inv,
      ← Category.assoc ((modulePullback B S hS
        (projectiveBundleAtlas E' hfree' ≫ projectiveBundleProj E' hfree')).map u), nat,
      Category.assoc, Iso.inv_hom_id_assoc]

/-- **The two read quotients on the presenting chart bundle of `𝐏(ℰ')` are isomorphic**:
`k^*` of the tautological quotient of `𝐏(ℰ|_U)` and `a^*π'^*u` followed by the tautological
quotient of `𝐏(ℰ'|_U)` have the same reading, so they are isomorphic quotients
(`AlgebraicGeometry.Space.exists_iso_comp_eq_of_quotientReadingHyp`). Stated in the shape of the
hypothesis of `AlgebraicGeometry.Space.exists_iso_modulePullback_comp_of_triangle`. -/
theorem exists_quotientIsoComp_siteApp_projectiveBundleChartQuotient :
    ∃ γ : (modulePullback B S hS (representedSpaceMap B S hS
      ((projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').siteApp
          (bundleBaseChart X)))).obj (projectiveBundleChartTwist E hfree) ≅
        projectiveBundleChartTwist E' hfree',
      QuotientIsoComp ((modulePullback B S hS (representedSpaceMap B S hS
        ((projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').siteApp
          (bundleBaseChart X)))).map (projectiveBundleChartQuotient E hfree)) γ
        (((modulePullback B S hS (representedSpaceMap B S hS
          ((projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').siteApp
          (bundleBaseChart X)))).mapIso
            (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E hfree)
              (projectiveBundleProj E hfree) (projectiveBundleAtlas E hfree ≫
                projectiveBundleProj E hfree) rfl E).symm ≪≫
            (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS
              ((projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').siteApp
          (bundleBaseChart X)))
              (projectiveBundleAtlas E hfree ≫ projectiveBundleProj E hfree)
              (projectiveBundleAtlas E' hfree' ≫ projectiveBundleProj E' hfree')
              (representedSpaceMap_siteApp_comp_projectiveBundleAtlas_comp_proj E E' u σ hσ hfree
                hfree') E).symm) ≪≫
          (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E' hfree')
            (projectiveBundleProj E' hfree') (projectiveBundleAtlas E' hfree' ≫
              projectiveBundleProj E' hfree') rfl E).symm.symm)
        ((modulePullback B S hS (projectiveBundleAtlas E' hfree')).map
            ((modulePullback B S hS (projectiveBundleProj E' hfree')).map u) ≫
          projectiveBundleChartQuotient E' hfree') := by
  obtain ⟨ε₁, h₁⟩ := exists_quotientReadingHyp_siteApp_projectiveBundleChartQuotient E E' u σ hσ
    hfree hfree'
  obtain ⟨ε₂, h₂⟩ := exists_quotientReadingHyp_precomp_projectiveBundleChartQuotient E E' u
    hfree'
  exact exists_iso_comp_eq_of_quotientReadingHyp E hE
    (representedSpaceMap_siteToChart_bundleBaseChart_comp E' hfree') _ h₁ h₂
    (isQuasicoherentOnSite_modulePullback_representedSpaceMap B S hS
      ((projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').siteApp
          (bundleBaseChart X))
      (relativelyRepresentable_yoneda_map B S hS _) _
      (isQuasicoherentOnSite_projectiveBundleChartModule E hfree))
    (isQuasicoherentOnSite_modulePullback_representedSpaceMap B S hS
      ((projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').siteApp
          (bundleBaseChart X))
      (relativelyRepresentable_yoneda_map B S hS _) _
      (isQuasicoherentOnSite_projectiveBundleChartTwist E hfree))
    (isQuasicoherentOnSite_projectiveBundleChartTwist E' hfree')

/-- The closed immersion of the presenting chart bundles, as a morphism between the atlases of
the two projective bundles. -/
abbrev splitEpiAtlasHom :
    (projectiveBundleGroupoid E' hfree').objects ⟶ (projectiveBundleGroupoid E hfree).objects :=
  (representedSpaceMap B S hS
      ((projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').siteApp
          (bundleBaseChart X)))

/-- `AlgebraicGeometry.Space.projectiveBundleAtlas_comp_projectiveBundleMapOfSplitEpi`, through
`AlgebraicGeometry.Space.splitEpiAtlasHom`. -/
theorem projectiveBundleAtlas_comp_mapOfSplitEpi_eq_splitEpiAtlasHom_comp :
    projectiveBundleAtlas E' hfree' ≫ projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree' =
      (splitEpiAtlasHom E E' u σ hσ hfree hfree') ≫ projectiveBundleAtlas E hfree :=
  projectiveBundleAtlas_comp_projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree'

/-- `AlgebraicGeometry.Space.representedSpaceMap_siteApp_comp_projectiveBundleAtlas_comp_proj`,
through `AlgebraicGeometry.Space.splitEpiAtlasHom`. -/
theorem splitEpiAtlasHom_comp_projectiveBundleAtlas_comp_proj :
    (splitEpiAtlasHom E E' u σ hσ hfree hfree') ≫ (projectiveBundleAtlas E hfree ≫
      projectiveBundleProj E hfree) =
      projectiveBundleAtlas E' hfree' ≫ projectiveBundleProj E' hfree' :=
  representedSpaceMap_siteApp_comp_projectiveBundleAtlas_comp_proj E E' u σ hσ hfree hfree'

/-- `AlgebraicGeometry.Space.exists_quotientIsoComp_siteApp_projectiveBundleChartQuotient`, through
`AlgebraicGeometry.Space.splitEpiAtlasHom`. -/
theorem exists_quotientIsoComp_splitEpiAtlasHom_projectiveBundleChartQuotient :
    ∃ γ : (modulePullback B S hS
      (splitEpiAtlasHom E E' u σ hσ hfree hfree')).obj (projectiveBundleChartTwist E hfree) ≅
        projectiveBundleChartTwist E' hfree',
      QuotientIsoComp ((modulePullback B S hS (splitEpiAtlasHom E E' u σ hσ hfree hfree')).map
        (projectiveBundleChartQuotient E hfree)) γ
        (((modulePullback B S hS (splitEpiAtlasHom E E' u σ hσ hfree hfree')).mapIso
            (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E hfree)
              (projectiveBundleProj E hfree) (projectiveBundleAtlas E hfree ≫
                projectiveBundleProj E hfree) rfl E).symm ≪≫
            (QuasiCoherentDescent.pullbackComparison B S hS
              (splitEpiAtlasHom E E' u σ hσ hfree hfree')
              (projectiveBundleAtlas E hfree ≫ projectiveBundleProj E hfree)
              (projectiveBundleAtlas E' hfree' ≫ projectiveBundleProj E' hfree')
              (splitEpiAtlasHom_comp_projectiveBundleAtlas_comp_proj E E' u σ hσ hfree hfree')
                E).symm) ≪≫
          (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E' hfree')
            (projectiveBundleProj E' hfree') (projectiveBundleAtlas E' hfree' ≫
              projectiveBundleProj E' hfree') rfl E).symm.symm)
        ((modulePullback B S hS (projectiveBundleAtlas E' hfree')).map
            ((modulePullback B S hS (projectiveBundleProj E' hfree')).map u) ≫
          projectiveBundleChartQuotient E' hfree') := by
  with_reducible exact
    exists_quotientIsoComp_siteApp_projectiveBundleChartQuotient E E' u σ hσ hfree hfree'

/-- **On the presenting chart bundle of `𝐏(ℰ')` the two quotients agree**: the inverse images
along the atlas `a : 𝐏(ℰ'|_U) ⟶ 𝐏(ℰ')` of `π'^*ℰ ≅ i^*π^*ℰ ⟶ i^*𝒪_{𝐏(ℰ)}(1)` and of
`π'^*u ≫ (π'^*ℰ' ⟶ 𝒪_{𝐏(ℰ')}(1))` are isomorphic quotients. -/
theorem exists_iso_modulePullback_projectiveBundleAtlas_splitEpi :
    ∃ β : (modulePullback B S hS (projectiveBundleAtlas E' hfree')).obj
        ((modulePullback B S hS (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree')).obj
          (projectiveBundleTwist E hfree).obj) ≅
        (modulePullback B S hS (projectiveBundleAtlas E' hfree')).obj
          (projectiveBundleTwist E' hfree').obj,
      (modulePullback B S hS (projectiveBundleAtlas E' hfree')).map
          ((QuasiCoherentDescent.pullbackComparison B S hS
              (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree')
                (projectiveBundleProj E hfree)
              (projectiveBundleProj E' hfree')
              (projectiveBundleMapOfSplitEpi_comp_projectiveBundleProj E E' u σ hσ hfree hfree')
              E).hom ≫
            (modulePullback B S hS (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree')).map
              (X := (modulePullback B S hS (projectiveBundleProj E hfree)).obj E)
              (projectiveBundleTautological E hfree).hom) ≫ β.hom =
        (modulePullback B S hS (projectiveBundleAtlas E' hfree')).map
          ((modulePullback B S hS (projectiveBundleProj E' hfree')).map u ≫
            (projectiveBundleTautological E' hfree').hom) := by
  obtain ⟨γ, hγ⟩ := exists_quotientIsoComp_splitEpiAtlasHom_projectiveBundleChartQuotient E E' u σ
    hσ hfree hfree'
  exact @exists_iso_modulePullback_comp_of_triangle B S hS X (projectiveBundle E hfree)
    (projectiveBundle E' hfree') (projectiveBundleGroupoid E hfree).objects
    (projectiveBundleGroupoid E' hfree').objects
    (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree') (projectiveBundleProj E hfree)
    (projectiveBundleProj E' hfree')
    (projectiveBundleMapOfSplitEpi_comp_projectiveBundleProj E E' u σ hσ hfree hfree')
    (projectiveBundleAtlas E' hfree') (splitEpiAtlasHom E E' u σ hσ hfree hfree')
    (projectiveBundleAtlas E hfree)
    (projectiveBundleAtlas_comp_mapOfSplitEpi_eq_splitEpiAtlasHom_comp E E' u σ hσ hfree hfree')
    (projectiveBundleAtlas E' hfree' ≫ projectiveBundleProj E' hfree') rfl
    (splitEpiAtlasHom_comp_projectiveBundleAtlas_comp_proj E E' u σ hσ hfree hfree')
    E E' u (projectiveBundleTwist E hfree).obj (projectiveBundleTautological E hfree).hom
    (projectiveBundleTwist E' hfree').obj (projectiveBundleTautological E' hfree').hom
    (projectiveBundleChartTwist E hfree)
    (projectiveBundleTwistAtlasIso E hfree) (projectiveBundleChartQuotient E hfree)
    (modulePullback_map_projectiveBundleTautological E hfree)
    (projectiveBundleChartTwist E' hfree')
    (projectiveBundleTwistAtlasIso E' hfree') (projectiveBundleChartQuotient E' hfree')
    (modulePullback_map_projectiveBundleTautological E' hfree') γ hγ

omit hE in
include σ hσ in
/-- The quotient `π'^*u ≫ (π'^*ℰ' ⟶ 𝒪_{𝐏(ℰ')}(1))` of `π'^*ℰ` is an epimorphism: `π'^*u` is a split
epimorphism. -/
theorem epi_modulePullback_map_comp_projectiveBundleTautological :
    Epi ((modulePullback B S hS (projectiveBundleProj E' hfree')).map u ≫
      (projectiveBundleTautological E' hfree').hom) := by
  have := ((⟨σ, hσ⟩ : SplitEpi u).map (modulePullback B S hS (projectiveBundleProj E' hfree'))).epi
  exact epi_comp _ _

/-- **The compatibility of an isomorphism `e : i^*𝒪_{𝐏(ℰ)}(1) ≅ 𝒪_{𝐏(ℰ')}(1)` with the
tautological quotients**: `π'^*ℰ ≅ i^*π^*ℰ ⟶ i^*𝒪_{𝐏(ℰ)}(1)` followed by `e` is
`π'^*u ≫ (π'^*ℰ' ⟶ 𝒪_{𝐏(ℰ')}(1))`. A structure, so that the isomorphism chosen from
`AlgebraicGeometry.Space.exists_projectiveBundleSplitEpiTwistIso` mentions only its name. -/
structure IsProjectiveBundleSplitEpiTwistIso
    (e : (modulePullback B S hS (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree')).obj
      (projectiveBundleTwist E hfree).obj ≅
      (projectiveBundleTwist E' hfree').obj) : Prop where
  /-- `π'^*ℰ ≅ i^*π^*ℰ ⟶ i^*𝒪(1) ≅ 𝒪'(1)` is `π'^*u` followed by the tautological quotient. -/
  comp_hom : ((QuasiCoherentDescent.pullbackComparison B S hS
    (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree')
        (projectiveBundleProj E hfree) (projectiveBundleProj E' hfree')
        (projectiveBundleMapOfSplitEpi_comp_projectiveBundleProj E E' u σ hσ hfree hfree') E).hom ≫
      (modulePullback B S hS (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree')).map
        (X := (modulePullback B S hS (projectiveBundleProj E hfree)).obj E)
        (projectiveBundleTautological E hfree).hom) ≫ e.hom =
    (modulePullback B S hS (projectiveBundleProj E' hfree')).map u ≫
      (projectiveBundleTautological E' hfree').hom

/-- **The inverse image along `i : 𝐏(ℰ') ⟶ 𝐏(ℰ)` of `𝒪_{𝐏(ℰ)}(1)` is `𝒪_{𝐏(ℰ')}(1)`, compatibly
with the tautological quotients**: both quotients of `π'^*ℰ` are isomorphic after the inverse image
along the flat surjective atlas of `𝐏(ℰ')`
(`AlgebraicGeometry.Space.exists_iso_modulePullback_projectiveBundleAtlas_splitEpi`), and a
quotient is determined by its inverse image along a flat surjection. -/
theorem exists_projectiveBundleSplitEpiTwistIso :
    ∃ e : (modulePullback B S hS
      (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree')).obj
      (projectiveBundleTwist E hfree).obj ≅
        (projectiveBundleTwist E' hfree').obj,
      IsProjectiveBundleSplitEpiTwistIso E E' u σ hσ hfree hfree' e :=
  ⟨_, ⟨@comp_quotientIsoOfModulePullbackIsFlatOfSurjectiveOfComp_hom B S hS
      (projectiveBundle E hfree)
      (projectiveBundle E' hfree') (projectiveBundleGroupoid E' hfree').objects
      (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree')
      ((modulePullback B S hS (projectiveBundleProj E hfree)).obj E)
      (projectiveBundleTwist E hfree).obj (projectiveBundleTautological E hfree).hom
      (epi_projectiveBundleTautological E hfree)
      ((modulePullback B S hS (projectiveBundleProj E' hfree')).obj E)
      (projectiveBundleTwist E' hfree').obj (QuasiCoherentDescent.pullbackComparison B S hS
        (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree')
        (projectiveBundleProj E hfree) (projectiveBundleProj E' hfree')
        (projectiveBundleMapOfSplitEpi_comp_projectiveBundleProj E E' u σ hσ hfree hfree') E)
      ((modulePullback B S hS (projectiveBundleProj E' hfree')).map u ≫
        (projectiveBundleTautological E' hfree').hom)
      (epi_modulePullback_map_comp_projectiveBundleTautological E E' u σ hσ hfree')
      (projectiveBundleAtlas E' hfree')
      (isFlat_of_isEtale B S hS (presentationAtlas_isEtale _))
      (surjective_pointsMap_projectiveBundleAtlas E' hfree')
      (exists_iso_modulePullback_projectiveBundleAtlas_splitEpi E E' u σ hσ hfree hfree')⟩⟩

/-- **The isomorphism `i^*𝒪_{𝐏(ℰ)}(1) ≅ 𝒪_{𝐏(ℰ')}(1)`** along the closed immersion
`i : 𝐏(ℰ') ⟶ 𝐏(ℰ)` of a split quotient `u : ℰ ⟶ ℰ'`. -/
def projectiveBundleSplitEpiTwistIso :
    (modulePullback B S hS
      (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree')).obj
      (projectiveBundleTwist E hfree).obj ≅
      (projectiveBundleTwist E' hfree').obj :=
  (exists_projectiveBundleSplitEpiTwistIso E E' u σ hσ hfree hfree').choose

/-- **`i^*𝒪_{𝐏(ℰ)}(1) ≅ 𝒪_{𝐏(ℰ')}(1)` carries the inverse image of the tautological quotient
of `𝐏(ℰ)` to `π'^*u` followed by the tautological quotient of `𝐏(ℰ')`.** -/
@[reassoc]
theorem comp_projectiveBundleSplitEpiTwistIso_hom :
    ((QuasiCoherentDescent.pullbackComparison B S hS
      (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree')
        (projectiveBundleProj E hfree) (projectiveBundleProj E' hfree')
        (projectiveBundleMapOfSplitEpi_comp_projectiveBundleProj E E' u σ hσ hfree hfree') E).hom ≫
      (modulePullback B S hS (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree')).map
        (X := (modulePullback B S hS (projectiveBundleProj E hfree)).obj E)
        (projectiveBundleTautological E hfree).hom) ≫
        (projectiveBundleSplitEpiTwistIso E E' u σ hσ hfree hfree').hom =
      (modulePullback B S hS (projectiveBundleProj E' hfree')).map u ≫
        (projectiveBundleTautological E' hfree').hom :=
  (exists_projectiveBundleSplitEpiTwistIso E E' u σ hσ hfree hfree').choose_spec.comp_hom

end Chart

/-! ### The hyperplane at infinity of the projective completion -/

section Completion

attribute [local instance] HasBinaryBiproducts.of_hasBinaryProducts

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (E : Modules.{u, u} B S hS X.1 X.2) {r : ℕ}
  (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) E r)

/-- **The twist of the projective completion restricts to the twist of `𝐏(ℰ)` along the
hyperplane at infinity**: `i^*𝒪_{𝐏(ℰ ⊕ 𝒪_X)}(1) ≅ 𝒪_{𝐏(ℰ)}(1)` for
`i = AlgebraicGeometry.Space.projectiveCompletionInfinityImmersion`, the case `u = pr₁` of
`AlgebraicGeometry.Space.projectiveBundleSplitEpiTwistIso`. -/
def projectiveCompletionInfinityTwistIso :
    (modulePullback B S hS (projectiveCompletionInfinityImmersion E hr)).obj
        (projectiveCompletionTwist E hr).obj ≅
      (@projectiveBundleTwist B S hS X E (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        hr.isFiniteLocallyFreeOnSite).obj :=
  @projectiveBundleSplitEpiTwistIso B S hS X (addUnit X.2 E) E (isQuasicoherentOnSite_addUnit hr)
    (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) biprod.fst biprod.inl
    biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr) hr.isFiniteLocallyFreeOnSite

/-- `AlgebraicGeometry.Space.projectiveCompletionInfinityTwistIso`, as the existence of an
isomorphism. -/
theorem nonempty_projectiveCompletionInfinityTwistIso :
    Nonempty ((modulePullback B S hS (projectiveCompletionInfinityImmersion E hr)).obj
        (projectiveCompletionTwist E hr).obj ≅
      (@projectiveBundleTwist B S hS X E (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        hr.isFiniteLocallyFreeOnSite).obj) :=
  ⟨projectiveCompletionInfinityTwistIso E hr⟩

end Completion

end AlgebraicGeometry.Space

end
