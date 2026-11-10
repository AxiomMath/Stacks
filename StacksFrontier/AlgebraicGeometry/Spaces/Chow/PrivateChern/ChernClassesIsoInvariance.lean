module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernClassesCongr
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ProjectiveBundleEmbeddingTwist
public import StacksFrontier.AlgebraicGeometry.RelativeProjMapDomain.EventualBijective
public import StacksFrontier.AlgebraicGeometry.ProjBundleSurjection.Functoriality
public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianAtlasDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ReadingBundleComparison

/-!
# Isomorphic modules have the same Chern classes

In Situation 0EDT let `X/B` be good and `ℰ ≅ ℰ'` finite locally free `𝒪_X`-modules of rank `r`.
Then `c_n(ℰ) ∩ - = c_n(ℰ') ∩ -` for every `n`, for the Chern classes of Stacks 0ERZ.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.isIso_projBundleSurjectionMap`: the morphism of relative
  projective spectra induced by a homomorphism of graded algebras which is an isomorphism in large
  degrees is an isomorphism.
* `AlgebraicGeometry.Space.PrivateChern.isIso_bundleEmbedding`: the closed immersion of projective
  bundles of schemes induced by an isomorphism of modules is an isomorphism.
* `AlgebraicGeometry.Space.PrivateChern.isPullback_projectiveBundleEmbedding_id`: the morphism
  `𝐏(ℱ) ⟶ 𝐏(ℰ)` induced by an isomorphism `ℰ ≅ ℱ` is cartesian over the identity of `X`.
* `AlgebraicGeometry.Space.PrivateChern.chernCap_congr_iso`: isomorphic modules have the same
  Chern classes.

## References

* [Stacks Project, Tag 0ERZ](https://stacks.math.columbia.edu/tag/0ERZ)
* [Stacks Project, Tag 07ZE](https://stacks.math.columbia.edu/tag/07ZE)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.PrivateChern

section Scheme

open Stacks.AlgebraicGeometry Stacks.AlgebraicGeometry.ProjShared
  Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjBridge
  Stacks.AlgebraicGeometry.RelativeProjTwistGlue
  Stacks.AlgebraicGeometry.RelativeProjMapDomain Stacks.AlgebraicGeometry.ProjBundleSurjection

variable {S : Scheme.{u}} {A B : SheafGradedAlgebra S} {ψ : SheafGradedAlgebraHom A B}

/-- The morphism of relative projective spectra induced by a homomorphism of graded algebras
which is surjective on affine sections and an isomorphism in every large degree is an
isomorphism. -/
theorem isIso_projBundleSurjectionMap (hψ : SurjectiveOnAffineSections ψ)
    (hiso : ∀ᶠ d : ℕ in Filter.atTop, IsIso (ψ.app (d : ℤ))) : IsIso (map hψ) := by
  change MorphismProperty.isomorphisms Scheme (map hψ)
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun U : AffineOpen S => ((relativeProj A).chart U.1 U.2).opensRange)
    (iSup_opensRange_chart_eq_top (relativeProj A)) fun U => ?_
  have e₁ : Arrow.mk (ProjBundleSurjection.chartMap hψ U.1 U.2) ≅
      Arrow.mk (pullback.snd (map hψ) ((relativeProj A).chart U.1 U.2)) :=
    Arrow.isoMk ((isPullback_chart hψ U.1 U.2).isoIsPullback _ _
      (IsPullback.of_hasPullback _ _)) (Iso.refl _)
  have hc : IsIso (ProjBundleSurjection.chartMap hψ U.1 U.2) := by
    have := Stacks.AlgebraicGeometry.RelativeProjChain.isIso_mapHom_of_eventually_bijective
      (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)
      (eventually_bijective_gradedAddHom ψ hiso U.1)
    rw [ProjBundleSurjection.chartMap, mapHomOfTop]
    infer_instance
  exact (MorphismProperty.arrow_mk_iso_iff (P := MorphismProperty.isomorphisms Scheme)
    (e₁.trans (morphismRestrictOpensRange (map hψ) ((relativeProj A).chart U.1 U.2)).symm)).mp hc

variable {X : Scheme.{u}} {E₁ E₂ : X.Modules}

/-- The homomorphism of symmetric algebras of `Stacks.SymGraded.schemeSymAlgebraHom` is the one
given by the universal property of the symmetric algebra. -/
theorem symUnitalHom_eq_symmetricAlgebraUnitalHom (g : E₁ ⟶ E₂) :
    symUnitalHom g = Scheme.Modules.symmetricAlgebraUnitalHom X g :=
  SheafOfModules.GradedAlgebra.IsUniversal.descComp_unique
    (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra X E₁) g
    (Scheme.Modules.symmetricAlgebraGen X E₂) _
    (Stacks.Chow.GenuineChern.symmetricAlgebraGen_comp_schemeSymAlgebraHom g)

/-- An isomorphism of modules induces isomorphisms of the homogeneous pieces of the symmetric
algebras. -/
theorem isIso_schemeSymAlgebraHom_app [E₁.IsQuasicoherent] [E₂.IsQuasicoherent] (g : E₁ ⟶ E₂)
    [IsIso g] (n : ℤ) :
    IsIso ((Stacks.SymGraded.schemeSymAlgebraHom g).app n) := by
  change IsIso ((symUnitalHom g).app n)
  rw [symUnitalHom_eq_symmetricAlgebraUnitalHom]
  exact Stacks.SymGraded.isIso_symSheafGradedAlgebraHom_app (E₁ := E₁) (E₂ := E₂)
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E₁)
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E₂) (asIso g) n

/-- **The closed immersion of projective bundles induced by an isomorphism of finite locally free
modules is an isomorphism.** -/
theorem isIso_bundleEmbedding
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E₁]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E₂] (g : E₁ ⟶ E₂) [IsIso g] :
    IsIso (Stacks.Chow.GenuineChern.bundleEmbedding g) :=
  isIso_projBundleSurjectionMap _
    (Filter.Eventually.of_forall fun d => isIso_schemeSymAlgebraHom_app g (d : ℤ))

end Scheme

section Chart

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  {E F : Modules.{u, u} B S hS X.1 X.2} [hE : E.IsQuasicoherentOnSite]
  [hF : F.IsQuasicoherentOnSite] (hfreeE : SheafOfModules.IsFiniteLocallyFreeOnSite E)
  (hfreeF : SheafOfModules.IsFiniteLocallyFreeOnSite F) (q : E ⟶ F)
  (hq : ∀ V : SmallEtale B S hS X.1, Epi (chartModuleMap q V))

omit hE hF in
/-- The reading over an étale chart of an isomorphism of modules is an isomorphism. -/
theorem isIso_chartModuleMap [IsIso q] (V : SmallEtale B S hS X.1) :
    IsIso (chartModuleMap q V) :=
  show IsIso ((readingFunctor _).map ((modulePullback B S hS _).map q)) from inferInstance

/-- Over an étale chart, the closed immersion of chart projective bundles induced by an
isomorphism of modules is an isomorphism. -/
theorem isIso_chartBundleEmbedding [IsIso q] (V : SmallEtale B S hS X.1) :
    IsIso (chartBundleEmbedding hfreeE hfreeF q hq V) := by
  have := isFiniteLocallyFree_chartBundleModule E hfreeE V
  have := isFiniteLocallyFree_chartBundleModule F hfreeF V
  have := hq V
  have := isIso_chartModuleMap q V
  rw [chartBundleEmbedding]
  exact IsIso.comp_isIso' (Iso.isIso_inv _)
    (IsIso.comp_isIso' (isIso_bundleEmbedding (chartModuleMap q V)) (Iso.isIso_hom _))

/-- Over the presenting chart, the closed immersion of chart projective bundles induced by an
isomorphism of modules is a cartesian square over the identity of the chart, in the site. -/
theorem isPullback_siteApp_projectiveBundleFamilyEmbedding [IsIso q] :
    IsPullback ((projectiveBundleFamilyEmbedding hfreeE hfreeF q hq).siteApp (bundleBaseChart X))
      ((projectiveBundleChartFamily F hfreeF).siteToChart (bundleBaseChart X))
      ((projectiveBundleChartFamily E hfreeE).siteToChart (bundleBaseChart X))
      (𝟙 _) := by
  refine IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS) ?_
  rw [CategoryTheory.Functor.map_id]
  have : IsIso ((BigFppfOver.toScheme B S hS).map
      ((projectiveBundleFamilyEmbedding hfreeE hfreeF q hq).siteApp (bundleBaseChart X))) :=
    isIso_chartBundleEmbedding hfreeE hfreeF q hq (bundleBaseChart X)
  exact IsPullback.of_horiz_isIso ⟨(chartBundleEmbedding_comp_toChart hfreeE hfreeF q hq
    (bundleBaseChart X)).trans (Category.comp_id _).symm⟩

/-- **The morphism `𝐏(ℱ) ⟶ 𝐏(ℰ)` induced by an isomorphism `ℰ ≅ ℱ` is an isomorphism over `X`**:
its square over the identity of `X` is cartesian. -/
theorem isPullback_projectiveBundleEmbedding_id [IsIso q] :
    IsPullback (projectiveBundleEmbedding hfreeE hfreeF q hq).hom
      (projectiveBundleProj F hfreeF).hom (projectiveBundleProj E hfreeE).hom (𝟙 X.1) := by
  have hproj : (projectiveBundleEmbedding hfreeE hfreeF q hq).hom ≫
      (projectiveBundleProj E hfreeE).hom = (projectiveBundleProj F hfreeF).hom ≫ 𝟙 X.1 :=
    (congrArg (fun f => f.hom) (projectiveBundleEmbedding_comp_proj hfreeE hfreeF q hq)).trans
      (Category.comp_id _).symm
  have hsq : projectiveBundleChart F hfreeF ≫ (projectiveBundleEmbedding hfreeE hfreeF q hq).hom =
      yoneda.map ((projectiveBundleFamilyEmbedding hfreeE hfreeF q hq).siteApp
        (bundleBaseChart X)) ≫ projectiveBundleChart E hfreeE :=
    congrArg (fun f => f.hom)
      (projectiveBundleAtlas_comp_projectiveBundleEmbedding hfreeE hfreeF q hq)
  have hbig : IsPullback (projectiveBundleChart F hfreeF ≫
        (projectiveBundleEmbedding hfreeE hfreeF q hq).hom)
      (yoneda.map ((projectiveBundleChartFamily F hfreeF).siteToChart (bundleBaseChart X)))
      (projectiveBundleProj E hfreeE).hom ((bundleBaseChart X).obj.hom ≫ 𝟙 X.1) := by
    rw [hsq, Category.comp_id]
    have h := ((isPullback_siteApp_projectiveBundleFamilyEmbedding hfreeE hfreeF q hq).map
      yoneda).paste_horiz (isPullback_projectiveBundleProj E hfreeE)
    rwa [CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact isPullback_of_isPullback_atlas B S hS (projectiveBundle F hfreeF).property.isSheaf
    (projectiveBundle E hfreeE).property.isSheaf X.property.isSheaf X.property.isSheaf hproj
    (projectiveBundlePresentation X).surjective (projectiveBundlePresentation X).etale
    (isPullback_projectiveBundlePresentation X) (isPullback_projectiveBundleProj F hfreeF) hbig
    (((projectiveBundleChartFamily F hfreeF).isPullback_siteMap (presentationRelationTargetHom
        (projectiveBundlePresentation X))).map yoneda)
    ((projectiveBundleChartFamily F hfreeF).isPullback_siteMap (presentationRelationSourceHom
        (projectiveBundlePresentation X))).w
    (isPullback_projectiveBundleSpaceChart_relation F hfreeF).w

end Chart

section ChernClasses

variable {D : BaseSpaceDimensionSituation.{u}}

/-- **Isomorphic modules have the same Chern classes**: if `ℰ ≅ ℰ'` are finite locally free of
rank `r` on a good space `X`, then `c_n(ℰ) ∩ - = c_n(ℰ') ∩ -` for every `n`. -/
theorem chernCap_congr_iso {X : D.Ambient} {sX : X ⟶ D.space} (hX : D.IsGood sX)
    (E E' : Modules.{u, u} D.site D.base D.base_mem X hX.1) (r : ℕ)
    (h : IsFiniteLocallyFreeOfRank D sX hX E r) (h' : IsFiniteLocallyFreeOfRank D sX hX E' r)
    (n : ℕ) (e : Nonempty (E ≅ E')) :
    chernCap.{u, u + 1} (hX := hX) E r h n = chernCap.{u, u + 1} (hX := hX) E' r h' n := by
  obtain ⟨e⟩ := e
  cases r with
  | zero => rfl
  | succ d =>
    let := isQuasicoherentOnSite_of_rank E h
    let := isQuasicoherentOnSite_of_rank E' h'
    have hfree := isFiniteLocallyFreeOnSite_of_rank E h
    have hfree' := isFiniteLocallyFreeOnSite_of_rank E' h'
    have : IsIso e.hom := Iso.isIso_hom e
    have : Epi e.hom := @IsIso.epi_of_iso _ _ _ _ e.hom (Iso.isIso_hom e)
    have hq : ∀ V : SmallEtale D.site D.base D.base_mem X,
        Epi (chartModuleMap (X := goodSpace hX) e.hom V) := fun V =>
      have := isIso_chartModuleMap (X := goodSpace hX) e.hom V
      IsIso.epi_of_iso _
    obtain ⟨t, -⟩ := exists_projectiveBundleEmbedding_twistIso (X := goodSpace hX) hfree hfree'
      e.hom hq
    exact (chernCap_eq_of_isPullback_projectiveBundle E E' d h h'
      (isPullback_projectiveBundleEmbedding_id (X := goodSpace hX) hfree hfree' e.hom hq) t n).symm

end ChernClasses

end AlgebraicGeometry.Space.PrivateChern

end
