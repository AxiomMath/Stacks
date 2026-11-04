module

public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.RepresentedFibreComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartSchemeRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionCoherent
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationFromAffine
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPullbackStability

/-!
# The relative assassin containment locus over an affine base

Let `V` be an affine scheme of the big fppf site, let `X` be an algebraic space of finite
presentation over `V` and let `F` be a quasi-coherent `𝒪_X`-module of finite presentation. This
file proves that the containment locus `AlgebraicGeometry.Space.relativeAssassinContainmentLocus`
is locally constructible in this case.

## Main results

* `AlgebraicGeometry.Space.exists_affine_etale_surjective_schemeSpace_chart`: a quasi-compact
  algebraic space over a scheme `V` of the site has a surjective étale chart whose scheme is
  affine, together with the morphism of the site under it.
* `AlgebraicGeometry.Space.quasiCompact_chartOpenOfOpenPoints_comp`: over an affine base, the
  open subscheme of an affine étale chart which reads a quasi-compact open subset of `|X|` is
  quasi-compact over the base.
* `AlgebraicGeometry.Space.isFinitePresentation_baseChangeModule_of_isFinitePresentationOnSite`:
  the Zariski restriction to an affine scheme étale over `X` of an `𝒪_X`-module of finite
  presentation on the small étale site is of finite presentation.
* `AlgebraicGeometry.Space.isLocallyConstructible_relativeAssassinContainmentLocus_of_isAffine`:
  the containment locus over an affine base is locally constructible.

## References

* [Stacks Project, Tag 0CVV](https://stacks.math.columbia.edu/tag/0CVV)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 073B](https://stacks.math.columbia.edu/tag/073B)
* [Stacks Project, Tag 06G5](https://stacks.math.columbia.edu/tag/06G5)
-/

@[expose] public noncomputable section

open CategoryTheory Topology

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An affine surjective étale scheme chart of a quasi-compact algebraic space over a scheme
of the site.** A quasi-compact algebraic space `X` with a morphism `f` to the algebraic space of a
scheme `V₀` of the site has a surjective étale chart `φ : schemeSpace W₀ ⟶ X` with `W₀` affine,
together with a morphism `α₀ : W₀ ⟶ V₀` of the site such that `φ ≫ f = schemeSpaceMap α₀`. -/
theorem exists_affine_etale_surjective_schemeSpace_chart {X : AlgebraicSpaces B S hS}
    (V₀ : BigFppfOver B S hS) (f : X ⟶ schemeSpace V₀)
    (hXqc : IsQuasiCompactSpace B S hS X.1) :
    ∃ (W₀ : BigFppfOver B S hS) (φ : schemeSpace W₀ ⟶ X) (α₀ : W₀ ⟶ V₀),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W₀) ∧
        IsEtale B S hS φ.hom ∧
          Function.Surjective (pointsMap B S hS (schemeSpace W₀).1 φ.hom) ∧
            φ ≫ f = schemeSpaceMap α₀ := by
  obtain ⟨W₀, a, haff, hasurj, haetale⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.1 X.2).1 hXqc
  obtain ⟨α₀, hα₀⟩ := (yoneda (C := BigFppfOver B S hS)).map_surjective (a ≫ f.hom)
  refine ⟨W₀, ObjectProperty.homMk a, α₀, haff, haetale,
    (surjective_iff_surjective_pointsMap B S hS X.1 X.2 W₀ a).1 hasurj, ?_⟩
  exact ObjectProperty.hom_ext _ hα₀.symm

/-- **Over an affine base, the open subscheme of an affine étale chart reading a quasi-compact
open subset of the points of the space is quasi-compact over the base.** Let `V` and `W` be affine
schemes of the site, let `f : X ⟶ schemeSpace V` be quasi-separated and let
`φ : schemeSpace W ⟶ X` and `α : W ⟶ V`. For a quasi-compact open `U ⊆ |X|`, the open subscheme
`AlgebraicGeometry.Space.chartOpenOfOpenPoints` of `W` cut out by the inverse image of `U` is
quasi-compact over `V` along `α`. -/
theorem quasiCompact_chartOpenOfOpenPoints_comp {X : AlgebraicSpaces B S hS}
    (V W : BigFppfOver B S hS) (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    (f : X ⟶ schemeSpace V) (hfqs : IsQuasiSeparated B S hS f.hom)
    (φ : schemeSpace W ⟶ X) (α : W ⟶ V)
    (U : Set (points B S hS X.1)) (hUopen : IsOpen U) (hUcpt : IsCompact U) :
    QuasiCompact ((chartOpenOfOpenPoints B S hS W φ U hUopen).ι ≫
      (BigFppfOver.toScheme B S hS).map α) := by
  have := hV
  have := hW
  have hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1 :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal X.2
      (isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS (yoneda.obj V)
        B.contains_terminal ⟨V, inferInstance, ⟨Functor.RepresentableBy.yoneda V⟩⟩) hfqs
  have hφqc : IsQuasiCompact B S hS φ.hom :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS B.contains_terminal X.2 hXqs
      (isQuasiCompactSpace_yoneda_of_isAffine B S hS W hW) φ.hom
  have himg : IsCompact (pointsToScheme B S hS W ''
      (pointsMap B S hS (schemeSpace W).1 φ.hom ⁻¹' U)) :=
    (isQuasiCompactMap_pointsMap B S hS (schemeSpace W).2 X.2 φ.hom hφqc hUopen hUcpt).image
      (schemePointsHomeomorph B S hS W).continuous
  have : CompactSpace ↥(chartOpenOfOpenPoints B S hS W φ U hUopen).toScheme :=
    isCompact_iff_compactSpace.mp himg
  have : QuasiCompact
      (Limits.terminal.from (chartOpenOfOpenPoints B S hS W φ U hUopen).toScheme) :=
    (compactSpace_iff_quasiCompact _).mp inferInstance
  have : QuasiCompact (((chartOpenOfOpenPoints B S hS W φ U hUopen).ι ≫
      (BigFppfOver.toScheme B S hS).map α) ≫
      Limits.terminal.from ((BigFppfOver.toScheme B S hS).obj V)) := by
    rwa [Limits.terminal.hom_ext (((chartOpenOfOpenPoints B S hS W φ U hUopen).ι ≫
      (BigFppfOver.toScheme B S hS).map α) ≫
      Limits.terminal.from ((BigFppfOver.toScheme B S hS).obj V))
      (Limits.terminal.from (chartOpenOfOpenPoints B S hS W φ U hUopen).toScheme)]
  exact QuasiCompact.of_comp _ (Limits.terminal.from ((BigFppfOver.toScheme B S hS).obj V))

/-- **The Zariski restriction of a module of finite presentation to an affine scheme étale over
the space is of finite presentation.** For a quasi-coherent `𝒪_X`-module `F` of finite
presentation on the small étale site of `X` and an affine scheme `W` of the site with a morphism
`φ : schemeSpace W ⟶ X`, the `AlgebraicGeometry.Scheme.Modules` which `F` becomes on `W` is of
finite presentation. -/
theorem isFinitePresentation_baseChangeModule_of_isFinitePresentationOnSite
    {X : AlgebraicSpaces B S hS} (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (hFfp : SheafOfModules.IsFinitePresentationOnSite F)
    (W : BigFppfOver B S hS) (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    (φ : schemeSpace W ⟶ X) :
    (baseChangeModule B S hS F W φ.hom).IsFinitePresentation := by
  have hGqc : ((modulePullback B S hS φ).obj F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS φ F hF
  have hGfp : SheafOfModules.IsFinitePresentationOnSite ((modulePullback B S hS φ).obj F) :=
    isFinitePresentationOnSite_modulePullback B S hS φ F hFfp
  have hsec := finitePresentation_sectionsTop_chartSchemeModule B S hS (schemeSpace W)
    ((modulePullback B S hS φ).obj F) hGqc hGfp (idEtaleChart B S hS W) hW
  have : (chartSchemeModule B S hS (schemeSpace W) ((modulePullback B S hS φ).obj F) hGqc
      (idEtaleChart B S hS W)).IsQuasicoherent :=
    isQuasicoherent_chartSchemeModule B S hS (schemeSpace W) ((modulePullback B S hS φ).obj F)
      hGqc (idEtaleChart B S hS W)
  have : IsAffine (chartScheme (idEtaleChart B S hS W)) := hW
  have hmod : (chartSchemeModule B S hS (schemeSpace W) ((modulePullback B S hS φ).obj F) hGqc
      (idEtaleChart B S hS W)).IsFinitePresentation :=
    Stacks.AlgebraicGeometry.FinitePresentationLocal.isFinitePresentation_of_affineCover _
      (fun _ : PUnit.{u + 1} => (⊤ : (chartScheme (idEtaleChart B S hS W)).Opens))
      (TopologicalSpace.IsOpenCover.mk iSup_const)
      (fun _ => isAffineOpen_top (chartScheme (idEtaleChart B S hS W))) fun _ => hsec
  exact (SheafOfModules.isFinitePresentation _).prop_of_iso
    (restrictToChartSchemeIsoChartSchemeModule B S hS (schemeSpace W)
      ((modulePullback B S hS φ).obj F) hGqc (idEtaleChart B S hS W)).symm hmod

/-- **The relative assassin containment locus over an affine base is locally constructible.**
Let `V` be an affine scheme of the site, let `X` be an algebraic space of finite presentation
over `V`, let `F` be a quasi-coherent `𝒪_X`-module of finite presentation and let `U` be a
quasi-compact open subset of `|X|`. Then the set of points of `V` over which every point of the
relative assassin of `F` above that point lies in `U` is locally constructible. -/
theorem isLocallyConstructible_relativeAssassinContainmentLocus_of_isAffine
    {X : AlgebraicSpaces B S hS} (V : BigFppfOver B S hS)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (f : X ⟶ schemeSpace V) (hf : IsFinitePresentation B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (hFfp : SheafOfModules.IsFinitePresentationOnSite F)
    (U : Set (points B S hS X.1)) (hUopen : IsOpen U) (hUcpt : IsCompact U) :
    IsLocallyConstructible (relativeAssassinContainmentLocus B S hS V f F U) := by
  have := hV
  have hXqc : IsQuasiCompactSpace B S hS X.1 :=
    isQuasiCompactSpace_of_isFinitePresentation B S hS f.hom (schemeSpace V).2
      (isQuasiCompactSpace_yoneda_of_isAffine B S hS V hV) hf
  obtain ⟨W, φ, α, hWaff, hφ, hsurj, hα⟩ :=
    exists_affine_etale_surjective_schemeSpace_chart B S hS V f hXqc
  have := hWaff
  exact isLocallyConstructible_relativeAssassinContainmentLocus B S hS V W f F U hUopen
    φ hφ hsurj α hα hf.1 inferInstance inferInstance hF
    (isFinitePresentation_baseChangeModule_of_isFinitePresentationOnSite B S hS F hF hFfp
      W hWaff φ)
    (quasiCompact_chartOpenOfOpenPoints_comp B S hS V W hV hWaff f hf.2.2 φ α U hUopen hUcpt)

end AlgebraicGeometry.Space

end
