module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionAffinePartSection
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionInfinityZeroScheme

/-!
# The hyperplane section of a split quotient is invertible off its projective bundle

Let `X` be an algebraic space, `u : ℰ ⟶ ℰ'` a split epimorphism of finite locally free
`𝒪_X`-modules with closed immersion `i : 𝐏(ℰ') ⟶ P = 𝐏(ℰ)` and open complement
`U = P ∖ i(𝐏(ℰ'))`, and `σ₀ : 𝒪_X ⟶ ℰ` a section completing `u` to a split short exact sequence
`0 ⟶ 𝒪_X ⟶ ℰ ⟶ ℰ' ⟶ 0`. The hyperplane section `𝒪_P ≅ π^*𝒪_X ⟶ π^*ℰ ⟶ 𝒪_P(1)` of `σ₀`
is an isomorphism on the chart `U_U ⟶ U` of `U`.

For the projective completion `𝐏(ℰ ⊕ 𝒪_X)` and the summand `𝒪_X` this is the invertibility of
the section `s` off the hyperplane at infinity.

## Main results

* `AlgebraicGeometry.Space.isIso_pullback_splitEpiComplementAtlasChartHom_hyperplane`: on the
  chart `U_U ⟶ P_U`, the hyperplane section of the chart bundle of a chart-level split datum is
  invertible.
* `AlgebraicGeometry.Space.isIso_modulePullback_splitEpiComplementAtlasChart_sectionHom`: the
  hyperplane section of `σ₀` is invertible on the chart `U_U ⟶ U ⟶ 𝐏(ℰ)`.
* `isIso_modulePullback_projectiveCompletionAffinePartHom_projectiveCompletionSectionHom`: the
  section `s` of `(0, 1)` is invertible on the affine part of the projective completion.

## Implementation notes

The presenting chart bundle is spelled both as the object `(BigFppfOver.toScheme B S hS).obj P.U`
of the site and as the scheme `𝐏(ℰ|_U)`; the two agree only after unfolding
`AlgebraicGeometry.Space.CartesianChartFamily.site`, which implicit arguments are not compared
with by default. The local attribute `implicit_reducible` on it (and on
`AlgebraicGeometry.BigFppfOver.siteObjectOver`) lets the generic lemmas of Stacks 01NS apply
without unfolding the projective bundles.

## References

* [Stacks Project, Tag 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- The inverse image of a morphism of modules along the morphism of schemes of a morphism of the
site is an isomorphism in one spelling of that morphism exactly when it is in the other. -/
theorem isIso_pullback_schemeHom_map_iff {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    {M N : ((BigFppfOver.toScheme B S hS).obj T).Modules} (φ : M ⟶ N) :
    IsIso ((Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
        (associatedBigEtaleSite B) g.left)).map φ) ↔
      IsIso ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).map φ) :=
  Iff.rfl

section Generic

attribute [local implicit_reducible] CartesianChartFamily.site BigFppfOver.siteObjectOver

variable (E E' : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]
  [hE' : E'.IsQuasicoherentOnSite] (u : E ⟶ E') (σ : E' ⟶ E) (hσ : σ ≫ u = 𝟙 E')
  (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)
  (hfree' : SheafOfModules.IsFiniteLocallyFreeOnSite E')

/-- On the chart `U_U ⟶ P_U` the hyperplane section of the chart bundle is invertible, for a
split datum `t₀ ≫ s₀ + u_U ≫ σ_U = 𝟙`, `s₀ ≫ u_U = 0` on the presenting chart. -/
theorem isIso_pullback_splitEpiComplementAtlasChartHom_hyperplane
    (s₀ : Scheme.unitModule (chartScheme (bundleBaseChart X)) ⟶
      chartBundleModule E (bundleBaseChart X))
    (t₀ : chartBundleModule E (bundleBaseChart X) ⟶
      Scheme.unitModule (chartScheme (bundleBaseChart X)))
    (hsplit : t₀ ≫ s₀ + chartModuleMap u (bundleBaseChart X) ≫
      chartModuleMap σ (bundleBaseChart X) = 𝟙 _)
    (hsu : s₀ ≫ chartModuleMap u (bundleBaseChart X) = 0) :
    IsIso ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map
        (splitEpiComplementAtlasChartHom E E' u σ hσ hfree hfree'))).map
      ((Scheme.Modules.pullback (chartBundleToChart E (bundleBaseChart X))).map s₀ ≫
        chartBundleTautological E (bundleBaseChart X))) := by
  have hf : Set.range ((BigFppfOver.toScheme B S hS).map
      (splitEpiComplementAtlasChartHom E E' u σ hσ hfree hfree')).base ⊆
      (Set.range (@Stacks.RelativeProj.projectiveBundleMapOfEpi _ _ _ _ _
        (chartModuleMap u (bundleBaseChart X)) (epi_chartModuleMap u σ hσ _)).base)ᶜ := by
    with_reducible exact range_splitEpiComplementAtlasChartHom_subset E E' u σ hσ hfree hfree'
  exact @Stacks.RelativeProj.isIso_pullback_map_hyperplane_of_range_subset
    _ _ _ _ _ (chartModuleMap u (bundleBaseChart X)) (epi_chartModuleMap u σ hσ _) s₀ t₀
    (chartModuleMap σ (bundleBaseChart X)) hsplit hsu _ _ hf

/-- A morphism `G(a ≫ H(g) ≫ t ≫ c)` with `a`, `c` isomorphisms is an isomorphism as soon as
`G(H(i⁻¹ ≫ g) ≫ t)` is one, for an isomorphism `i` out of the source of `g`. -/
theorem _root_.CategoryTheory.Functor.isIso_map_of_eq_comp_map_comp {C C' D : Type*} [Category C]
    [Category C'] [Category D] (G : C ⥤ D) (H : C' ⥤ C) {x₀ y₀ y₁ : C} {z₀ z₁ w : C'}
    (a : x₀ ≅ H.obj z₀) (i : z₀ ≅ z₁) (g : z₀ ⟶ w) (t : H.obj w ⟶ y₀) (c : y₀ ≅ y₁)
    (hm : IsIso (G.map (H.map (i.inv ≫ g) ≫ t))) (f : x₀ ⟶ y₁)
    (hf : f = a.hom ≫ H.map g ≫ t ≫ c.hom) : IsIso (G.map f) := by
  rw [hf, show G.map (a.hom ≫ H.map g ≫ t ≫ c.hom) =
      G.map a.hom ≫ G.map (H.map i.hom) ≫ G.map (H.map (i.inv ≫ g) ≫ t) ≫ G.map c.hom by
    simp only [← G.map_comp, Category.assoc, ← H.map_comp_assoc, Iso.hom_inv_id_assoc]]
  infer_instance

variable (σ₀ : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS X.1 X.2).O)) ⟶ E)
  (τ : E ⟶ SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS X.1 X.2).O)))
  (hsplit : τ ≫ σ₀ + u ≫ σ = 𝟙 E) (hσ₀u : σ₀ ≫ u = 0)

omit hE hE' in
include hsplit in
/-- The split datum on the presenting chart, with `𝒪_X` read as the structure sheaf of the
chart: `t₀ ≫ s₀ + u_U ≫ σ_U = 𝟙`. -/
theorem chartSplit_add_eq_id :
    (schemeReadingMap (chartToSpace B S hS X (bundleBaseChart X)) τ ≫
        (completionChartUnitIso (X := X)).hom) ≫
      ((completionChartUnitIso (X := X)).inv ≫
        schemeReadingMap (chartToSpace B S hS X (bundleBaseChart X)) σ₀) +
      chartModuleMap u (bundleBaseChart X) ≫ chartModuleMap σ (bundleBaseChart X) = 𝟙 _ := by
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact ((congrArg₂ (· + ·)
      (schemeReadingMap_comp (T := (SmallEtale.toOver B S hS X.1).obj (bundleBaseChart X))
        (chartToSpace B S hS X (bundleBaseChart X)) τ σ₀).symm
      (schemeReadingMap_comp (T := (SmallEtale.toOver B S hS X.1).obj (bundleBaseChart X))
        (chartToSpace B S hS X (bundleBaseChart X)) u σ).symm).trans
    (schemeReadingMap_add (T := (SmallEtale.toOver B S hS X.1).obj (bundleBaseChart X))
      (chartToSpace B S hS X (bundleBaseChart X)) _ _).symm).trans
    ((congrArg (schemeReadingMap (T := (SmallEtale.toOver B S hS X.1).obj (bundleBaseChart X))
      (chartToSpace B S hS X (bundleBaseChart X))) hsplit).trans
      (schemeReadingMap_id (T := (SmallEtale.toOver B S hS X.1).obj (bundleBaseChart X))
        (chartToSpace B S hS X (bundleBaseChart X))))

omit hE hE' in
include hσ₀u in
/-- `s₀ ≫ u_U = 0` on the presenting chart. -/
theorem chartSection_comp_eq_zero :
    ((completionChartUnitIso (X := X)).inv ≫
        schemeReadingMap (chartToSpace B S hS X (bundleBaseChart X)) σ₀) ≫
      chartModuleMap u (bundleBaseChart X) = 0 := by
  have h : schemeReadingMap (chartToSpace B S hS X (bundleBaseChart X)) σ₀ ≫
      chartModuleMap u (bundleBaseChart X) = 0 :=
    (schemeReadingMap_comp (T := (SmallEtale.toOver B S hS X.1).obj (bundleBaseChart X))
        (chartToSpace B S hS X (bundleBaseChart X)) σ₀ u).symm.trans
      ((congrArg (schemeReadingMap (T := (SmallEtale.toOver B S hS X.1).obj (bundleBaseChart X))
        (chartToSpace B S hS X (bundleBaseChart X))) hσ₀u).trans
        (schemeReadingMap_zero (T := (SmallEtale.toOver B S hS X.1).obj (bundleBaseChart X))
          (chartToSpace B S hS X (bundleBaseChart X))))
  rw [Category.assoc, h, comp_zero]

include hsplit hσ₀u in
/-- The hyperplane section of the reading of `σ₀` on the presenting chart bundle is invertible on
the chart `U_U ⟶ P_U`, with the chart morphism in the spelling of the comparisons of readings. -/
theorem isIso_pullback_schemeHom_splitEpiComplementAtlasChartHom_hyperplane :
    IsIso ((Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
      (associatedBigEtaleSite B)
        (splitEpiComplementAtlasChartHom E E' u σ hσ hfree hfree').left)).map
      ((Scheme.Modules.pullback (chartBundleToChart E (bundleBaseChart X))).map
          ((completionChartUnitIso (X := X)).inv ≫
            schemeReadingMap (chartToSpace B S hS X (bundleBaseChart X)) σ₀) ≫
        chartBundleTautological E (bundleBaseChart X))) :=
  (isIso_pullback_schemeHom_map_iff _ _).2
    (isIso_pullback_splitEpiComplementAtlasChartHom_hyperplane E E' u σ hσ hfree hfree'
      ((completionChartUnitIso (X := X)).inv ≫
        schemeReadingMap (chartToSpace B S hS X (bundleBaseChart X)) σ₀)
      (schemeReadingMap (chartToSpace B S hS X (bundleBaseChart X)) τ ≫
        (completionChartUnitIso (X := X)).hom)
      (by with_reducible exact chartSplit_add_eq_id E E' u σ σ₀ τ hsplit)
      (by with_reducible exact chartSection_comp_eq_zero E E' u σ₀ hσ₀u))

include hsplit hσ₀u in
/-- The reading on `P_U` of the hyperplane section of `σ₀`, pulled back to the chart
`U_U ⟶ P_U`, is invertible. -/
theorem isIso_pullback_schemeHom_schemeReadingMap_projectiveBundleSectionHom :
    IsIso ((Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
      (associatedBigEtaleSite B)
        (splitEpiComplementAtlasChartHom E E' u σ hσ hfree hfree').left)).map
      ((SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj (projectiveBundleChartPresentation E hfree).U)
          (projectiveBundleChartPresentation E hfree).U.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS
          (projectiveBundleChartPresentation E hfree).U).inverse.map
          ((modulePullback B S hS (projectiveBundleAtlas E hfree)).map
            (projectiveBundleSectionHom E hfree σ₀))))) := by
  have hm := isIso_pullback_schemeHom_splitEpiComplementAtlasChartHom_hyperplane E E' u σ hσ hfree
    hfree' σ₀ τ hsplit hσ₀u
  obtain ⟨A, C, hAC⟩ := exists_representedZariski_map_projectiveBundleAtlas_sectionHom E hfree σ₀
  rw [projectiveBundleSectionHom, hAC]
  exact Functor.isIso_map_of_eq_comp_map_comp _
    (Scheme.Modules.pullback (chartBundleToChart E (bundleBaseChart X))) A
    (completionChartUnitIso (X := X))
    (schemeReadingMap (chartToSpace B S hS X (bundleBaseChart X)) σ₀)
    (chartBundleTautological E (bundleBaseChart X)) C hm _ rfl

include hsplit hσ₀u in
/-- The hyperplane section of `σ₀` is invertible on the chart `U_U ⟶ U ⟶ 𝐏(ℰ)` of the
complement of `𝐏(ℰ')`, for a split short exact sequence `0 ⟶ 𝒪_X ⟶ ℰ ⟶ ℰ' ⟶ 0`. -/
theorem isIso_modulePullback_splitEpiComplementAtlasChart_sectionHom :
    IsIso ((modulePullback B S hS
      ((ObjectProperty.homMk (splitEpiComplementAtlasChartToComplement E E' u σ hσ hfree hfree') :
          representedAlgebraicSpace B S hS (splitEpiComplementAtlasChart E E' u σ hσ hfree hfree') ⟶
            projectiveBundleSplitEpiComplement E E' u σ hσ hfree hfree') ≫
        projectiveBundleSplitEpiComplementHom E E' u σ hσ hfree hfree')).map
      (projectiveBundleSectionHom E hfree σ₀)) := by
  have hw : (ObjectProperty.homMk
        (splitEpiComplementAtlasChartToComplement E E' u σ hσ hfree hfree') :
        representedAlgebraicSpace B S hS (splitEpiComplementAtlasChart E E' u σ hσ hfree hfree') ⟶
          projectiveBundleSplitEpiComplement E E' u σ hσ hfree hfree') ≫
        projectiveBundleSplitEpiComplementHom E E' u σ hσ hfree hfree' =
      representedSpaceMap B S hS (splitEpiComplementAtlasChartHom E E' u σ hσ hfree hfree') ≫
        projectiveBundleAtlas E hfree :=
    ObjectProperty.hom_ext _ (isPullback_splitEpiComplementAtlasChart E E' u σ hσ hfree hfree').w
  refine isIso_modulePullback_map_of_eq hw _ ?_
  refine isIso_of_isIso_representedZariski_map
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _
      (SheafOfModules.isQuasicoherentOnSite_unit _))
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _
      (projectiveBundleTwist E hfree).property) _ ?_
  have nat := schemeReadingPullbackIso_hom_naturality
    (splitEpiComplementAtlasChartHom E E' u σ hσ hfree hfree') (ψ := projectiveBundleAtlas E hfree)
    rfl (SheafOfModules.isQuasicoherentOnSite_unit _) (projectiveBundleTwist E hfree).property
    (projectiveBundleSectionHom E hfree σ₀)
  have := isIso_pullback_schemeHom_schemeReadingMap_projectiveBundleSectionHom E E' u σ hσ hfree
    hfree' σ₀ τ hsplit hσ₀u
  exact IsIso.of_isIso_fac_left nat.symm

end Generic

section Completion

attribute [local instance] HasBinaryBiproducts.of_hasBinaryProducts

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

variable (E : Modules.{u, u} B S hS X.1 X.2) {r : ℕ}
    (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) E r)

/-- On the chart `U_U ⟶ U ⟶ P` of the affine part of the projective completion, the section `s`
of `(0, 1)` is invertible. -/
theorem isIso_modulePullback_projectiveCompletionAffinePartChart_sectionHom :
    IsIso ((modulePullback B S hS
      (projectiveCompletionAffinePartChartToAffinePart E hr ≫
        projectiveCompletionAffinePartHom E hr)).map (projectiveCompletionSectionHom E hr)) := by
  have hsplit : addUnitSnd X.2 E ≫ addUnitInr X.2 E + biprod.fst ≫ biprod.inl =
      𝟙 (addUnit X.2 E) :=
    (add_comm _ _).trans biprod.total
  rw [projectiveCompletionSectionHom_eq]
  have key := @isIso_modulePullback_splitEpiComplementAtlasChart_sectionHom B S hS X
    (addUnit X.2 E) E
    (isQuasicoherentOnSite_addUnit hr) (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
    biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
    hr.isFiniteLocallyFreeOnSite (addUnitInr X.2 E) (addUnitSnd X.2 E) hsplit biprod.inr_fst
  with_reducible exact key

/-- The section `s` of `(0, 1)` is invertible on the affine part `U = P ∖ i(𝐏(ℰ))` of the
projective completion: `ι^*s : 𝒪_U ⟶ ι^*𝒪_P(1)` is an isomorphism. -/
theorem isIso_modulePullback_projectiveCompletionAffinePartHom_projectiveCompletionSectionHom :
    IsIso ((modulePullback B S hS (projectiveCompletionAffinePartHom E hr)).map
      (projectiveCompletionSectionHom E hr)) :=
  isIso_modulePullback_projectiveCompletionAffinePartHom_sectionHom E hr
    (isIso_modulePullback_projectiveCompletionAffinePartChart_sectionHom E hr)

end Completion

end AlgebraicGeometry.Space

end
