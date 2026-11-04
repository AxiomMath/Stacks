module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.ModuleIsoFlatness
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Limits.RelativeApproximation.FlatDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteNoetherianApproximation.KernelPairDescend
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteNoetherianApproximation.KernelPairLift
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteNoetherianApproximation.KernelPairTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteNoetherianApproximation.TerminalSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescentBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.DiagonalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleAtlasCriterionUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartSystemConvention
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.RelativeDimensionDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianApproximationFromPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFormallySmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonoCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparated
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeComposite

/-!
# Absolute Noetherian approximation: the limit of the glued system is the given space

This is the end of the proof of Stacks 07SU. Given the systems `V_j ⊇ W_j ⟶ U_j` and the glued
relations `R_j = V_j ⊔_{W_j} W_j ×_{U_j} W_j`, the quotients `X_j = V_j / R_j` (Stacks 02WW) form
an inverse system with affine transitions whose stages are quasi-separated and of finite type
over `ℤ`, and its limit is `X`. The source proves the last claim by identifying the kernel pair of
`V ⟶ lim X_j` with `V ×_X V` and applying Stacks 0262; here the two kernel pairs are compared on
points: a pair of points of `V` is identified in `X` exactly when it is related in every `R_j`
(`exists_lift_gluedRelation_of_kernelPair` and `comp_eq_comp_of_forall_lift_gluedRelation`),
which is exactly when it is identified in `lim X_j` (Stacks 02WV). The limit is an algebraic space
because `V ⟶ lim X_j` is a base change of the quotient chart `V_j ⟶ X_j`, and the new system
satisfies the chapter's convention because it has the chart system `V_j` with limit `V`.

## Main results

* `AlgebraicGeometry.Space.hasConventionalNoetherianApproximation_of_relationSystem`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open Stacks.Groupoids

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}

/-- Two maps `T ⟶ X`, `T ⟶ Y` whose Yoneda images agree over the cospan of a pullback square of
representables factor through the pullback object. -/
private theorem exists_comp_eq_of_isPullback_yoneda {C : Type*} [Category C]
    {G : Cᵒᵖ ⥤ Type _} {K X Y T : C} {k₁ : K ⟶ X} {k₂ : K ⟶ Y}
    {f : yoneda.obj X ⟶ G} {g : yoneda.obj Y ⟶ G}
    (hk : IsPullback (yoneda.map k₁) (yoneda.map k₂) f g) (x : T ⟶ X) (y : T ⟶ Y)
    (h : yoneda.map x ≫ f = yoneda.map y ≫ g) : ∃ e : T ⟶ K, e ≫ k₁ = x ∧ e ≫ k₂ = y :=
  ⟨yoneda.preimage (hk.lift _ _ h), yoneda.map_injective (by
    rw [Functor.map_comp, Functor.map_preimage, hk.lift_fst]), yoneda.map_injective (by
    rw [Functor.map_comp, Functor.map_preimage, hk.lift_snd])⟩

/-- Two points of `V` are identified by a map `h_V ⟶ lim_j V_j / R_j` lying over the quotient
charts exactly when they are related in every `R_j` (Stacks 02WV). -/
private theorem yoneda_map_comp_limit_quotientSystem_eq_iff
    {J : Type u} [Preorder J] {Vs R : Jᵒᵖ ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ} (s t : R ⟶ Vs)
    [∀ j, IsEtaleEquivalenceRelation (relation B (⊤_ Scheme.{u}) hZ (s.app j) (t.app j))]
    {V : BigFppfOver B (⊤_ Scheme.{u}) hZ} (vπ : (Functor.const Jᵒᵖ).obj V ⟶ Vs)
    (f' : yoneda.obj V ⟶ limit (relationQuotientSystem B (⊤_ Scheme.{u}) hZ s t))
    (hf'π : ∀ j, f' ≫ limit.π _ j =
      yoneda.map (vπ.app j) ≫ (quotientSystemπ B (⊤_ Scheme.{u}) hZ s t).app j)
    {T : BigFppfOver B (⊤_ Scheme.{u}) hZ} (x y : T ⟶ V) :
    yoneda.map x ≫ f' = yoneda.map y ≫ f' ↔
      ∀ j, ∃ r : T ⟶ R.obj j, r ≫ s.app j = x ≫ vπ.app j ∧ r ≫ t.app j = y ≫ vπ.app j := by
  constructor
  · intro hxy j
    have hq := quotientMap_isPullback B (⊤_ Scheme.{u}) hZ (s.app j) (t.app j)
    have hw : yoneda.map (y ≫ vπ.app j) ≫ (quotientSystemπ B (⊤_ Scheme.{u}) hZ s t).app j =
        yoneda.map (x ≫ vπ.app j) ≫ (quotientSystemπ B (⊤_ Scheme.{u}) hZ s t).app j := by
      have := congrArg (· ≫ limit.π (relationQuotientSystem B (⊤_ Scheme.{u}) hZ s t) j) hxy
      simp only [Category.assoc, hf'π] at this
      simpa only [Functor.map_comp, Category.assoc] using this.symm
    obtain ⟨r, hrt, hrs⟩ := exists_comp_eq_of_isPullback_yoneda hq _ _ hw
    exact ⟨r, hrs, hrt⟩
  · intro h
    refine limit.hom_ext fun j => ?_
    obtain ⟨r, hrs, hrt⟩ := h j
    have hq := quotientMap_isPullback B (⊤_ Scheme.{u}) hZ (s.app j) (t.app j)
    simp only [Category.assoc, hf'π]
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← hrs, ← hrt, Functor.map_comp_assoc,
      Functor.map_comp_assoc]
    exact congrArg (yoneda.map r ≫ ·) hq.w.symm

/-- A map `h_V ⟶ lim_j V_j / R_j` lying over the quotient charts, where `V = lim_j V_j`, has
every base-change-stable property of a quotient chart `h_{V_j} ⟶ V_j / R_j`. -/
private theorem presheaf_of_comp_limit_π_eq_quotientSystemπ
    {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)]
    {Vs R : Jᵒᵖ ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ} (s t : R ⟶ Vs)
    [∀ j, IsEtaleEquivalenceRelation (relation B (⊤_ Scheme.{u}) hZ (s.app j) (t.app j))]
    (hcartR : ∀ {j j' : Jᵒᵖ} (e : j ⟶ j'), IsPullback (R.map e) (s.app j) (s.app j') (Vs.map e))
    {V : BigFppfOver B (⊤_ Scheme.{u}) hZ} (vπ : (Functor.const Jᵒᵖ).obj V ⟶ Vs)
    (hvπ : IsLimit ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).mapCone (Cone.mk V vπ)))
    (f' : yoneda.obj V ⟶ limit (relationQuotientSystem B (⊤_ Scheme.{u}) hZ s t))
    (hf'π : ∀ j, f' ≫ limit.π _ j =
      yoneda.map (vπ.app j) ≫ (quotientSystemπ B (⊤_ Scheme.{u}) hZ s t).app j)
    (P : MorphismProperty ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)) [P.RespectsIso]
    [P.IsStableUnderBaseChange] (j₀ : Jᵒᵖ)
    (hP : P ((quotientSystemπ B (⊤_ Scheme.{u}) hZ s t).app j₀)) : P f' := by
  have hVlim : IsLimit (yoneda.mapCone (Cone.mk V vπ)) :=
    BigFppfOver.isLimitYonedaMapConeOfIsLimitToScheme hvπ
  let ℓ : yoneda.obj V ⟶ limit (Vs ⋙ yoneda) :=
    limit.lift (Vs ⋙ yoneda) (yoneda.mapCone (Cone.mk V vπ))
  have hℓ : IsIso ℓ := by
    have : ℓ = (hVlim.conePointUniqueUpToIso (limit.isLimit (Vs ⋙ yoneda))).hom := by
      refine limit.hom_ext fun j => ?_
      simp [ℓ]
    rw [this]
    infer_instance
  have hf'eq : f' = ℓ ≫ limMap (quotientSystemπ B (⊤_ Scheme.{u}) hZ s t) := by
    refine limit.hom_ext fun j => ?_
    rw [hf'π, Category.assoc, limMap_π, ← Category.assoc, limit.lift_π]
    rfl
  rw [hf'eq]
  exact MorphismProperty.RespectsIso.precomp _ ℓ _ (P.of_isPullback
    (isPullback_limit_π_limMap_quotientSystemπ B (⊤_ Scheme.{u}) hZ s t hcartR j₀) hP)

/-- If a surjective étale atlas `h_V ⟶ X` and a map `h_V ⟶ lim_j V_j / R_j` lying over the
quotient charts have the same kernel pair, then `X` has a conventional Noetherian
approximation (Stacks 0262). -/
private theorem hasConventionalNoetherianApproximation_of_kernelPair_quotientSystem
    {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    {V : BigFppfOver B (⊤_ Scheme.{u}) hZ} (f : yoneda.obj V ⟶ X)
    (hfs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf f)
    (hfe' : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf f)
    {J : Type u} [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)]
    {Vs R : Jᵒᵖ ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ} (vπ : (Functor.const Jᵒᵖ).obj V ⟶ Vs)
    (hvπ : IsLimit ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).mapCone (Cone.mk V vπ)))
    (hVsc : ∀ j, CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (Vs.obj j)))
    (hVsft : ∀ j, LocallyOfFiniteType
      (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (Vs.obj j))))
    (hVsqs : ∀ j, QuasiSeparatedSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (Vs.obj j)))
    (hVsaff : ∀ {j j' : Jᵒᵖ} (e : j ⟶ j'),
      _root_.AlgebraicGeometry.IsAffineHom
        ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (Vs.map e)))
    (s t : R ⟶ Vs)
    (hcartR : ∀ {j j' : Jᵒᵖ} (e : j ⟶ j'), IsPullback (R.map e) (s.app j) (s.app j') (Vs.map e))
    [∀ j, IsEtaleEquivalenceRelation (relation B (⊤_ Scheme.{u}) hZ (s.app j) (t.app j))]
    (hsqc : ∀ j, QuasiCompact ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (s.app j)))
    (f' : yoneda.obj V ⟶ limit (relationQuotientSystem B (⊤_ Scheme.{u}) hZ s t))
    (hf'π : ∀ j, f' ≫ limit.π _ j =
      yoneda.map (vπ.app j) ≫ (quotientSystemπ B (⊤_ Scheme.{u}) hZ s t).app j)
    {K : BigFppfOver B (⊤_ Scheme.{u}) hZ} {k₁ k₂ : K ⟶ V}
    (hk : IsPullback (yoneda.map k₁) (yoneda.map k₂) f f)
    (hk' : IsPullback (yoneda.map k₁) (yoneda.map k₂) f' f') :
    HasConventionalNoetherianApproximation B hZ X := by
  obtain ⟨j₀⟩ : Nonempty J := inferInstance
  let PS := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)
  let PE := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)
  have : PS.presheaf.IsStableUnderBaseChange := PS.relative_isStableUnderBaseChange (F := yoneda)
  have : PE.presheaf.IsStableUnderBaseChange := PE.relative_isStableUnderBaseChange (F := yoneda)
  -- `f'` is a base change of a quotient chart, hence surjective and étale
  have hs' : PS.presheaf f' := presheaf_of_comp_limit_π_eq_quotientSystemπ s t hcartR vπ hvπ f'
    hf'π PS.presheaf (op j₀) (quotientSystemπ_app_surjective B (⊤_ Scheme.{u}) hZ s t (op j₀))
  have he' : PE.presheaf f' := presheaf_of_comp_limit_π_eq_quotientSystemπ s t hcartR vπ hvπ f'
    hf'π PE.presheaf (op j₀) (quotientSystemπ_app_etale B (⊤_ Scheme.{u}) hZ s t (op j₀))
  -- the limit is an algebraic space, presented by the same relation as `X`
  have hL : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ
      (limit (relationQuotientSystem B (⊤_ Scheme.{u}) hZ s t)) :=
    isAlgebraicSpace_of_surjective_etale_atlas B (⊤_ Scheme.{u}) hZ
      (isSheaf_limit B (⊤_ Scheme.{u}) hZ _ fun j =>
        (isAlgebraicSpace_quotientSystem_obj B (⊤_ Scheme.{u}) hZ s t j).isSheaf) V f' hs' he'
  obtain ⟨e, -⟩ := exists_iso_of_common_presentation B (⊤_ Scheme.{u}) hZ hk hk' hX hL
    hfs hfe' hs' he'
  -- the limit is its own Noetherian approximation
  refine ⟨(noetherianApproximationLimit B (⊤_ Scheme.{u}) hZ hZ
    (relationQuotientSystem B (⊤_ Scheme.{u}) hZ s t)
    (isAlgebraicSpace_quotientSystem_obj B (⊤_ Scheme.{u}) hZ s t)
    (fun e => isAffineHom_quotientSystem_map B (⊤_ Scheme.{u}) hZ s t e (hcartR e) (hVsaff e))
    (fun j => isAbsolutelyQuasiSeparated_quotientSystem_obj B (⊤_ Scheme.{u}) hZ hZ s t j
      (hVsqs j) (hsqc j))
    (fun j => isFiniteType_viewOverIntegers_quotientSystem_obj B (⊤_ Scheme.{u}) hZ hZ s t j
      (hVsc j) (hVsft j))).ofIso e.symm, ?_⟩
  exact siteContainsBaseChangeLimits_of_chartSystem
    (relationQuotientSystem B (⊤_ Scheme.{u}) hZ s t) Vs (quotientSystemπ B (⊤_ Scheme.{u}) hZ s t)
    (quotientSystemπ_app_surjective B (⊤_ Scheme.{u}) hZ s t)
    (quotientSystemπ_app_etale B (⊤_ Scheme.{u}) hZ s t)
    (fun e => isPullback_quotientSystemπ B (⊤_ Scheme.{u}) hZ s t e (hcartR e))
    _ hvπ V.left.property

/-- **The limit of the glued system is `X`.** In the situation of the gluing step of the proof of
Stacks 07SU — an étale neighbourhood `f : V ⟶ X` which is an isomorphism over the closed
complement `Z` of the open `U`, a system `U_j` with limit `U`, a system `V_j` with limit `V`
(as schemes) containing compatible opens `W_j` étale over `U_j` with limit `W = f⁻¹U`, and the
glued étale equivalence relations `R_j ⇉ V_j` — the quotients `V_j / R_j` form a Noetherian
approximation of `X` satisfying the chapter's convention. -/
theorem hasConventionalNoetherianApproximation_of_relationSystem
    {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    (U : Subfunctor X) (hU : IsOpenSubspace B (⊤_ Scheme.{u}) hZ U)
    (Z : Subfunctor X) (hZc : IsClosedSubspace B (⊤_ Scheme.{u}) hZ Z)
    (hcover : ∀ x : points B (⊤_ Scheme.{u}) hZ X,
      x ∈ Set.range (pointsMap B (⊤_ Scheme.{u}) hZ U.toFunctor U.ι) ∨
        x ∈ Set.range (pointsMap B (⊤_ Scheme.{u}) hZ Z.toFunctor Z.ι))
    (V : BigFppfOver B (⊤_ Scheme.{u}) hZ) (f : yoneda.obj V ⟶ X)
    (hfs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf f)
    (hfe' : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf f)
    (hfe : IsEtale B (⊤_ Scheme.{u}) hZ f) (hfZ : IsIso (pullback.fst Z.ι f))
    {J : Type u} [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)]
    (D : Jᵒᵖ ⥤ (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
    (hD : ∀ j, IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (D.obj j))
    (uπ : (Functor.const Jᵒᵖ).obj U.toFunctor ⟶ D) (huπ : IsLimit (Cone.mk _ uπ))
    (Vs Ws P R : Jᵒᵖ ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ) (vπ : (Functor.const Jᵒᵖ).obj V ⟶ Vs)
    (hvπ : IsLimit ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).mapCone (Cone.mk V vπ)))
    (hVsc : ∀ j, CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (Vs.obj j)))
    (hVsft : ∀ j, LocallyOfFiniteType
      (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (Vs.obj j))))
    (hVsqs : ∀ j, QuasiSeparatedSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (Vs.obj j)))
    (hVsaff : ∀ {j j' : Jᵒᵖ} (e : j ⟶ j'),
      _root_.AlgebraicGeometry.IsAffineHom
        ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (Vs.map e)))
    (ι : Ws ⟶ Vs)
    (hι : ∀ j, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (ι.app j)))
    (g : Ws ⋙ yoneda ⟶ D)
    (W : BigFppfOver B (⊤_ Scheme.{u}) hZ) (ιW : W ⟶ V) (gW : yoneda.obj W ⟶ U.toFunctor)
    (hW : IsPullback (yoneda.map ιW) gW f U.ι)
    (wπ : (Functor.const Jᵒᵖ).obj W ⟶ Ws)
    (hwcart : ∀ j, IsPullback (wπ.app j) ιW (ι.app j) (vπ.app j))
    (hwg : ∀ j, yoneda.map (wπ.app j) ≫ g.app j = gW ≫ uπ.app j)
    (p₁ p₂ : P ⟶ Ws)
    (hP : ∀ j, IsPullback (yoneda.map (p₁.app j)) (yoneda.map (p₂.app j)) (g.app j) (g.app j))
    (δ : Ws ⟶ P)
    (hδ : ∀ j, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (δ.app j)))
    (a : Vs ⟶ R) (b : P ⟶ R) (s t : R ⟶ Vs)
    (hR : ∀ j, IsPushout ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (ι.app j))
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (δ.app j))
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (a.app j))
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (b.app j)))
    (has : ∀ j, a.app j ≫ s.app j = 𝟙 _) (hat : ∀ j, a.app j ≫ t.app j = 𝟙 _)
    (hbs : ∀ j, b.app j ≫ s.app j = p₁.app j ≫ ι.app j)
    (hbt : ∀ j, b.app j ≫ t.app j = p₂.app j ≫ ι.app j)
    (hcartR : ∀ {j j' : Jᵒᵖ} (e : j ⟶ j'), IsPullback (R.map e) (s.app j) (s.app j') (Vs.map e))
    (hjm : ∀ j, JointlyMono₂ ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (t.app j))
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (s.app j)))
    [∀ j, IsEtaleEquivalenceRelation (relation B (⊤_ Scheme.{u}) hZ (s.app j) (t.app j))]
    (hsqc : ∀ j, QuasiCompact ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (s.app j))) :
    HasConventionalNoetherianApproximation B hZ X := by
  -- the stages and their quotient charts
  set Xs := relationQuotientSystem B (⊤_ Scheme.{u}) hZ s t
  set π := quotientSystemπ B (⊤_ Scheme.{u}) hZ s t
  -- the map from `V` to the limit of the stages
  let f' : yoneda.obj V ⟶ limit Xs :=
    limit.lift Xs ⟨yoneda.obj V, (yoneda.mapCone (Cone.mk V vπ)).π ≫ π⟩
  have hf'π : ∀ j, f' ≫ limit.π Xs j = yoneda.map (vπ.app j) ≫ π.app j := fun j =>
    limit.lift_π _ j
  -- the kernel pair of `f`
  let K := atlasKernelPair B (⊤_ Scheme.{u}) hZ f hX.diagonal_representable
  -- the points identified by `f` are those related in every stage
  have hiff : ∀ (T : BigFppfOver B (⊤_ Scheme.{u}) hZ) (x y : T ⟶ V),
      yoneda.map x ≫ f = yoneda.map y ≫ f ↔
        ∀ j, ∃ r : T ⟶ R.obj j, r ≫ s.app j = x ≫ vπ.app j ∧ r ≫ t.app j = y ≫ vπ.app j := by
    intro T x y
    constructor
    · intro hxy j
      obtain ⟨rE, hrEt, hrEs⟩ := exists_lift_gluedRelation_of_kernelPair hX U hU Z hZc hcover V f
        hfe hfZ W ιW gW hW (ι.app j) (g.app j) (p₁.app j) (p₂.app j) (hP j) (a.app j) (b.app j)
        (s.app j) (t.app j) (has j) (hat j) (hbs j) (hbt j) (vπ.app j) (wπ.app j) (uπ.app j)
        (hwcart j).w (hwg j) K.R K.s K.t K.kernelPair
      obtain ⟨e, he₁, he₂⟩ := exists_comp_eq_of_isPullback_yoneda K.kernelPair x y hxy
      refine ⟨e ≫ rE, ?_, ?_⟩
      · rw [Category.assoc, hrEs, ← Category.assoc, he₁]
      · rw [Category.assoc, hrEt, ← Category.assoc, he₂]
    · intro h
      exact comp_eq_comp_of_forall_lift_gluedRelation hX U V f W ιW gW hW D hD uπ huπ Vs Ws P R ι hι
        g p₁ p₂ hP δ hδ a b s t hR has hat hbs hbt hcartR hjm vπ hvπ wπ hwcart hwg T x y h
  -- the points identified by `f'` are those related in every stage
  have hK' : IsPullback (yoneda.map K.s) (yoneda.map K.t) f' f' :=
    isPullback_yoneda_of_isPullback_of_forall_iff K.s K.t f f' K.kernelPair fun T x y =>
      (hiff T x y).trans (yoneda_map_comp_limit_quotientSystem_eq_iff s t vπ f' hf'π x y).symm
  exact hasConventionalNoetherianApproximation_of_kernelPair_quotientSystem hX f hfs hfe' vπ hvπ
    hVsc hVsft hVsqs hVsaff s t hcartR hsqc f' hf'π K.kernelPair hK'

end AlgebraicGeometry.Space

end
