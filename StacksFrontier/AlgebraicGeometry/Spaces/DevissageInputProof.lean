module

public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceContainmentNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.ProjectiveSectionsShrinkBasicOpen
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPullbackStability
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsProjectiveOfChartPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryChartAlongBaseChangeFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityEtaleChartSpecialization
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsHenselianLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapTargetBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubobjectLift
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# The dévissage of Stacks 0CWC

`AlgebraicGeometry.Space.ModuleMapSituation.DevissageInput` — étale locally on the base and over
an affine, a flat chart with affine source capturing the relative assassin, along which the
sections of the target module are projective over the functions on the base — is proved here
from the hypotheses of Stacks 0CWC.

## The argument

Fix `y ∈ |Y|`.

1. `AlgebraicGeometry.Space.exists_elementary_chart_projective_sections_covering_baseChange_fibre`
   (Stacks 0CVZ in its pointed elementary form) gives an étale `A ⟶ Y` from an affine scheme with
   a point `a₀` over `y`, and an étale chart `Y' ⟶ X` from an affine scheme with `h : Y' ⟶ A`
   over `f`, along which the sections of `𝒢` are projective over `Γ(A, 𝒪_A)`, and whose induced
   chart `s : Y' ⟶ X_A = X ×_Y A` covers the fibre of `X_A` over `a₀`.
2. Purity above `y`
   (`AlgebraicGeometry.Space.exists_specializes_fibre_of_isPureAbove_of_isPullback`) specializes
   every point of `Ass_{X_A/A}(𝒢_A)` over a generalization of `a₀` into that fibre,
   hence into the open image of `s`.
3. The locus of `a ∈ A` over which `Ass_{X_A/A}(𝒢_A)` lies in the image of `s` is locally
   constructible by Stacks 0CVV, and contains every generalization of `a₀` by step 2, so it is a
   neighbourhood of `a₀` by Morphisms 05LW.  It contains a basic open `D(t) ∋ a₀`.
4. Restricting `A` to `D(t)` and `Y'` to `D(h^♯ t)` keeps projectivity of the sections
   (`AlgebraicGeometry.projective_sections_pullback_basicOpen`), and the relative assassin of the
   restricted base change lands in the restricted chart: it maps into the relative assassin over
   `A` by part (1) of Stacks 0CV2, and points of `X_{D(t)}` are determined by their images in
   `X_A` because `D(t) ⟶ A` is an open immersion
   (`AlgebraicGeometry.Space.eq_of_pointsMap_eq_of_isPullback_of_isIso_residueFieldMap`).

Flatness of `𝒢` is consumed by step 1, finite presentation of `f` and of `𝒢` by steps 1 and 3,
and purity by step 2.

## References

* [Stacks Project, Tag 0CWC](https://stacks.math.columbia.edu/tag/0CWC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The part of the image of a chart `s` from an affine scheme lying over `h : Y' ⟶ A` along
`π` which lies over a quasi-compact open of the affine scheme `A` is quasi-compact. -/
private theorem isCompact_range_pointsMap_inter_preimage
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Y' A : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Y')]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj A)]
    (s : yoneda.obj Y' ⟶ F) (π : F ⟶ yoneda.obj A) (h : Y' ⟶ A) (hs : s ≫ π = yoneda.map h)
    (W : ((BigFppfOver.toScheme B S hS).obj A).Opens)
    (hW : IsCompact (W : Set ((BigFppfOver.toScheme B S hS).obj A))) :
    IsCompact (Set.range (pointsMap B S hS _ s) ∩
      (fun x => pointsToScheme B S hS A (pointsMap B S hS _ π x)) ⁻¹'
        (W : Set ((BigFppfOver.toScheme B S hS).obj A))) := by
  have hset : Set.range (pointsMap B S hS _ s) ∩
      (fun x => pointsToScheme B S hS A (pointsMap B S hS _ π x)) ⁻¹'
        (W : Set ((BigFppfOver.toScheme B S hS).obj A)) =
      pointsMap B S hS _ s '' ((schemePointsHomeomorph B S hS Y') ⁻¹'
        (((BigFppfOver.toScheme B S hS).map h) ⁻¹ᵁ W :
          Set ((BigFppfOver.toScheme B S hS).obj Y'))) := by
    ext x
    constructor
    · rintro ⟨⟨z, rfl⟩, hz⟩
      refine ⟨z, ?_, rfl⟩
      show (BigFppfOver.toScheme B S hS).map h (pointsToScheme B S hS Y' z) ∈ W
      rwa [← pointsToScheme_pointsMap_yoneda, ← hs, pointsMap_comp_apply]
    · rintro ⟨z, hz, rfl⟩
      refine ⟨⟨z, rfl⟩, ?_⟩
      show pointsToScheme B S hS A (pointsMap B S hS _ π (pointsMap B S hS _ s z)) ∈ W
      rwa [← pointsMap_comp_apply, hs, pointsToScheme_pointsMap_yoneda]
  rw [hset]
  exact (((schemePointsHomeomorph B S hS Y').isCompact_preimage).2
    (((BigFppfOver.toScheme B S hS).map h).isCompact_preimage hW)).image
    (continuous_pointsMap B S hS s)

namespace ModuleMapSituation

/-- **The dévissage of Stacks 0CWC.**  A situation of Stacks 083F whose morphism is of finite
presentation and whose target module is of finite presentation, flat over the base and pure
relative to it has, étale locally on its base and over an affine, a flat chart with affine source
capturing the relative assassin, along which the sections of the target module are projective
over the functions on the base.  See the module docstring for the argument. -/
theorem hasAffineFlatChartEtaleLocallyOnBase_of_isPureRelative
    (D : ModuleMapSituation.{u, u} B S hS) (hfp : IsFinitePresentation B S hS D.f.hom)
    (hGfp : SheafOfModules.IsFinitePresentationOnSite D.G)
    (hflat : IsFlatOver B S hS D.X.2 D.f.hom D.G)
    (hft : IsFiniteType B S hS D.f.hom) (hdec : IsDecent B S hS D.f.hom)
    (hGft : SheafOfModules.IsFiniteTypeOnSite D.G)
    (hpure : ∀ y : points B S hS D.Y.1,
      IsPureRelative (D.targetPrePureSituation hft hdec hGft y)) :
    D.HasAffineFlatChartEtaleLocallyOnBase := by
  classical
  intro y
  obtain ⟨V₀, b₀, U, A, Y', q, r, h, a₀, hb₀E, hqE, hres, hya, hAaff, hY'aff, hrE, hsq, hcov,
    hproj⟩ := exists_elementary_chart_projective_sections_covering_baseChange_fibre B S hS
      D.X.2 D.Y.2 D.f.hom D.G y hfp D.quasicoherent_G hGfp hflat
  -- The base change `X_A = X ×_Y A`.
  let bA : schemeSpace A ⟶ D.Y := ObjectProperty.homMk (yoneda.map q ≫ b₀)
  have hbAE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map q ≫ b₀) :=
    etale_comp_of_scheme B S hS q b₀ hqE hb₀E
  let pX := D.baseChangeTargetProjection bA
  let πA := D.baseChangeTargetMorphism bA
  let πAh : (D.baseChangeTargetSpace bA).obj ⟶ yoneda.obj A :=
    pullback.snd D.f.hom (yoneda.map q ≫ b₀)
  have sqA : IsPullback pX.hom πAh D.f.hom (yoneda.map q ≫ b₀) :=
    IsPullback.of_hasPullback D.f.hom (yoneda.map q ≫ b₀)
  have hpXE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf pX.hom :=
    presheaf_of_isPullback B S hS sqA.flip hbAE
  -- The chart `s : Y' ⟶ X_A` and its open image.
  let sA : yoneda.obj Y' ⟶ (D.baseChangeTargetSpace bA).obj :=
    pullback.lift (yoneda.map r ≫ U.obj.hom) (yoneda.map h) hsq
  have hsA₁ : sA ≫ pX.hom = yoneda.map r ≫ U.obj.hom := pullback.lift_fst _ _ _
  have hsA₂ : sA ≫ πAh = yoneda.map h := pullback.lift_snd _ _ _
  have hrUE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map r ≫ U.obj.hom) :=
    etale_comp_of_scheme B S hS r U.obj.hom hrE U.property
  have hsAE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf sA :=
    presheaf_etale_of_postcomp B S hS hpXE hrUE hsA₁
  have hO : IsOpen (Set.range (pointsMap B S hS _ sA)) :=
    isOpen_range_pointsMap_of_isEtale B S hS sA (isAlgebraicSpace_yoneda B S hS Y')
      (D.baseChangeTargetSpace bA).2 ((isEtale_iff_presheaf_of_yoneda B S hS sA).2 hsAE)
  -- Step 2: purity puts the relative assassin over generalizations of `a₀` into the chart.
  have hstep2 : ∀ ξ ∈ relativeWeaklyAssociatedPoints B S hS πA
      ((modulePullback B S hS pX).obj D.G),
      pointsToScheme B S hS A (pointsMap B S hS _ πAh ξ) ⤳ a₀ →
      ξ ∈ Set.range (pointsMap B S hS _ sA) := by
    intro ξ hξ hgen
    obtain ⟨θ, hξθ, hθ⟩ := exists_specializes_fibre_of_isPureAbove_of_isPullback
      (D.targetPrePureSituation hft hdec hGft y) (hpure y y) A (yoneda.map q ≫ b₀)
      (isEtale_of_presheaf_etale B S hS hbAE) ((pointsEquivScheme B S hS A).symm a₀) hya
      (p := pX) (q := πA) sqA hξ
      (by
        show pointsToScheme B S hS A (pointsMap B S hS _ πAh ξ) ⤳ _
        rw [show pointsToScheme B S hS A ((pointsEquivScheme B S hS A).symm a₀) = a₀ from
          (pointsEquivScheme B S hS A).apply_symm_apply a₀]
        exact hgen)
    refine hξθ.mem_open hO (hcov sqA sA hsA₁ hsA₂ θ ?_)
    rw [show pointsMap B S hS _ πAh θ = (pointsEquivScheme B S hS A).symm a₀ from hθ]
    exact (pointsEquivScheme B S hS A).apply_symm_apply a₀
  -- Step 3: the containment locus is a neighbourhood of `a₀`.
  set E := relativeAssassinContainmentLocus B S hS A πA ((modulePullback B S hS pX).obj D.G)
    (Set.range (pointsMap B S hS _ sA)) with hE
  have hπfp : IsFinitePresentation B S hS πA.hom :=
    isFinitePresentation_pullback_snd B S hS D.f.hom (yoneda.map q ≫ b₀) D.X.2 D.Y.2
      (isAlgebraicSpace_yoneda B S hS A) hfp
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj A) := hAaff
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj Y') := hY'aff
  have hEloc : IsLocallyConstructible E := by
    refine isLocallyConstructible_relativeAssassinContainmentLocus_of_isFinitePresentation B S hS
      A πA hπfp _ (D.isQuasicoherentOnSite_baseChangeTargetG bA)
      (isFinitePresentationOnSite_modulePullback B S hS pX D.G hGfp) _ hO ?_
    intro W hW
    exact isCompact_range_pointsMap_inter_preimage B S hS sA πAh h hsA₂ W hW
  have hEnhds : E ∈ 𝓝 a₀ := by
    refine (mem_nhds_iff_specializes_subset_of_isLocallyConstructible hEloc).2 ?_
    intro a' ha' ξ hξ hξa'
    obtain rfl : pointsToScheme B S hS A (pointsMap B S hS _ πAh ξ) = a' := hξa'
    exact hstep2 ξ hξ ha'
  -- A basic open neighbourhood of `a₀` inside the locus.
  obtain ⟨O, hOE, hOopen, ha₀O⟩ := mem_nhds_iff.1 hEnhds
  obtain ⟨_, ⟨t, rfl⟩, hta, htO⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1
    (isBasis_basicOpen ((BigFppfOver.toScheme B S hS).obj A)))
    (show a₀ ∈ (⟨O, hOopen⟩ : TopologicalSpace.Opens _) from ha₀O)
  -- Step 4: shrink `A` to `D(t)` and `Y'` to `D(h^♯ t)`.
  set Ah := (BigFppfOver.toScheme B S hS).map h with hAh
  let jA := ((BigFppfOver.toScheme B S hS).obj A).basicOpen t
  let jY := ((BigFppfOver.toScheme B S hS).obj Y').basicOpen (Ah.appTop.hom t)
  let A' := openSubobject B S hS A jA.ι inferInstance
  let ιA : A' ⟶ A := openSubobjectHom B S hS A jA.ι inferInstance
  let Y'' := openSubobject B S hS Y' jY.ι inferInstance
  let ιY : Y'' ⟶ Y' := openSubobjectHom B S hS Y' jY.ι inferInstance
  let α : Y'' ⟶ A' := openSubobjectLift B S hS h jA.ι inferInstance jY.ι inferInstance
    (restrictBasicOpenHom Ah t) (restrictBasicOpenHom_comp_ι Ah t)
  have hιA : (BigFppfOver.toScheme B S hS).map ιA = jA.ι :=
    toScheme_map_openSubobjectHom B S hS A jA.ι inferInstance
  have hιY : (BigFppfOver.toScheme B S hS).map ιY = jY.ι :=
    toScheme_map_openSubobjectHom B S hS Y' jY.ι inferInstance
  have hα : (BigFppfOver.toScheme B S hS).map α = restrictBasicOpenHom Ah t :=
    toScheme_map_openSubobjectLift B S hS h jA.ι inferInstance jY.ι inferInstance _ _
  have hαι : α ≫ ιA = ιY ≫ h :=
    openSubobjectLift_comp B S hS h jA.ι inferInstance jY.ι inferInstance _ _
  have hA'aff : IsAffine ((BigFppfOver.toScheme B S hS).obj A') :=
    (isAffineOpen_top _).basicOpen t
  have hY''aff : IsAffine ((BigFppfOver.toScheme B S hS).obj Y'') :=
    (isAffineOpen_top _).basicOpen _
  have hιAoi : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map ιA) := by
    rw [hιA]
    exact (inferInstance : AlgebraicGeometry.IsOpenImmersion
      (((BigFppfOver.toScheme B S hS).obj A).basicOpen t).ι)
  have hιYoi : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map ιY) := by
    rw [hιY]
    exact (inferInstance : AlgebraicGeometry.IsOpenImmersion
      (((BigFppfOver.toScheme B S hS).obj Y').basicOpen (Ah.appTop.hom t)).ι)
  have hιAE : Etale ((BigFppfOver.toScheme B S hS).map ιA) := inferInstance
  have hιYE : Etale ((BigFppfOver.toScheme B S hS).map ιY) := inferInstance
  have hmemjA : ∀ a : (BigFppfOver.toScheme B S hS).obj A',
      (BigFppfOver.toScheme B S hS).map ιA a ∈ jA := by
    intro a
    have : (BigFppfOver.toScheme B S hS).map ιA a ∈ Set.range jA.ι := by
      rw [← hιA]
      exact ⟨a, rfl⟩
    rwa [Scheme.Opens.range_ι] at this
  -- The final chart of the base.
  let b : schemeSpace A' ⟶ D.Y := schemeSpaceMap ιA ≫ bA
  have hbE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b.hom :=
    etale_comp_of_scheme B S hS ιA _ hιAE hbAE
  let a₀' : (BigFppfOver.toScheme B S hS).obj A' := ⟨a₀, hta⟩
  have hιa₀ : pointsMap B S hS _ (yoneda.map ιA) ((pointsEquivScheme B S hS A').symm a₀') =
      (pointsEquivScheme B S hS A).symm a₀ := by
    refine injective_pointsToScheme B S hS A ?_
    rw [pointsToScheme_pointsMap_yoneda]
    show (BigFppfOver.toScheme B S hS).map ιA
      ((pointsEquivScheme B S hS A') ((pointsEquivScheme B S hS A').symm a₀')) =
      (pointsEquivScheme B S hS A) ((pointsEquivScheme B S hS A).symm a₀)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, hιA]
    rfl
  -- The base change `X_{A'}` and the final chart into it.
  let pX' : (D.baseChangeTargetSpace b).obj ⟶ D.X.obj := pullback.fst D.f.hom b.hom
  let π' : (D.baseChangeTargetSpace b).obj ⟶ yoneda.obj A' := pullback.snd D.f.hom b.hom
  have sq' : IsPullback pX' π' D.f.hom b.hom := IsPullback.of_hasPullback D.f.hom b.hom
  have h2 : yoneda.map ιY ≫ yoneda.map h = yoneda.map α ≫ yoneda.map ιA := by
    rw [← Functor.map_comp, ← Functor.map_comp, hαι]
  have hgw : (yoneda.map (ιY ≫ r) ≫ U.obj.hom) ≫ D.f.hom = yoneda.map α ≫ b.hom :=
    calc (yoneda.map (ιY ≫ r) ≫ U.obj.hom) ≫ D.f.hom
        = yoneda.map ιY ≫ ((yoneda.map r ≫ U.obj.hom) ≫ D.f.hom) := by
          simp only [Functor.map_comp, Category.assoc]
      _ = yoneda.map ιY ≫ yoneda.map h ≫ yoneda.map q ≫ b₀ := by rw [hsq]
      _ = yoneda.map α ≫ yoneda.map ιA ≫ yoneda.map q ≫ b₀ := by
          rw [← Category.assoc, h2, Category.assoc]
      _ = yoneda.map α ≫ b.hom := rfl
  let gh : yoneda.obj Y'' ⟶ (D.baseChangeTargetSpace b).obj :=
    pullback.lift (yoneda.map (ιY ≫ r) ≫ U.obj.hom) (yoneda.map α) hgw
  have hgh₁ : gh ≫ pX' = yoneda.map (ιY ≫ r) ≫ U.obj.hom := pullback.lift_fst _ _ _
  have hgh₂ : gh ≫ π' = yoneda.map α := pullback.lift_snd _ _ _
  let g : schemeSpace Y'' ⟶ (D.baseChangeTarget b).X := ObjectProperty.homMk gh
  have hpX'E : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf pX' :=
    presheaf_of_isPullback B S hS sq'.flip hbE
  have hghE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf gh :=
    presheaf_etale_of_postcomp B S hS hpX'E
      (etale_comp_of_scheme B S hS (ιY ≫ r) U.obj.hom
        (by rw [Functor.map_comp]; exact Etale.etale_comp _ _) U.property) hgh₁
  refine ⟨A', b, hA'aff, isEtale_of_presheaf_etale B S hS hbE,
    ⟨(pointsEquivScheme B S hS A').symm a₀', by
      show pointsMap B S hS (yoneda.obj A') (yoneda.map ιA ≫ (yoneda.map q ≫ b₀)) _ = y
      rwa [pointsMap_comp_apply, hιa₀]⟩,
    Y'', g,
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g _
      (D.baseChangeTarget b).quasicoherent_F,
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g _
      (D.baseChangeTarget b).quasicoherent_G,
    α, hY''aff,
    isFlat_of_isEtale B S hS ((isEtale_iff_presheaf_of_yoneda B S hS gh).2 hghE),
    ObjectProperty.hom_ext _ hgh₂, ?_, ?_⟩
  · -- The relative assassin of the restricted base change lies in the restricted chart.
    intro ξ' hξ'
    let ψ : (D.baseChangeTargetSpace b).obj ⟶ (D.baseChangeTargetSpace bA).obj :=
      pullback.lift pX' (π' ≫ yoneda.map ιA) (by
        show pX' ≫ D.f.hom = (π' ≫ yoneda.map ιA) ≫ (yoneda.map q ≫ b₀)
        rw [Category.assoc]; exact sq'.w)
    have hψ₁ : ψ ≫ pX.hom = pX' := pullback.lift_fst _ _ _
    have hψ₂ : ψ ≫ πAh = π' ≫ yoneda.map ιA := pullback.lift_snd _ _ _
    have sqψ : IsPullback ψ π' πAh (yoneda.map ιA) :=
      IsPullback.of_right (by rwa [hψ₁]) hψ₂ sqA
    let Ψ : (D.baseChangeTarget b).X ⟶ D.baseChangeTargetSpace bA := ObjectProperty.homMk ψ
    have hΨ : Ψ ≫ pX = D.baseChangeTargetProjection b := ObjectProperty.hom_ext _ hψ₁
    have hmod : (modulePullback B S hS Ψ).obj ((modulePullback B S hS pX).obj D.G) ≅
        (modulePullback B S hS (D.baseChangeTargetProjection b)).obj D.G := by
      refine (modulePullbackCompIso B S hS Ψ pX).app D.G ≪≫ ?_
      rw [hΨ]
    have hψξ : IsRelativeWeaklyAssociatedPoint B S hS πA ((modulePullback B S hS pX).obj D.G)
        (pointsMap B S hS _ ψ ξ') :=
      isRelativeWeaklyAssociatedPoint_of_baseChange B S hS (g' := Ψ)
        (f' := (D.baseChangeTarget b).f) (f := πA) (g := schemeSpaceMap ιA) sqψ _
        ((isRelativeWeaklyAssociatedPoint_congr (D.baseChangeTarget b).f hmod ξ').2 hξ')
    have hinj : Function.Injective ((BigFppfOver.toScheme B S hS).map ιA) := by
      rw [hιA]
      exact jA.ι.isOpenEmbedding.injective
    set a := pointsToScheme B S hS A' (pointsMap B S hS _ π' ξ')
    have hψa : pointsToScheme B S hS A (pointsMap B S hS _ πAh (pointsMap B S hS _ ψ ξ')) =
        (BigFppfOver.toScheme B S hS).map ιA a := by
      rw [← pointsMap_comp_apply, hψ₂, pointsMap_comp_apply, pointsToScheme_pointsMap_yoneda]
    have hmemO : (BigFppfOver.toScheme B S hS).map ιA a ∈ O := htO (hmemjA a)
    obtain ⟨d, hd⟩ := hOE hmemO _ hψξ hψa
    have hdA : Ah (pointsToScheme B S hS Y' d) = (BigFppfOver.toScheme B S hS).map ιA a := by
      rw [hAh, ← pointsToScheme_pointsMap_yoneda, ← hsA₂, pointsMap_comp_apply, hd, hψa]
    have hdmem : pointsToScheme B S hS Y' d ∈ jY := by
      have : pointsToScheme B S hS Y' d ∈ Ah ⁻¹ᵁ jA := by
        show Ah (pointsToScheme B S hS Y' d) ∈ jA
        rw [hdA]
        exact hmemjA a
      rwa [Scheme.preimage_basicOpen_top] at this
    let y'' : (BigFppfOver.toScheme B S hS).obj Y'' := ⟨pointsToScheme B S hS Y' d, hdmem⟩
    set d'' := (pointsEquivScheme B S hS Y'').symm y''
    have hd''pt : pointsToScheme B S hS Y'' d'' = y'' :=
      (pointsEquivScheme B S hS Y'').apply_symm_apply y''
    have hιYd : pointsMap B S hS _ (yoneda.map ιY) d'' = d := by
      refine injective_pointsToScheme B S hS Y' ?_
      rw [pointsToScheme_pointsMap_yoneda, hd''pt, hιY]
      rfl
    have hghψ : gh ≫ ψ = yoneda.map ιY ≫ sA := by
      apply pullback.hom_ext
      · show (gh ≫ ψ) ≫ pX.hom = (yoneda.map ιY ≫ sA) ≫ pX.hom
        rw [Category.assoc, hψ₁, hgh₁, Category.assoc, hsA₁, Functor.map_comp, Category.assoc]
      · show (gh ≫ ψ) ≫ πAh = (yoneda.map ιY ≫ sA) ≫ πAh
        rw [Category.assoc, hψ₂, ← Category.assoc, hgh₂, Category.assoc, hsA₂, h2]
    refine ⟨d'', ?_⟩
    show pointsMap B S hS _ gh d'' = ξ'
    refine eq_of_pointsMap_eq_of_isPullback_of_isIso_residueFieldMap B S hS sqψ a ?_ ?_ rfl
    · rw [← pointsMap_comp_apply, hghψ, pointsMap_comp_apply, hιYd, hd]
    · rw [← pointsMap_comp_apply, hgh₂, pointsToScheme_pointsMap_yoneda, hd''pt]
      apply hinj
      rwa [← Scheme.Hom.comp_apply, ← Functor.map_comp, hαι, Functor.map_comp,
        Scheme.Hom.comp_apply, hιY]
  · -- Projectivity.
    have hFqc : (restrictToChart B S hS D.X.2 D.G U).IsQuasicoherent :=
      isQuasicoherentOnCharts_of_isQuasicoherentOnSite B S hS D.X D.G D.quasicoherent_G U
    have : ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).obj
        (restrictToChart B S hS D.X.2 D.G U)).IsQuasicoherent :=
      pullback_isQuasicoherent' _ _
    refine chartSectionsProjective_baseChangeTarget B S hS D b g α U (ιY ≫ r) hgh₁ ?_
    have e1 : (BigFppfOver.toScheme B S hS).map (ιY ≫ r) =
        jY.ι ≫ (BigFppfOver.toScheme B S hS).map r := by
      rw [Functor.map_comp, hιY]
      rfl
    rw [e1, hα]
    exact projective_sections_pullback_basicOpen Ah ((BigFppfOver.toScheme B S hS).map r)
      (restrictToChart B S hS D.X.2 D.G U) t hproj

/-- **The dévissage of Stacks 0CWC, proved.**
`AlgebraicGeometry.Space.ModuleMapSituation.DevissageInput` holds outright: it is
`AlgebraicGeometry.Space.ModuleMapSituation.hasAffineFlatChartEtaleLocallyOnBase_of_isPureRelative`
at every situation. -/
theorem devissageInput : DevissageInput B S hS :=
  hasAffineFlatChartEtaleLocallyOnBase_of_isPureRelative B S hS

end ModuleMapSituation

end AlgebraicGeometry.Space

end
