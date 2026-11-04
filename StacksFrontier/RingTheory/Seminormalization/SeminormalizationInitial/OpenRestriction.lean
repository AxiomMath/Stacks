module

public import StacksFrontier.AlgebraicGeometry.Morphisms.ResidueFieldMapIsIso
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Factorization
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.RelativeSeminormalization
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.SeminormalizationLocalization
public import Mathlib.Topology.LocalAtTarget
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import StacksFrontier.AlgebraicGeometry.Morphisms.PullbackRestrictTransport
public import StacksFrontier.RingTheory.Seminormalization.SeminormalizationInitial.Initiality

/-!
# The relative seminormalization factorization and restriction to opens

Formation of the initial subintegral factorization commutes with restriction to an open
subscheme of the target (Stacks Project, Tag 0H3N, part (3)).
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

section Restriction

open Limits Scheme.AffineZariskiSite

attribute [local instance] relativeSeminormalizationGlueData_isLocallyDirected

/-- The relative seminormalization of a dominant map of commutative rings. -/
public noncomputable def chartRing (A B : CommRingCat.{u}) (g : A ⟶ B)
    (hg : IsDominant (Spec.map g)) : CommRingCat.{u} :=
  letI := g.hom.toAlgebra
  CommRingCat.of (relativeSeminormalization A B hg)

/-- The inclusion of the relative seminormalization of a dominant map of rings into the
target of that map. -/
public noncomputable def chartRingInclusion (A B : CommRingCat.{u}) (g : A ⟶ B)
    (hg : IsDominant (Spec.map g)) : chartRing A B g hg ⟶ B :=
  letI := g.hom.toAlgebra
  CommRingCat.ofHom (relativeSeminormalization A B hg).val.toRingHom

/-- Two descriptions of one chart, over equal opens of the source, have the same relative
seminormalization. -/
public noncomputable def chartRingCongr {Z : Scheme.{u}} (A : CommRingCat.{u})
    {V W : Z.Opens} (e : V = W) (g : A ⟶ Γ(Z, V)) (g' : A ⟶ Γ(Z, W))
    (h : g ≫ Z.presheaf.map (eqToHom e.symm).op = g')
    (hg : IsDominant (Spec.map g)) (hg' : IsDominant (Spec.map g')) :
    chartRing A _ g hg ≅ chartRing A _ g' hg' := by
  subst e
  have hgg : g = g' := by simpa using h
  cases hgg
  exact Iso.refl _

/-- The comparison of two descriptions of one chart is compatible with the inclusions into the
sections of the source. -/
public theorem chartRingCongr_hom_inclusion {Z : Scheme.{u}} (A : CommRingCat.{u})
    {V W : Z.Opens} (e : V = W) (g : A ⟶ Γ(Z, V)) (g' : A ⟶ Γ(Z, W))
    (h : g ≫ Z.presheaf.map (eqToHom e.symm).op = g')
    (hg : IsDominant (Spec.map g)) (hg' : IsDominant (Spec.map g')) :
    (chartRingCongr A e g g' h hg hg').hom ≫ chartRingInclusion A _ g' hg' =
      chartRingInclusion A _ g hg ≫ Z.presheaf.map (eqToHom e.symm).op := by
  subst e
  have hgg : g = g' := by simpa using h
  cases hgg
  simp [chartRingCongr]

/-- The chart diagram map is the inclusion of the chart ring, up to the identification of the
charts with relative seminormalizations. -/
public theorem relativeSeminormalizationDiagram_map_inclusion
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f] [IsDominant f]
    {V W : X.AffineZariskiSite} (i : V ⟶ W) :
    (relativeSeminormalizationDiagram f).map i.op ≫
        chartRingInclusion Γ(X, V.1) _ (f.app V.1)
          (affineChart_app_isDominant f V.1 V.2) =
      chartRingInclusion Γ(X, W.1) _ (f.app W.1)
          (affineChart_app_isDominant f W.1 W.2) ≫
        Y.presheaf.map (homOfLE (f.preimage_mono (toOpens_mono i.le))).op :=
  rfl

/-- The chart ring inclusion is a monomorphism. -/
public theorem mono_chartRingInclusion (A B : CommRingCat.{u}) (g : A ⟶ B)
    (hg : IsDominant (Spec.map g)) : Mono (chartRingInclusion A B g hg) :=
  ConcreteCategory.mono_of_injective _ Subtype.val_injective

variable {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (U : X.Opens) [IsDominant (f ∣_ U)]

/-- An affine open of an open subscheme of `X`, viewed as an affine open of `X`. -/
public abbrev affineImage (V : U.toScheme.AffineZariskiSite) : X.AffineZariskiSite :=
  ⟨U.ι ''ᵁ V.1, V.2.image_of_isOpenImmersion U.ι⟩

public lemma affineImage_mono : Monotone (affineImage U) := by
  rintro V W ⟨r, hr⟩
  refine ⟨r, ?_⟩
  show X.basicOpen r = U.ι ''ᵁ V.1
  simpa [Scheme.image_basicOpen, Scheme.Opens.ι_appIso] using!
    congrArg (fun Q => U.ι ''ᵁ Q) hr

/-- An arrow of the small affine site of the open subscheme induces an inclusion of the
corresponding affine opens of `X`. -/
public lemma affineImage_le {V W : U.toScheme.AffineZariskiSite} (i : V ⟶ W) :
    affineImage U V ≤ affineImage U W :=
  affineImage_mono U i.le

/-- The chart of the restricted morphism over an affine open of the open subscheme agrees with
the chart of the morphism itself over the corresponding affine open of `X`. -/
public noncomputable def chartRestrictionIso (V : U.toScheme.AffineZariskiSite) :
    (relativeSeminormalizationDiagram f).obj (.op (affineImage U V)) ≅
      (relativeSeminormalizationDiagram (f ∣_ U)).obj (.op V) :=
  chartRingCongr Γ(X, U.ι ''ᵁ V.1)
    (image_morphismRestrict_preimage f U V.1).symm
    (f.app (U.ι ''ᵁ V.1)) ((f ∣_ U).app V.1)
    (morphismRestrict_app f U V.1).symm
    (affineChart_app_isDominant f _ (V.2.image_of_isOpenImmersion U.ι))
    (affineChart_app_isDominant (f ∣_ U) V.1 V.2)

public theorem chartRestrictionIso_hom_inclusion (V : U.toScheme.AffineZariskiSite) :
    (chartRestrictionIso f U V).hom ≫
        chartRingInclusion Γ(U.toScheme, V.1) _ ((f ∣_ U).app V.1)
          (affineChart_app_isDominant (f ∣_ U) V.1 V.2) =
      chartRingInclusion Γ(X, U.ι ''ᵁ V.1) _ (f.app (U.ι ''ᵁ V.1))
          (affineChart_app_isDominant f _ (V.2.image_of_isOpenImmersion U.ι)) ≫
        Y.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V.1)).op :=
  chartRingCongr_hom_inclusion ..

/-- A morphism into the chart ring of the restricted morphism is determined by its composite
with the chart inclusion, which can be computed on the chart of `f`. -/
private theorem comp_chartRestrictionIso_hom_eq (V : U.toScheme.AffineZariskiSite)
    {T : CommRingCat.{u}} {a : T ⟶ (relativeSeminormalizationDiagram f).obj (.op (affineImage U V))}
    {b : T ⟶ (relativeSeminormalizationDiagram (f ∣_ U)).obj (.op V)}
    (h : (a ≫ chartRingInclusion Γ(X, U.ι ''ᵁ V.1) _ (f.app (U.ι ''ᵁ V.1))
          (affineChart_app_isDominant f _ (V.2.image_of_isOpenImmersion U.ι))) ≫
        Y.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V.1)).op =
      b ≫ chartRingInclusion Γ(U.toScheme, V.1) _ ((f ∣_ U).app V.1)
        (affineChart_app_isDominant (f ∣_ U) V.1 V.2)) :
    a ≫ (chartRestrictionIso f U V).hom = b := by
  have := mono_chartRingInclusion Γ(U.toScheme, V.1) _ ((f ∣_ U).app V.1)
    (affineChart_app_isDominant (f ∣_ U) V.1 V.2)
  refine (cancel_mono (chartRingInclusion Γ(U.toScheme, V.1) _ ((f ∣_ U).app V.1)
    (affineChart_app_isDominant (f ∣_ U) V.1 V.2))).mp ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (whisker_eq _ (chartRestrictionIso_hom_inclusion f U V)).trans ?_
  exact (Category.assoc _ _ _).symm.trans h

public theorem chartRestrictionIso_naturality
    {V W : U.toScheme.AffineZariskiSite} (i : V ⟶ W) :
    (relativeSeminormalizationDiagram f).map (homOfLE (affineImage_le U i)).op ≫
        (chartRestrictionIso f U V).hom =
      (chartRestrictionIso f U W).hom ≫ (relativeSeminormalizationDiagram (f ∣_ U)).map i.op := by
  refine comp_chartRestrictionIso_hom_eq f U V ?_
  refine (eq_whisker (relativeSeminormalizationDiagram_map_inclusion f
    (homOfLE (affineImage_le U i))) _).trans ?_
  refine (Category.assoc _ _ _).trans (Eq.symm ?_)
  refine (Category.assoc _ _ _).trans ?_
  refine (whisker_eq _ (relativeSeminormalizationDiagram_map_inclusion (f ∣_ U) i)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (eq_whisker (chartRestrictionIso_hom_inclusion f U W) _).trans ?_
  refine (Category.assoc _ _ _).trans (Eq.symm (whisker_eq _ ?_))
  simp only [Scheme.Opens.toScheme_presheaf_map]
  refine (Y.presheaf.map_comp _ _).symm.trans (Eq.trans ?_ (Y.presheaf.map_comp _ _))
  rfl

/-- The comparison morphism from the glued relative seminormalization of the restricted
morphism to the glued relative seminormalization. -/
public noncomputable def relativeSeminormalizationRestriction :
    relativeSeminormalizationMiddle (f ∣_ U) ⟶ relativeSeminormalizationMiddle f := by
  refine colimit.desc _
    { pt := _
      ι.app V := Spec.map (chartRestrictionIso f U V).hom ≫
        (relativeSeminormalizationOpenCover f).f (affineImage U V)
      ι.naturality := ?_ }
  intro V W i
  dsimp
  rw [Category.comp_id]
  change Spec.map ((relativeSeminormalizationDiagram (f ∣_ U)).map i.op) ≫ _ ≫ _ = _
  refine (Spec.map_comp_assoc _ _ _).symm.trans ?_
  refine (congrArg (fun g => Spec.map g ≫ (relativeSeminormalizationOpenCover f).f
    (affineImage U W)) (chartRestrictionIso_naturality f U i).symm).trans ?_
  refine (Spec.map_comp_assoc _ _ _).trans ?_
  exact whisker_eq _ (colimit.w (relativeSeminormalizationGlueData f).functor
    (homOfLE (affineImage_le U i)))

public theorem ι_relativeSeminormalizationRestriction (V : U.toScheme.AffineZariskiSite) :
    (relativeSeminormalizationOpenCover (f ∣_ U)).f V ≫
        relativeSeminormalizationRestriction f U =
      Spec.map (chartRestrictionIso f U V).hom ≫
        (relativeSeminormalizationOpenCover f).f (affineImage U V) :=
  colimit.ι_desc _ _

public theorem chartRestrictionIso_comp_base (V : U.toScheme.AffineZariskiSite) :
    (relativeSeminormalizationDiagramMap f).app (.op (affineImage U V)) ≫
        (chartRestrictionIso f U V).hom =
      (relativeSeminormalizationDiagramMap (f ∣_ U)).app (.op V) := by
  exact comp_chartRestrictionIso_hom_eq f U V (morphismRestrict_app f U V.1).symm

public theorem relativeSeminormalizationOpenCover_comp_toBase
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f] [IsDominant f]
    (V : X.AffineZariskiSite) :
    (relativeSeminormalizationOpenCover f).f V ≫ relativeSeminormalizationToBase f =
      Spec.map ((relativeSeminormalizationDiagramMap f).app (.op V)) ≫ V.2.fromSpec :=
  relativeSeminormalizationOpenCover_toBase f V

/-- Over one chart, the comparison morphism is compatible with the two structure maps to the
base. -/
public theorem ι_relativeSeminormalizationRestriction_comp
    (V : U.toScheme.AffineZariskiSite) :
    (relativeSeminormalizationOpenCover (f ∣_ U)).f V ≫
        relativeSeminormalizationRestriction f U ≫ relativeSeminormalizationToBase f =
      (relativeSeminormalizationOpenCover (f ∣_ U)).f V ≫
        relativeSeminormalizationToBase (f ∣_ U) ≫ U.ι := by
  have hid : U.ι.appLE (U.ι ''ᵁ V.1) V.1 (U.ι.preimage_image_eq V.1).ge =
      𝟙 Γ(X, U.ι ''ᵁ V.1) :=
    (Scheme.Opens.ι_appLE ..).trans (X.presheaf.map_id _)
  have hfs : (V.2.image_of_isOpenImmersion U.ι).fromSpec = V.2.fromSpec ≫ U.ι :=
    ((eq_whisker (congrArg Spec.map hid) _).trans
        ((eq_whisker (Spec.map_id _) _).trans (Category.id_comp _))).symm.trans
      ((V.2.image_of_isOpenImmersion U.ι).SpecMap_appLE_fromSpec U.ι V.2
        (U.ι.preimage_image_eq V.1).ge)
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (eq_whisker (ι_relativeSeminormalizationRestriction f U V) _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (whisker_eq _ (relativeSeminormalizationOpenCover_comp_toBase f
    (affineImage U V))).trans ?_
  refine (Spec.map_comp_assoc _ _ _).symm.trans ?_
  refine (eq_whisker (congrArg Spec.map (chartRestrictionIso_comp_base f U V)) _).trans
    (Eq.symm ?_)
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (eq_whisker (relativeSeminormalizationOpenCover_comp_toBase (f ∣_ U) V) _).trans ?_
  refine (Category.assoc _ _ _).trans (Eq.symm ?_)
  exact whisker_eq _ hfs

public theorem relativeSeminormalizationRestriction_comp :
    relativeSeminormalizationRestriction f U ≫ relativeSeminormalizationToBase f =
      relativeSeminormalizationToBase (f ∣_ U) ≫ U.ι := by
  apply (relativeSeminormalizationOpenCover (f ∣_ U)).hom_ext
  intro V
  exact ι_relativeSeminormalizationRestriction_comp f U V

omit [QuasiCompact f] [QuasiSeparated f] [IsDominant f] [IsDominant (f ∣_ U)] in
public theorem opens_ι_appLE_eq_map_eqToHom (V : U.toScheme.AffineZariskiSite)
    (hVW : (f ∣_ U) ⁻¹ᵁ V.1 ≤ (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ (U.ι ''ᵁ V.1))) :
    (f ⁻¹ᵁ U).ι.appLE (f ⁻¹ᵁ (U.ι ''ᵁ V.1)) ((f ∣_ U) ⁻¹ᵁ V.1) hVW =
      Y.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V.1)).op := by
  rw [Scheme.Opens.ι_appLE]
  rfl

public theorem ι_relativeSeminormalizationFromSource_restriction
    (V : U.toScheme.AffineZariskiSite) :
    ((f ∣_ U) ⁻¹ᵁ V.1).ι ≫ relativeSeminormalizationFromSource (f ∣_ U) ≫
        relativeSeminormalizationRestriction f U =
      ((f ∣_ U) ⁻¹ᵁ V.1).ι ≫ (f ⁻¹ᵁ U).ι ≫ relativeSeminormalizationFromSource f := by
  have hVW : (f ∣_ U) ⁻¹ᵁ V.1 ≤ (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ (U.ι ''ᵁ V.1)) := by
    rw [← image_morphismRestrict_preimage f U V.1, Scheme.Hom.preimage_image_eq]
  refine (relativeSeminormalizationFromSource_chart_assoc (f ∣_ U) V _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (whisker_eq _ (ι_relativeSeminormalizationRestriction f U V)).trans ?_
  refine (eq_whisker (show affineSemiNormalizationFromSource (f ∣_ U) V.1 V.2 =
    ((f ∣_ U) ⁻¹ᵁ V.1).toSpecΓ ≫ Spec.map (chartRingInclusion Γ(U.toScheme, V.1) _
      ((f ∣_ U).app V.1) (affineChart_app_isDominant (f ∣_ U) V.1 V.2)) from rfl) _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (whisker_eq _ (Spec.map_comp_assoc _ _ _).symm).trans ?_
  refine (whisker_eq _ (eq_whisker (congrArg Spec.map
    (chartRestrictionIso_hom_inclusion f U V)) _)).trans ?_
  refine (whisker_eq _ (Spec.map_comp_assoc _ _ _)).trans ?_
  refine (whisker_eq _ (eq_whisker (congrArg Spec.map
    (opens_ι_appLE_eq_map_eqToHom f U V hVW).symm) _)).trans ?_
  refine (Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc ..).trans ?_
  refine (whisker_eq _ ((Category.assoc _ _ _).symm.trans
    (relativeSeminormalizationFromSource_chart f (affineImage U V)).symm)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (eq_whisker (Scheme.Hom.resLE_comp_ι ..) _).trans ?_
  exact Category.assoc _ _ _

public theorem relativeSeminormalizationFromSource_restriction :
    relativeSeminormalizationFromSource (f ∣_ U) ≫
        relativeSeminormalizationRestriction f U =
      (f ⁻¹ᵁ U).ι ≫ relativeSeminormalizationFromSource f := by
  apply Scheme.Cover.hom_ext ((f ⁻¹ᵁ U).toScheme.openCoverOfIsOpenCover _
    (.comap (iSup_affineOpens_eq_top U.toScheme) (f ∣_ U).base.hom))
  intro V
  exact ι_relativeSeminormalizationFromSource_restriction f U V

public theorem relativeSeminormalizationToBase_isHomeomorph :
    IsHomeomorph (relativeSeminormalizationToBase f).base :=
  MorphismProperty.universally_le (topologically @IsHomeomorph) _
    (relativeSeminormalizationToBase_universalHomeomorphism f).universally_isHomeomorph

public theorem relativeSeminormalizationRestriction_injective :
    Function.Injective (relativeSeminormalizationRestriction f U) := by
  intro x y hxy
  apply (relativeSeminormalizationToBase_isHomeomorph (f ∣_ U)).injective
  apply U.ι.injective
  have h := congrArg (fun z => relativeSeminormalizationToBase f z) hxy
  simpa only [← Scheme.Hom.comp_apply, relativeSeminormalizationRestriction_comp] using h

/-- Each chart of the restricted glued seminormalization maps into the glued seminormalization
by an open immersion. -/
public theorem isOpenImmersion_ι_relativeSeminormalizationRestriction
    (V : U.toScheme.AffineZariskiSite) :
    IsOpenImmersion ((relativeSeminormalizationOpenCover (f ∣_ U)).f V ≫
      relativeSeminormalizationRestriction f U) := by
  have hspec : IsOpenImmersion (Spec.map (chartRestrictionIso f U V).hom) := by
    have : IsIso (Spec.map (chartRestrictionIso f U V).hom) :=
      ⟨Spec.map (chartRestrictionIso f U V).inv,
        by rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id],
        by rw [← Spec.map_comp, Iso.hom_inv_id, Spec.map_id]⟩
    infer_instance
  have hcov : IsOpenImmersion ((relativeSeminormalizationOpenCover f).f (affineImage U V)) :=
    (relativeSeminormalizationOpenCover f).map_prop (affineImage U V)
  rw [ι_relativeSeminormalizationRestriction]
  exact MorphismProperty.comp_mem @IsOpenImmersion _ _ hspec hcov

public theorem relativeSeminormalizationRestriction_isOpenImmersion :
    IsOpenImmersion (relativeSeminormalizationRestriction f U) :=
  IsOpenImmersion.of_openCover_source _ (relativeSeminormalizationOpenCover (f ∣_ U))
    (relativeSeminormalizationRestriction_injective f U)
    (isOpenImmersion_ι_relativeSeminormalizationRestriction f U)

attribute [local instance] relativeSeminormalizationRestriction_isOpenImmersion

public theorem relativeSeminormalizationRestriction_isPullback :
    IsPullback (relativeSeminormalizationRestriction f U)
      (relativeSeminormalizationToBase (f ∣_ U)) (relativeSeminormalizationToBase f) U.ι := by
  apply (IsOpenImmersion.isPullback _ _ _ _
    (relativeSeminormalizationRestriction_comp f U) ?_).flip
  rw [Scheme.Opens.opensRange_ι]
  ext x
  show relativeSeminormalizationToBase f x ∈ U ↔
    x ∈ Set.range (relativeSeminormalizationRestriction f U)
  constructor
  · intro hx
    obtain ⟨y, hy⟩ :=
      (relativeSeminormalizationToBase_isHomeomorph (f ∣_ U)).surjective ⟨_, hx⟩
    refine ⟨y, (relativeSeminormalizationToBase_isHomeomorph f).injective ?_⟩
    show (relativeSeminormalizationRestriction f U ≫
      relativeSeminormalizationToBase f) y = _
    rw [relativeSeminormalizationRestriction_comp, Scheme.Hom.comp_apply, hy]
    rfl
  · rintro ⟨y, rfl⟩
    show (relativeSeminormalizationRestriction f U ≫
      relativeSeminormalizationToBase f) y ∈ U
    rw [relativeSeminormalizationRestriction_comp, Scheme.Hom.comp_apply]
    exact (relativeSeminormalizationToBase (f ∣_ U) y).property

/-- Two comparison morphisms exhibiting the restricted factorization as a base change agree. -/
public theorem subintegralFactorization_comparison_unique
    (h₀ h₁ : (seminormalizationFactorization (f ∣_ U)).middle ⟶
      (seminormalizationFactorization f).middle)
    (hp₀ : IsPullback h₀ (seminormalizationFactorization (f ∣_ U)).toBase
      (seminormalizationFactorization f).toBase U.ι)
    (hp₁ : IsPullback h₁ (seminormalizationFactorization (f ∣_ U)).toBase
      (seminormalizationFactorization f).toBase U.ι)
    (hs₀ : (seminormalizationFactorization (f ∣_ U)).toMiddle ≫ h₀ =
      (f ⁻¹ᵁ U).ι ≫ (seminormalizationFactorization f).toMiddle)
    (hs₁ : (seminormalizationFactorization (f ∣_ U)).toMiddle ≫ h₁ =
      (f ⁻¹ᵁ U).ι ≫ (seminormalizationFactorization f).toMiddle) : h₀ = h₁ := by
  let F := seminormalizationFactorization f
  let FU := seminormalizationFactorization (f ∣_ U)
  have : IsOpenImmersion h₀ := MorphismProperty.of_isPullback hp₀.flip inferInstance
  let k := hp₀.lift h₁ FU.toBase hp₁.w
  have hk₀ : k ≫ h₀ = h₁ := hp₀.lift_fst _ _ _
  have hk₁ : k ≫ FU.toBase = FU.toBase := hp₀.lift_snd _ _ _
  have hsource : FU.toMiddle ≫ k ≫ h₀ = FU.toMiddle ≫ h₀ := by
    calc FU.toMiddle ≫ k ≫ h₀ = FU.toMiddle ≫ h₁ := by rw [hk₀]
      _ = (f ⁻¹ᵁ U).ι ≫ F.toMiddle := hs₁
      _ = FU.toMiddle ≫ h₀ := hs₀.symm
  have hkSource : FU.toMiddle ≫ k = FU.toMiddle := (cancel_mono h₀).mp hsource
  let m : SubintegralFactorization.Hom FU FU := ⟨k, hkSource, hk₁⟩
  have hm : m = 𝟙 FU :=
    (seminormalizationFactorizationIsInitial (f ∣_ U)).hom_ext m (𝟙 FU)
  have hk : k = 𝟙 FU.middle := congrArg SubintegralFactorization.Hom.hom hm
  calc h₀ = 𝟙 FU.middle ≫ h₀ := by simp
    _ = k ≫ h₀ := by rw [← hk]
    _ = h₁ := hk₀

/-- The intermediate schemes of isomorphic subintegral factorizations are isomorphic. -/
public noncomputable def subintegralFactorizationMiddleIso {Y X : Scheme.{u}} {f : Y ⟶ X}
    {F G : SubintegralFactorization f} (e : F ≅ G) : F.middle ≅ G.middle where
  hom := e.hom.hom
  inv := e.inv.hom
  hom_inv_id := congrArg SubintegralFactorization.Hom.hom e.hom_inv_id
  inv_hom_id := congrArg SubintegralFactorization.Hom.hom e.inv_hom_id

end Restriction

/-- **Stacks Project, Tag 0H3N.** Formation of the relative seminormalization factorization
commutes with base change to an open subscheme of the target: the intermediate scheme of the
factorization of `f ∣_ U` is the restriction of the intermediate scheme of the factorization of
`f`, by a unique morphism compatible with both legs. -/
@[stacks 0H3N "part (3), compatibility with restriction to opens"]
public theorem existsUnique_isPullback_seminormalizationFactorization_restrict
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (U : X.Opens) :
    letI : IsDominant (f ∣_ U) := IsZariskiLocalAtTarget.restrict (‹IsDominant f›) U
    ∃! h : (seminormalizationFactorization (f ∣_ U)).middle ⟶
        (seminormalizationFactorization f).middle,
      IsPullback h (seminormalizationFactorization (f ∣_ U)).toBase
          (seminormalizationFactorization f).toBase U.ι ∧
        (seminormalizationFactorization (f ∣_ U)).toMiddle ≫ h =
          (f ⁻¹ᵁ U).ι ≫ (seminormalizationFactorization f).toMiddle := by
  classical
  let : IsDominant (f ∣_ U) := IsZariskiLocalAtTarget.restrict (‹IsDominant f›) U
  let F := seminormalizationFactorization f
  let FU := seminormalizationFactorization (f ∣_ U)
  let e := (relativeSeminormalizationFactorizationIsInitial f).uniqueUpToIso
    (seminormalizationFactorizationIsInitial f)
  let eU := (relativeSeminormalizationFactorizationIsInitial (f ∣_ U)).uniqueUpToIso
    (seminormalizationFactorizationIsInitial (f ∣_ U))
  let E : relativeSeminormalizationMiddle f ≅ F.middle :=
    subintegralFactorizationMiddleIso e
  let EU : relativeSeminormalizationMiddle (f ∣_ U) ≅ FU.middle :=
    subintegralFactorizationMiddleIso eU
  let h : FU.middle ⟶ F.middle :=
    EU.inv ≫ relativeSeminormalizationRestriction f U ≫ E.hom
  have hs : FU.toMiddle ≫ h = (f ⁻¹ᵁ U).ι ≫ F.toMiddle := by
    dsimp only [h]
    rw [← Category.assoc]
    show (FU.toMiddle ≫ eU.inv.hom) ≫ _ = _
    rw [eU.inv.toMiddle_hom]
    show relativeSeminormalizationFromSource (f ∣_ U) ≫
      relativeSeminormalizationRestriction f U ≫ E.hom = _
    rw [← Category.assoc, relativeSeminormalizationFromSource_restriction, Category.assoc]
    show (f ⁻¹ᵁ U).ι ≫ (relativeSeminormalizationFactorization f).toMiddle ≫ e.hom.hom = _
    rw [e.hom.toMiddle_hom]
  have hp : IsPullback h FU.toBase F.toBase U.ι := by
    refine (relativeSeminormalizationRestriction_isPullback f U).of_iso EU E
      (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · dsimp only [h]
      exact (Iso.hom_inv_id_assoc EU _).symm
    · exact (Category.comp_id _).trans eU.hom.hom_toBase.symm
    · exact (Category.comp_id _).trans e.hom.hom_toBase.symm
    · simp
  refine ⟨h, ⟨hp, hs⟩, ?_⟩
  intro g hg
  exact subintegralFactorization_comparison_unique f U g h hg.1 hp hg.2 hs

end AlgebraicGeometry

end
