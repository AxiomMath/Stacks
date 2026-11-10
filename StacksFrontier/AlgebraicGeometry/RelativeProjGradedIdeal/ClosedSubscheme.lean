module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionFinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Modules.PushforwardDisjointRange
public import StacksFrontier.AlgebraicGeometry.ProjBundleSurjection.Basic
public import StacksFrontier.AlgebraicGeometry.ProjMapCard.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.DegreePresenterChart
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.SectionwiseQuotient
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.FiniteTilde
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjectExtension
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjects
public import StacksFrontier.AlgebraicGeometry.SectionEpiAffine.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasicoherentSubobjectGluing.FiniteTypeCover
public import StacksFrontier.RingTheory.GradedAlgebra.UniformDegreeKernel
public import StacksFrontier.Topology.Sheaves.Modules.SupportSection

/-!
# Closed subschemes of a relative Proj, cut out in one degree

Work in Situation 01NN: a scheme `S` and a quasi-coherent graded `𝒪_S`-algebra `𝒜`, with
`p : X = Proj_S(𝒜) ⟶ S` the relative homogeneous spectrum. This file states and proves, for a
closed subscheme `i : Z ⟶ X` of finite presentation, that `Z` is cut out by a **finite type**
quasi-coherent submodule `ℱ` of a **single** homogeneous piece `𝒜_d` with `d > 0`.

The vocabulary the two tags are stated in —
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.GradedQuotientPresentation`,
`…CutsOutOnCharts`, `…IsQuotientByDegreeSubmodule`, `…DegreeQuotientPresentation` and
`…DegreeQuotientPresenter` — is in
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/DegreeDefs.lean`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.VanishesOver`: every homogeneous local
  section of `𝒜` over an open of the base is an equation for `Z`.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.VanishingIdealPresentation`: Tag 0801 as an
  input to Tag 0803 — `Z` is the relative Proj of the quotient of `𝒜` by a graded ideal `ℐ`
  containing the sections vanishing on `Z`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.compactSpace_proj_grading`: the chart of a
  quasi-compact relative Proj over an affine open of the base is quasi-compact.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.exists_finiteType_degreeQuotientPresentation`:
  the content of **Tag 0802**, with the relative case of Tag 0801 as an argument; the tag is
  registered on the statement with that argument discharged, in the module
  `StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.FiniteTypeDegreeQuotientPresentation`.
* `…RelativeProjGradedIdeal.exists_finiteType_presentation_supp_of_vanishingIdeal`:
  the content of **Tag 0803** — the submodule chosen so that `𝒜_d/ℱ` is supported away from an open
  of the base the closed subscheme misses — with the relative case of Tag 0801 as an argument;
  the tag is registered on the statement with that argument discharged, in
  `StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/FiniteTypePresentationOffSupport.lean`.

## References

* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
* [Stacks Project, Tag 0802](https://stacks.math.columbia.edu/tag/0802)
* [Stacks Project, Tag 0803](https://stacks.math.columbia.edu/tag/0803)

## Not done here

**Tag 0801 in the relative case is not proved in this file**, and the two statements below are
written with it as an argument: `…exists_finiteType_degreeQuotientPresentation` (Tag 0802) takes
a `GradedQuotientPresentation` and `…exists_finiteType_presentation_supp_of_vanishingIdeal`
(Tag 0803) takes a `VanishingIdealPresentation`.

**Both are produced, in full, downstream.** The constructions are
`Stacks.AlgebraicGeometry.RelativeProjTwists.gradedQuotientPresentation` and
`…RelativeProjTwists.vanishingIdealPresentation` in
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/VanishingPresentation.lean`, which carry
no hypothesis beyond the two tags' own, and the registrations of Tags 0802 and 0803 with those
arguments discharged are
`Stacks.AlgebraicGeometry.RelativeProjTwists.exists_finiteType_degreeQuotientPresentation` in
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/FiniteTypeDegreeQuotientPresentation.lean`
and `…RelativeProjTwists.exists_finiteType_presentation_supp` in
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/FiniteTypePresentationOffSupport.lean`.

The order is forced: `…compactSpace_proj_grading` below is what makes a chart of a quasi-compact
relative Proj quasi-compact, which is the hypothesis the absolute case of Tag 0801 is stated
with, so the construction of the presentation is downstream of this file and the statements here
cannot consume it.

Two apparent obstructions are *not* among the inputs at all: the
`Submodule`-versus-`AddSubgroup` grading mismatch has a bridge
(`Stacks.ProjChartKerQuotient.ker_eq_ker_projMap_quotientMk` reproves the absolute case at an
`AddSubgroup`-valued grading outright), and the chart-level comparison of the relative twists and
of the relative section map with the absolute ones exists
(`…RelativeProjTwists.ChartData.chartIso` and `…RelativeProjTwists.TwistData.ψ_chart`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.ProjMapCard
open Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain

namespace Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

universe u

variable {S : Scheme.{u}}

/-! ### The charts of a quasi-compact relative Proj are quasi-compact -/

/-- **The chart over an affine open of the base is quasi-compact when the structure morphism of
the relative Proj is**: the chart is the inverse image of that affine open.

Public because it is the only producer of `CompactSpace (AlgebraicGeometry.Proj (𝒜.grading U))`,
which is the hypothesis the absolute case of Tag 0801 —
`Stacks.ClosedSubschemeProjQuotient.ker_eq_ker_ambientHom` — is stated with, and so the form in
which quasi-compactness of `Proj_S(𝒜) ⟶ S` reaches a chart-level argument. -/
public theorem compactSpace_proj_grading (A : SheafGradedAlgebra S)
    [QuasiCompact (relativeProj A).toBase] (U : S.Opens) (hU : IsAffineOpen U) :
    CompactSpace (AlgebraicGeometry.Proj (A.grading U)) := by
  have : IsAffine U.toScheme := hU
  have : QuasiCompact (projInclusionToOpen A U hU) :=
    MorphismProperty.of_isPullback ((relativeProj A).chart_isPullback U hU) inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (projInclusionToOpen A U hU)

/-- Finitely many homogeneous sections of positive degree over an affine open of the base whose
standard opens cover the chart. -/
private theorem exists_finite_cover_chart (A : SheafGradedAlgebra S)
    [QuasiCompact (relativeProj A).toBase] (U : S.Opens) (hU : IsAffineOpen U) :
    ∃ t : Finset (A.sectionRing U), (∀ f ∈ t, ∃ e : ℕ, 0 < e ∧ f ∈ A.grading U e) ∧
      (⨆ f ∈ t, AlgebraicGeometry.Proj.basicOpen (A.grading U) f) = ⊤ := by
  obtain ⟨t, ht, h⟩ := (AlgebraicGeometry.Proj.compactSpace_iff (A.grading U)).mp
    (compactSpace_proj_grading A U hU)
  exact ⟨t, ht, AlgebraicGeometry.Proj.iSup_basicOpen_eq_top_of_irrelevant_le_radical _ t h⟩

/-! ### The localized kernel on a chart is finitely generated -/

/-- `AlgebraicGeometry.LocallyOfFinitePresentation` respects isomorphisms of arrows. -/
private theorem respectsIso_locallyOfFinitePresentation :
    MorphismProperty.RespectsIso
      (@AlgebraicGeometry.LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
  MorphismProperty.RespectsIso.mk _
    (fun _ _ hf => by have := hf; infer_instance)
    (fun _ _ hf => by have := hf; infer_instance)

/-- For a closed immersion locally of finite presentation, the kernel of the map of sections over
an affine open of the target and its inverse image is finitely generated. -/
private theorem ker_appLE_fg_of_closedImmersion {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsClosedImmersion g] [AlgebraicGeometry.LocallyOfFinitePresentation g]
    {V : Y.Opens} (hV : IsAffineOpen V) {V' : X.Opens} (hV' : V' = g ⁻¹ᵁ V)
    (hle : V' ≤ g ⁻¹ᵁ V) :
    (RingHom.ker (g.appLE V V' hle).hom).FG := by
  subst hV'
  have hV2 : IsAffineOpen (g ⁻¹ᵁ V) := hV.preimage g
  have hfp := g.finitePresentation_appLE hV hV2 hle
  have hsurj : Function.Surjective (g.appLE V (g ⁻¹ᵁ V) hle).hom := by
    rw [Scheme.Hom.appLE_eq_app]
    exact g.app_surjective V hV
  let : Algebra Γ(Y, V) Γ(X, g ⁻¹ᵁ V) := RingHom.toAlgebra (g.appLE V (g ⁻¹ᵁ V) hle).hom
  let : Algebra.FinitePresentation Γ(Y, V) Γ(X, g ⁻¹ᵁ V) := hfp
  exact Algebra.FinitePresentation.ker_fG_of_surjective
    (Algebra.ofId Γ(Y, V) Γ(X, g ⁻¹ᵁ V)) hsurj

/-- The inclusion of an open which is everything is an isomorphism on sections. -/
private theorem isIso_opens_ι_appLE {X : Scheme.{u}} {U : X.Opens} (hU : U = ⊤) (W : X.Opens) :
    IsIso (U.ι.appLE W (U.ι ⁻¹ᵁ W) le_rfl) := by
  have himg : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, hU, top_inf_eq]
  have h2 : IsIso (U.ι.appLE (U.ι ''ᵁ (U.ι ⁻¹ᵁ W)) (U.ι ⁻¹ᵁ W)
      (Scheme.Hom.preimage_image_eq U.ι _).ge) := by
    rw [← Scheme.Hom.appIso_hom' U.ι]
    infer_instance
  exact (Scheme.Hom.appLE_congr U.ι _ himg rfl (fun g => IsIso g)).mp h2

section Away

variable {R T : Type u} {σ τ : Type*} [CommRing R] [CommRing T]
  [SetLike σ R] [AddSubgroupClass σ R] [SetLike τ T] [AddSubgroupClass τ T]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- Transporting a kernel across a commuting square of ring isomorphisms. -/
private theorem ker_eq_map_of_iso_square {R₁ T₁ R₂ T₂ : CommRingCat.{u}}
    (α : R₁ ≅ R₂) (β : T₁ ≅ T₂) {φ : R₁ ⟶ T₁} {φ' : R₂ ⟶ T₂}
    (h : α.hom ≫ φ' = φ ≫ β.hom) :
    RingHom.ker φ.hom = Ideal.map α.inv.hom (RingHom.ker φ'.hom) := by
  have hsq (x : R₁) : φ'.hom (α.hom.hom x) = β.hom.hom (φ.hom x) :=
    congrArg (fun k : R₁ ⟶ T₂ => k.hom x) h
  have hα (x : R₁) : α.inv.hom (α.hom.hom x) = x :=
    congrArg (fun k : R₁ ⟶ R₁ => k.hom x) α.hom_inv_id
  have hα' (x : R₂) : α.hom.hom (α.inv.hom x) = x :=
    congrArg (fun k : R₂ ⟶ R₂ => k.hom x) α.inv_hom_id
  have hβ (x : T₁) : β.inv.hom (β.hom.hom x) = x :=
    congrArg (fun k : T₁ ⟶ T₁ => k.hom x) β.hom_inv_id
  refine le_antisymm (fun x hx => ?_) ?_
  · have hx' : φ'.hom (α.hom.hom x) = 0 := by
      rw [hsq, RingHom.mem_ker.mp hx, map_zero]
    have hmem := Ideal.mem_map_of_mem (α.inv.hom : R₂ →+* R₁) (RingHom.mem_ker.mpr hx')
    rwa [hα x] at hmem
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy
    refine Ideal.mem_comap.mpr (RingHom.mem_ker.mpr ?_)
    have h0 : β.hom.hom (φ.hom (α.inv.hom y)) = 0 := by
      rw [← hsq, hα' y, RingHom.mem_ker.mp hy]
    have h1 := congrArg β.inv.hom h0
    rwa [map_zero, hβ] at h1

/-- For a graded ring homomorphism whose induced morphism of projective spectra is everywhere
defined, a closed immersion and locally of finite presentation, the kernel of the induced map of
degree-zero localizations away from a positive-degree homogeneous element is finitely
generated. -/
private theorem away_map_ker_fg (φ : 𝒜 →+*ᵍ ℬ)
    (hci : IsClosedImmersion (projMapData 𝒜 ℬ φ).hom)
    (hfp : AlgebraicGeometry.LocallyOfFinitePresentation (projMapData 𝒜 ℬ φ).hom)
    (hdom : mapDomain 𝒜 ℬ φ = ⊤)
    (f : R) (e : ℕ) (hf : f ∈ 𝒜 e) (he : 0 < e) :
    (RingHom.ker (HomogeneousLocalization.Away.map φ f)).FG := by
  have := hci
  have := hfp
  have hbo := projMapData_basicOpen 𝒜 ℬ φ f e hf he
  have hfg' : (RingHom.ker (Scheme.Hom.appLE (projMapData 𝒜 ℬ φ).hom
      (AlgebraicGeometry.Proj.basicOpen 𝒜 f)
      ((mapDomain 𝒜 ℬ φ).ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen ℬ (φ f))
      (by rw [hbo])).hom).FG :=
    ker_appLE_fg_of_closedImmersion _
      (AlgebraicGeometry.Proj.isAffineOpen_basicOpen 𝒜 f hf he) hbo.symm _
  have := isIso_opens_ι_appLE hdom (AlgebraicGeometry.Proj.basicOpen ℬ (φ f))
  have hker := ker_eq_map_of_iso_square
    (AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 f hf he)
    (AlgebraicGeometry.Proj.basicOpenIsoAway ℬ (φ f) (GradedRingHom.map_mem φ hf) he ≪≫
      asIso (Scheme.Hom.appLE (mapDomain 𝒜 ℬ φ).ι
        (AlgebraicGeometry.Proj.basicOpen ℬ (φ f))
        ((mapDomain 𝒜 ℬ φ).ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen ℬ (φ f)) le_rfl))
    (φ := CommRingCat.ofHom (HomogeneousLocalization.Away.map φ f))
    (by
      rw [AlgebraicGeometry.Proj.basicOpenIsoAway_hom, Iso.trans_hom, asIso_hom,
        AlgebraicGeometry.Proj.basicOpenIsoAway_hom]
      exact projMapData_awayToSection 𝒜 ℬ φ f e hf he)
  have hres : (RingHom.ker (CommRingCat.ofHom
      (HomogeneousLocalization.Away.map φ f)).hom).FG := by
    rw [hker]
    exact hfg'.map _
  exact hres

/-- The everywhere-defined induced morphism is the morphism of the canonical bundle, up to the
isomorphism identifying `Proj ℬ` with the domain of definition. -/
private theorem comp_projMapData_hom (φ : 𝒜 →+*ᵍ ℬ) (hdom : mapDomain 𝒜 ℬ φ = ⊤) :
    ((Scheme.topIso (AlgebraicGeometry.Proj ℬ)).inv ≫
        ((AlgebraicGeometry.Proj ℬ).isoOfEq hdom.symm).hom) ≫ (projMapData 𝒜 ℬ φ).hom =
      mapHomOfTop 𝒜 ℬ φ hdom :=
  Category.assoc _ _ _

/-- A morphism property respecting isomorphisms holds for the morphism of the canonical bundle as
soon as it holds for the everywhere-defined induced morphism. -/
private theorem property_projMapData_hom (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (φ : 𝒜 →+*ᵍ ℬ) (hdom : mapDomain 𝒜 ℬ φ = ⊤) (h : P (mapHomOfTop 𝒜 ℬ φ hdom)) :
    P (projMapData 𝒜 ℬ φ).hom := by
  rw [← comp_projMapData_hom 𝒜 ℬ φ hdom] at h
  exact (P.cancel_left_of_respectsIso _ _).mp h

end Away

/-- The chart maps of a graded quotient presentation of a closed subscheme locally of finite
presentation are locally of finite presentation: the chart over an affine open of the base is the
inverse image of the corresponding chart of the ambient relative Proj. -/
private theorem locallyOfFinitePresentation_chartMap {A : SheafGradedAlgebra S} {Z : Scheme.{u}}
    {i : Z ⟶ (relativeProj A).scheme} (P : GradedQuotientPresentation A i)
    (hi : AlgebraicGeometry.LocallyOfFinitePresentation i)
    (U : S.Opens) (hU : IsAffineOpen U) :
    AlgebraicGeometry.LocallyOfFinitePresentation
      (ProjBundleSurjection.chartMap P.surjective U hU) := by
  have hri := respectsIso_locallyOfFinitePresentation.{u}
  have hmap : AlgebraicGeometry.LocallyOfFinitePresentation
      (ProjBundleSurjection.map P.surjective) := by
    have h0 : AlgebraicGeometry.LocallyOfFinitePresentation
        (P.iso.hom ≫ ProjBundleSurjection.map P.surjective) := by
      rw [P.iso_comp]; exact hi
    exact (MorphismProperty.cancel_left_of_respectsIso _ P.iso.hom _).mp h0
  have h₂ := ProjBundleSurjection.isPullback_chart P.surjective U hU
  have h₁ : IsPullback (pullback.fst (ProjBundleSurjection.map P.surjective)
      ((relativeProj A).chart U hU))
      (pullback.snd (ProjBundleSurjection.map P.surjective) ((relativeProj A).chart U hU))
      (ProjBundleSurjection.map P.surjective) ((relativeProj A).chart U hU) :=
    IsPullback.of_hasPullback _ _
  have e₁ : Arrow.mk (ProjBundleSurjection.chartMap P.surjective U hU) ≅
      Arrow.mk (pullback.snd (ProjBundleSurjection.map P.surjective)
        ((relativeProj A).chart U hU)) :=
    Arrow.isoMk (h₂.isoIsPullback _ _ h₁) (Iso.refl _)
  have e₂ := morphismRestrictOpensRange (ProjBundleSurjection.map P.surjective)
    ((relativeProj A).chart U hU)
  have := hmap
  exact (MorphismProperty.arrow_mk_iso_iff
    (P := @AlgebraicGeometry.LocallyOfFinitePresentation) (e₁.trans e₂.symm)).mpr
    inferInstance

/-- **The localized kernel on a chart is finitely generated.** For a graded quotient presentation
of a closed subscheme of finite presentation, the kernel of the induced map of degree-zero
homogeneous localizations away from a positive-degree homogeneous section over an affine open of
the base is a finitely generated ideal. -/
private theorem away_sectionHom_ker_fg {A : SheafGradedAlgebra S} {Z : Scheme.{u}}
    {i : Z ⟶ (relativeProj A).scheme} [IsClosedImmersion i]
    (P : GradedQuotientPresentation A i) (hi : AlgebraicGeometry.LocallyOfFinitePresentation i)
    (U : S.Opens) (hU : IsAffineOpen U)
    (f : A.sectionRing U) (e : ℕ) (hf : f ∈ A.grading U e) (he : 0 < e) :
    (RingHom.ker (HomogeneousLocalization.Away.map (P.hom.sectionHom U) f)).FG := by
  have hdom := ProjBundleSurjection.mapDomain_sectionHom_eq_top P.surjective hU
  have hri := respectsIso_locallyOfFinitePresentation.{u}
  refine away_map_ker_fg (A.grading U) (P.target.grading U) (P.hom.sectionHom U) ?_ ?_ hdom
    f e hf he
  · exact property_projMapData_hom _ _ (@IsClosedImmersion) _ hdom
      (ProjBundleSurjection.isClosedImmersion_chartMap P.surjective U hU)
  · exact property_projMapData_hom _ _ (@AlgebraicGeometry.LocallyOfFinitePresentation) _ hdom
      (locallyOfFinitePresentation_chartMap P hi U hU)

/-! ### Finite type quasi-coherent submodules containing given local sections -/

section FiniteType

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]

/-- A section of a quasi-coherent module over an affine open lies in a quasi-coherent submodule
of finite type: this is Tag 01PG, through the extension lemma Tag 01PF. -/
private theorem exists_finiteTypeSubobject_section (F : X.Modules) [F.IsQuasicoherent]
    (W : X.Opens) (hW : IsAffineOpen W) (s : Γ(F, W)) :
    ∃ (G : FiniteTypeQuasicoherentSubobject F) (z : Γ((G.1 : X.Modules), W)),
      G.1.arrow.app W z = s :=
  exists_finiteTypeQuasicoherentSubobject_section_of_extension F W s fun G hqc hft => by
    have := hqc
    have := hft
    exact exists_finiteTypeQuasicoherentSubobject_extension F W hW.isCompact G

/-- Finitely many sections of a quasi-coherent module over affine opens lie in a single
quasi-coherent submodule of finite type: the quasi-coherent submodules of finite type are
filtered, so finitely many of them have an upper bound. -/
private theorem exists_finiteTypeSubobject_sections (F : X.Modules) [F.IsQuasicoherent]
    (t : Finset (Σ W : X.Opens, Γ(F, W))) (ht : ∀ x ∈ t, IsAffineOpen x.1) :
    ∃ G : Subobject F, (G : X.Modules).IsQuasicoherent ∧
      SheafOfModules.IsFiniteType.{u, u, u} (G : X.Modules) ∧
        ∀ x ∈ t, ∃ z, G.arrow.app x.1 z = x.2 := by
  classical
  have hlocal : ∀ x : t, ∃ G : FiniteTypeQuasicoherentSubobject F,
      ∃ z, G.1.arrow.app x.1.1 z = x.1.2 :=
    fun x => exists_finiteTypeSubobject_section F x.1.1 (ht x.1 x.2) x.1.2
  choose G z hz using hlocal
  refine ⟨(IsFiltered.sup (Finset.univ.image G) ∅).1,
    (IsFiltered.sup (Finset.univ.image G) ∅).2.1,
    (IsFiltered.sup (Finset.univ.image G) ∅).2.2, fun x hx => ?_⟩
  have hle : (G ⟨x, hx⟩).1 ≤ (IsFiltered.sup (Finset.univ.image G) ∅).1 :=
    leOfHom (IsFiltered.toSup (Finset.univ.image G) ∅
      (Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩)).hom
  have h1 : (G ⟨x, hx⟩).1.ofLE (IsFiltered.sup (Finset.univ.image G) ∅).1 hle ≫
      (IsFiltered.sup (Finset.univ.image G) ∅).1.arrow = (G ⟨x, hx⟩).1.arrow :=
    Subobject.ofLE_arrow hle
  refine ⟨((G ⟨x, hx⟩).1.ofLE _ hle).app x.1 (z ⟨x, hx⟩), ?_⟩
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, h1]
  exact hz ⟨x, hx⟩

end FiniteType

/-- The sectionwise image of a monomorphism of modules, as a submodule of its target, is
isomorphic to its source. -/
private def imageSubmoduleIso {X : Scheme.{u}} {M N : X.Modules} (p : M ⟶ N) [Mono p] :
    (AlgebraicGeometry.imageSubmodule p).toSheafOfModules ≅ M :=
  Stacks.Algebraization.kernelSubmoduleIso (cokernel.π (C := X.Modules) p) ≪≫
    Abelian.imageIsoImage p ≪≫ Limits.imageMonoIsoSource p

/-! ### The degreewise kernel, and the submodules a subobject of it cuts out -/

/-- The sectionwise kernel of the degree-`n` component of a homomorphism of sheaf-level graded
algebras, as a module on the base. -/
private def kernelModule (A : SheafGradedAlgebra S) {B : SheafGradedAlgebra S}
    (ψ : SheafGradedAlgebraHom A B) (n : ℕ) : S.Modules :=
  (Stacks.Algebraization.kernelSubmodule (ψ.app (n : ℤ))).toSheafOfModules

/-- Its inclusion into the degree-`n` homogeneous piece. -/
private def kernelInclusion (A : SheafGradedAlgebra S) {B : SheafGradedAlgebra S}
    (ψ : SheafGradedAlgebraHom A B) (n : ℕ) : kernelModule A ψ n ⟶ A.piece (n : ℤ) :=
  (Stacks.Algebraization.kernelSubmodule (ψ.app (n : ℤ))).ι

/-- The inclusion of the sectionwise kernel is a monomorphism. -/
private theorem mono_kernelInclusion (A : SheafGradedAlgebra S) {B : SheafGradedAlgebra S}
    (ψ : SheafGradedAlgebraHom A B) (n : ℕ) : Mono (kernelInclusion A ψ n) :=
  inferInstanceAs (Mono (Stacks.Algebraization.kernelSubmodule (ψ.app (n : ℤ))).ι)

/-- The sections of the sectionwise kernel are the sections killed by the degree-`n`
component. -/
private theorem range_kernelInclusion_app (A : SheafGradedAlgebra S) {B : SheafGradedAlgebra S}
    (ψ : SheafGradedAlgebraHom A B) (n : ℕ) (W : S.Opens) :
    LinearMap.range ((kernelInclusion A ψ n).val.app (op W)).hom =
      (Stacks.Algebraization.kernelSubmodule (ψ.app (n : ℤ))).toSubmodule.obj (op W) :=
  AlgebraicGeometry.range_submodule_ι_app _ W

/-- The sectionwise kernel is quasi-coherent. -/
private theorem isQuasicoherent_kernelModule (A : SheafGradedAlgebra S) {B : SheafGradedAlgebra S}
    (ψ : SheafGradedAlgebraHom A B) (n : ℕ) : (kernelModule A ψ n).IsQuasicoherent :=
  (_root_.SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
    (Stacks.Algebraization.kernelSubmoduleIso (ψ.app (n : ℤ))).symm
    (Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel _)

/-- A section of `𝒜_n` comes from the sectionwise kernel exactly when the degree-`n` component
kills it. -/
private theorem mem_range_kernelInclusion_app_iff (A : SheafGradedAlgebra S)
    {B : SheafGradedAlgebra S} (ψ : SheafGradedAlgebraHom A B) (n : ℕ) (W : S.Opens)
    (a : Γ(A.piece (n : ℤ), W)) :
    a ∈ LinearMap.range ((kernelInclusion A ψ n).val.app (op W)).hom ↔
      (ψ.app (n : ℤ)).app W a = 0 := by
  rw [range_kernelInclusion_app]
  exact AlgebraicGeometry.mem_kernelSubmodule_iff (ψ.app (n : ℤ)) W a

/-- The submodule of `𝒜_n` cut out by a subobject of the sectionwise kernel: the sectionwise
image of its inclusion. -/
private def kernelSubobjectSubmodule (A : SheafGradedAlgebra S) {B : SheafGradedAlgebra S}
    (ψ : SheafGradedAlgebraHom A B) (n : ℕ) (H : Subobject (kernelModule A ψ n)) :
    (A.piece (n : ℤ)).Submodule :=
  AlgebraicGeometry.imageSubmodule (H.arrow ≫ kernelInclusion A ψ n)

/-- Its sections over an open are the image of the sections of the subobject. -/
private theorem kernelSubobjectSubmodule_obj (A : SheafGradedAlgebra S)
    {B : SheafGradedAlgebra S} (ψ : SheafGradedAlgebraHom A B) (n : ℕ)
    (H : Subobject (kernelModule A ψ n)) (W : S.Opens) :
    (kernelSubobjectSubmodule A ψ n H).toSubmodule.obj (op W) =
      LinearMap.range (((H.arrow ≫ kernelInclusion A ψ n).val.app (op W))).hom :=
  have : Mono (H.arrow ≫ kernelInclusion A ψ n) :=
    @mono_comp _ _ _ _ _ _ inferInstance _ (mono_kernelInclusion A ψ n)
  AlgebraicGeometry.imageSubmodule_obj _ this W

/-- Every local section of it is an equation for the closed subscheme: it comes from the
sectionwise kernel. -/
private theorem isEquationSubmodule_kernelSubobjectSubmodule (A : SheafGradedAlgebra S)
    {B : SheafGradedAlgebra S} (ψ : SheafGradedAlgebraHom A B) (n : ℕ)
    (H : Subobject (kernelModule A ψ n)) :
    IsEquationSubmodule A (kernelSubobjectSubmodule A ψ n H) ψ := by
  intro W a ha
  rw [kernelSubobjectSubmodule_obj A ψ n H W] at ha
  obtain ⟨b, hb⟩ := ha
  exact (mem_range_kernelInclusion_app_iff A ψ n W a).mp ⟨H.arrow.val.app (op W) b, hb⟩

/-- Passing from a subobject to a larger one does not change the image in `𝒜_n`. -/
private theorem kernelInclusion_app_ofLE (A : SheafGradedAlgebra S) {B : SheafGradedAlgebra S}
    (ψ : SheafGradedAlgebraHom A B) (n : ℕ) {G H : Subobject (kernelModule A ψ n)} (h : G ≤ H)
    (W : S.Opens) (b : Γ((G : S.Modules), W)) :
    ((H.arrow ≫ kernelInclusion A ψ n).val.app (op W)).hom
        ((Subobject.ofLE G H h).val.app (op W) b) =
      ((G.arrow ≫ kernelInclusion A ψ n).val.app (op W)).hom b := by
  rw [← Subobject.ofLE_arrow h]
  rfl

/-- Enlarging the subobject enlarges the submodule it cuts out. -/
private theorem kernelSubobjectSubmodule_mono (A : SheafGradedAlgebra S)
    {B : SheafGradedAlgebra S} (ψ : SheafGradedAlgebraHom A B) (n : ℕ)
    {G H : Subobject (kernelModule A ψ n)} (h : G ≤ H) :
    kernelSubobjectSubmodule A ψ n G ≤ kernelSubobjectSubmodule A ψ n H := by
  intro W a ha
  rw [kernelSubobjectSubmodule_obj A ψ n G W.unop] at ha
  rw [kernelSubobjectSubmodule_obj A ψ n H W.unop]
  obtain ⟨b, hb⟩ := ha
  exact ⟨(Subobject.ofLE G H h).val.app (op W.unop) b,
    (kernelInclusion_app_ofLE A ψ n h W.unop b).trans hb⟩

/-- The submodule cut out by a quasi-coherent subobject is quasi-coherent. -/
private theorem isQuasicoherent_kernelSubobjectSubmodule (A : SheafGradedAlgebra S)
    {B : SheafGradedAlgebra S} (ψ : SheafGradedAlgebraHom A B) (n : ℕ)
    (H : Subobject (kernelModule A ψ n)) (hH : (H : S.Modules).IsQuasicoherent) :
    (kernelSubobjectSubmodule A ψ n H).toSheafOfModules.IsQuasicoherent :=
  have := hH
  AlgebraicGeometry.isQuasicoherent_imageSubmodule (H.arrow ≫ kernelInclusion A ψ n)

/-- The submodule cut out by a subobject of finite type is of finite type. -/
private theorem isFiniteType_kernelSubobjectSubmodule (A : SheafGradedAlgebra S)
    [CompactSpace S] [QuasiSeparatedSpace S] {B : SheafGradedAlgebra S}
    (ψ : SheafGradedAlgebraHom A B) (n : ℕ) (H : Subobject (kernelModule A ψ n))
    (hH : SheafOfModules.IsFiniteType.{u, u, u} (H : S.Modules)) :
    SheafOfModules.IsFiniteType.{u, u, u}
      (kernelSubobjectSubmodule A ψ n H).toSheafOfModules :=
  have := hH
  have : Mono (H.arrow ≫ kernelInclusion A ψ n) :=
    @mono_comp _ _ _ _ _ _ inferInstance _ (mono_kernelInclusion A ψ n)
  Stacks.SheafOfModules.isFiniteType_of_iso.{u} (imageSubmoduleIso _).symm

/-! ### Monotonicity of the cutting-out condition -/

/-- Enlarging `ℱ` enlarges its set of homogeneous local sections. -/
private theorem degreeSectionSet_mono (A : SheafGradedAlgebra S) {d : ℕ}
    {ℱ ℋ : (A.piece (d : ℤ)).Submodule} (h : ℱ ≤ ℋ) (U : S.Opens) :
    degreeSectionSet A ℱ U ⊆ degreeSectionSet A ℋ U := by
  rintro x ⟨a, ha, rfl⟩
  exact ⟨a, h (op U) ha, rfl⟩

/-- Enlarging `ℱ` enlarges the ideal it generates on a chart. -/
private theorem chartIdeal_mono (A : SheafGradedAlgebra S) {d : ℕ}
    {ℱ ℋ : (A.piece (d : ℤ)).Submodule} (h : ℱ ≤ ℋ) (U : S.Opens) {e : ℕ}
    {f : A.sectionRing U} (hf : f ∈ A.grading U e) :
    chartIdeal A ℱ U hf ≤ chartIdeal A ℋ U hf := by
  refine Ideal.span_mono ?_
  rintro z ⟨k, x, hx, hxspan, rfl⟩
  exact ⟨k, x, hx, Ideal.span_mono (degreeSectionSet_mono A h U) hxspan, rfl⟩

/-- Cutting out on the charts is preserved by enlarging `ℱ`. -/
private theorem cutsOutOnCharts_mono (A : SheafGradedAlgebra S) {d : ℕ}
    {ℱ ℋ : (A.piece (d : ℤ)).Submodule} (h : ℱ ≤ ℋ) {B : SheafGradedAlgebra S}
    (ψ : SheafGradedAlgebraHom A B) (hcut : CutsOutOnCharts A ℱ ψ) :
    CutsOutOnCharts A ℋ ψ := by
  obtain ⟨D⟩ := hcut
  exact ⟨{ index := D.index
           cover := D.cover
           isAffineOpen_cover := D.isAffineOpen_cover
           iSup_cover := D.iSup_cover
           chart := fun k =>
             { index := (D.chart k).index
               elt := (D.chart k).elt
               deg := (D.chart k).deg
               deg_pos := (D.chart k).deg_pos
               elt_mem := (D.chart k).elt_mem
               cover := (D.chart k).cover
               ker_le := fun c =>
                 ((D.chart k).ker_le c).trans (chartIdeal_mono A h _ _) } }⟩

/-! ### The uniform degree and the finite type submodule -/

/-- A finite set of positive natural numbers has a positive common multiple. -/
private theorem exists_common_positive_multiple (s : Finset ℕ) (hs : ∀ n ∈ s, 0 < n) :
    ∃ d : ℕ, 0 < d ∧ ∀ n ∈ s, n ∣ d :=
  ⟨∏ n ∈ s, n, Finset.prod_pos hs, fun _ hn => Finset.dvd_prod_of_mem (fun n => n) hn⟩

/-- A homogeneous section of degree `n` dies in the graded ring of sections of the quotient
exactly when the degree-`n` component of the quotient map kills it. -/
private theorem sectionHom_of_eq_zero_iff {A B : SheafGradedAlgebra S}
    (ψ : SheafGradedAlgebraHom A B) (U : S.Opens) (n : ℕ) (a : A.sectionPieces U n) :
    ψ.sectionHom U (DirectSum.of (A.sectionPieces U) n a) = 0 ↔
      ψ.sectionPieceHom U n a = 0 := by
  rw [ψ.sectionHom_of U a]
  exact map_eq_zero_iff _ (DirectSum.of_injective (β := B.sectionPieces U) n)

/-- The degree-`d` generators of the localized kernel on one standard open of one chart: an
exponent for the common denominator, the generators themselves, and homogeneous numerators of
degree `d` which die in the quotient. -/
private structure LocalKernelGenerators (A : SheafGradedAlgebra S) {Z : Scheme.{u}}
    {i : Z ⟶ (relativeProj A).scheme} (P : GradedQuotientPresentation A i) (d : ℕ)
    (U : S.Opens) (e : ℕ) (f : A.grading U e) where
  /-- The exponent of the common denominator. -/
  exp : ℕ
  /-- The chosen generators of the localized kernel. -/
  gens : Finset (HomogeneousLocalization.Away (A.grading U) (f : A.sectionRing U))
  /-- A numerator for each generator. -/
  num : ↥gens → A.sectionRing U
  /-- Each numerator is homogeneous of the degree matching the denominator. -/
  num_mem (w : ↥gens) : num w ∈ A.grading U (exp • e)
  /-- Each numerator represents its generator. -/
  num_mk (w : ↥gens) :
    HomogeneousLocalization.Away.mk (A.grading U) f.2 exp (num w) (num_mem w) = w.val
  /-- Each numerator is homogeneous of degree `d`. -/
  num_deg (w : ↥gens) : num w ∈ A.grading U d
  /-- Each numerator dies in the quotient. -/
  num_zero (w : ↥gens) : P.hom.sectionHom U (num w) = 0
  /-- The generators generate the localized kernel. -/
  span_eq : Ideal.span (gens : Set (HomogeneousLocalization.Away (A.grading U)
      (f : A.sectionRing U))) =
    RingHom.ker (HomogeneousLocalization.Away.map (P.hom.sectionHom U) (f : A.sectionRing U))

/-- **The uniform degree on one chart.** Over an affine open of the base there is a positive
degree `D` and a family of positive-degree homogeneous sections covering the chart such that, in
every positive multiple of `D`, the localized kernel is generated by elements of that degree
dying in the quotient. -/
private theorem exists_uniform_degree_chart (A : SheafGradedAlgebra S) {Z : Scheme.{u}}
    {i : Z ⟶ (relativeProj A).scheme} [IsClosedImmersion i]
    [QuasiCompact (relativeProj A).toBase] (P : GradedQuotientPresentation A i)
    (hi : AlgebraicGeometry.LocallyOfFinitePresentation i) (U : S.affineOpens) :
    ∃ D : ℕ, 0 < D ∧ ∃ Sg : Finset (Σ n : ℕ, A.grading U.1 n),
      (∀ x ∈ Sg, 0 < x.1) ∧
      (⨆ x : ↥Sg, AlgebraicGeometry.Proj.basicOpen (A.grading U.1)
        (x.1.2 : A.sectionRing U.1)) = ⊤ ∧
      ∀ D' : ℕ, D ∣ D' → 0 < D' → ∀ x : ↥Sg,
        Nonempty (LocalKernelGenerators A P D' U.1 x.1.1 x.1.2) := by
  classical
  obtain ⟨tg, htgdeg, htgrad⟩ :=
    (AlgebraicGeometry.Proj.compactSpace_iff (A.grading U.1)).mp
      (compactSpace_proj_grading A U.1 U.2)
  obtain ⟨Sg, hSpos, hSsurj, -⟩ :=
    Stacks.RingTheory.UniformDegreeKernel.exists_homogeneous_finset_lift
      (A.grading U.1) tg htgdeg
  have hcov : (⨆ x : ↥Sg, AlgebraicGeometry.Proj.basicOpen (A.grading U.1)
      (x.1.2 : A.sectionRing U.1)) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← AlgebraicGeometry.Proj.iSup_basicOpen_eq_top_of_irrelevant_le_radical
      (A.grading U.1) tg htgrad]
    refine iSup₂_le fun f hf => ?_
    obtain ⟨x, hx, hxf⟩ := hSsurj f hf
    have hle := le_iSup (fun c : ↥Sg => AlgebraicGeometry.Proj.basicOpen (A.grading U.1)
      (c.1.2 : A.sectionRing U.1)) (⟨x, hx⟩ : ↥Sg)
    rwa [hxf] at hle
  obtain ⟨D, hDpos, hDdata⟩ :=
    Stacks.RingTheory.UniformDegreeKernel.exists_uniform_degree_kernel_generators_multiple
      (A.grading U.1) (P.target.grading U.1) (P.hom.sectionHom U.1) Sg hSpos
      (fun x hx => away_sectionHom_ker_fg P hi U.1 U.2 (x.2 : A.sectionRing U.1) x.1 x.2.2
        (hSpos x hx))
  refine ⟨D, hDpos, Sg, hSpos, hcov, fun D' hdvd hD'pos x => ?_⟩
  obtain ⟨e', hde', T, aa, haa, hphi, hmkk, hspan⟩ := hDdata D' hdvd hD'pos x
  have hdeg : ∀ w, aa w ∈ A.grading U.1 D' := by
    intro w
    have h1 := haa w
    have h2 : e' • x.1.1 = D' := by rw [hde']; simp
    rwa [h2] at h1
  exact ⟨{ exp := e', gens := T, num := aa, num_mem := haa, num_mk := hmkk,
           num_deg := hdeg, num_zero := hphi, span_eq := hspan }⟩

/-- **The uniform degree of Tag 0802.** There is one positive degree `d` and a finite cover of
the base by affine opens on each of whose charts the localized kernel has degree-`d`
generators. -/
private theorem exists_uniform_degree_cover (A : SheafGradedAlgebra S) {Z : Scheme.{u}}
    {i : Z ⟶ (relativeProj A).scheme} [CompactSpace S] [IsClosedImmersion i]
    [QuasiCompact (relativeProj A).toBase] (P : GradedQuotientPresentation A i)
    (hi : AlgebraicGeometry.LocallyOfFinitePresentation i) :
    ∃ d : ℕ, 0 < d ∧ ∃ BC : Finset S.affineOpens, (⨆ V : ↥BC, (V.1.1 : S.Opens)) = ⊤ ∧
      ∃ Sg : ∀ V : ↥BC, Finset (Σ n : ℕ, A.grading V.1.1 n),
        (∀ (V : ↥BC), ∀ x ∈ Sg V, 0 < x.1) ∧
        (∀ V : ↥BC, (⨆ x : ↥(Sg V), AlgebraicGeometry.Proj.basicOpen (A.grading V.1.1)
          (x.1.2 : A.sectionRing V.1.1)) = ⊤) ∧
        ∀ (V : ↥BC) (x : ↥(Sg V)),
          Nonempty (LocalKernelGenerators A P d V.1.1 x.1.1 x.1.2) := by
  classical
  have htopcompact : IsCompact ((⊤ : S.Opens) : Set S) := by
    rw [TopologicalSpace.Opens.coe_top]
    exact isCompact_univ
  obtain ⟨baseCover, hbcFin, hbc⟩ :=
    (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : S.Opens))).mp htopcompact
  have hcov : (⨆ V : ↥hbcFin.toFinset, (V.1.1 : S.Opens)) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [hbc]
    refine iSup₂_le fun W hW => ?_
    exact le_iSup (fun V : ↥hbcFin.toFinset => (V.1.1 : S.Opens))
      (⟨W, hbcFin.mem_toFinset.mpr hW⟩ : ↥hbcFin.toFinset)
  choose DD hDDpos Sgen hSpos hScov hDDdata using
    fun V : S.affineOpens => exists_uniform_degree_chart A P hi V
  obtain ⟨d, hdpos, hddvd⟩ := exists_common_positive_multiple
    (hbcFin.toFinset.image DD)
    (fun n hn => by obtain ⟨V, -, rfl⟩ := Finset.mem_image.mp hn; exact hDDpos V)
  exact ⟨d, hdpos, hbcFin.toFinset, hcov, fun V => Sgen V.1, fun V => hSpos V.1,
    fun V => hScov V.1,
    fun V x => hDDdata V.1 d (hddvd _ (Finset.mem_image_of_mem DD V.2)) hdpos x⟩

/-- **The degree and the finite type subobject of Tag 0802.** For a closed subscheme of finite
presentation of a quasi-compact relative Proj over a quasi-compact quasi-separated base there is
a positive degree `d` and a quasi-coherent subobject of finite type of the degree-`d` sectionwise
kernel which, together with every larger subobject, cuts the closed subscheme out on the
charts. -/
private theorem exists_degreeSubobject (A : SheafGradedAlgebra S) {Z : Scheme.{u}}
    {i : Z ⟶ (relativeProj A).scheme} [CompactSpace S] [QuasiSeparatedSpace S]
    [IsClosedImmersion i] [QuasiCompact (relativeProj A).toBase]
    (P : GradedQuotientPresentation A i)
    (hi : AlgebraicGeometry.LocallyOfFinitePresentation i) :
    ∃ d : ℕ, 0 < d ∧ ∃ G : Subobject (kernelModule A P.hom d),
      (G : S.Modules).IsQuasicoherent ∧
        SheafOfModules.IsFiniteType.{u, u, u} (G : S.Modules) ∧
          ∀ H : Subobject (kernelModule A P.hom d), G ≤ H →
            CutsOutOnCharts A (kernelSubobjectSubmodule A P.hom d H) P.hom := by
  classical
  obtain ⟨d, hdpos, BC, hcov, Sg, hSpos, hScov, hdata⟩ := exists_uniform_degree_cover A P hi
  let GG : ∀ (V : ↥BC) (x : ↥(Sg V)), LocalKernelGenerators A P d V.1.1 x.1.1 x.1.2 :=
    fun V x => (hdata V x).some
  have hKqc := isQuasicoherent_kernelModule A P.hom d
  have hsec : ∀ (V : ↥BC) (x : ↥(Sg V)) (w : ↥(GG V x).gens),
      ∃ κ : Γ(kernelModule A P.hom d, V.1.1),
        DirectSum.of (A.sectionPieces V.1.1) d ((kernelInclusion A P.hom d).app V.1.1 κ) =
          (GG V x).num w := by
    intro V x w
    obtain ⟨β, hβ⟩ := (GG V x).num_deg w
    obtain ⟨κ, hκ⟩ := (mem_range_kernelInclusion_app_iff A P.hom d V.1.1 β).mpr
      ((sectionHom_of_eq_zero_iff P.hom V.1.1 d β).mp (by rw [hβ]; exact (GG V x).num_zero w))
    exact ⟨κ, (congrArg (DirectSum.of (A.sectionPieces V.1.1) d) hκ).trans hβ⟩
  choose κ hκ using hsec
  obtain ⟨G, hGqc, hGft, hGsec⟩ :=
    @exists_finiteTypeSubobject_sections S _ _ (kernelModule A P.hom d) hKqc
      (BC.attach.biUnion fun V => (Sg V).attach.biUnion fun x =>
        (GG V x).gens.attach.image fun w =>
          (⟨V.1.1, κ V x w⟩ : (W : S.Opens) × Γ(kernelModule A P.hom d, W)))
      (by
        intro v hv
        obtain ⟨V, -, hv⟩ := Finset.mem_biUnion.mp hv
        obtain ⟨x, -, hv⟩ := Finset.mem_biUnion.mp hv
        obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hv
        exact V.1.2)
  refine ⟨d, hdpos, G, hGqc, hGft, fun H hGH => ?_⟩
  have hsections : ∀ (V : ↥BC) (x : ↥(Sg V)) (w : ↥(GG V x).gens),
      ∃ a ∈ (kernelSubobjectSubmodule A P.hom d H).toSubmodule.obj (op V.1.1),
        (GG V x).num w = DirectSum.of (A.sectionPieces V.1.1) d a := by
    intro V x w
    obtain ⟨a0, ha0⟩ := hGsec ⟨V.1.1, κ V x w⟩
      (Finset.mem_biUnion.mpr ⟨V, Finset.mem_attach _ _,
        Finset.mem_biUnion.mpr ⟨x, Finset.mem_attach _ _,
          Finset.mem_image.mpr ⟨w, Finset.mem_attach _ _, rfl⟩⟩⟩)
    refine ⟨(kernelInclusion A P.hom d).app V.1.1 (κ V x w), ?_, (hκ V x w).symm⟩
    rw [kernelSubobjectSubmodule_obj A P.hom d H V.1.1]
    exact ⟨(Subobject.ofLE G H hGH).val.app (op V.1.1) a0,
      (kernelInclusion_app_ofLE A P.hom d hGH V.1.1 a0).trans
        (congrArg ((kernelInclusion A P.hom d).val.app (op V.1.1)) ha0)⟩
  refine ⟨{ index := ↥BC
            cover := fun V => V.1.1
            isAffineOpen_cover := fun V => V.1.2
            iSup_cover := hcov
            chart := fun V =>
              { index := ↥(Sg V)
                elt := fun x => (x.1.2 : A.sectionRing V.1.1)
                deg := fun x => x.1.1
                deg_pos := fun x => hSpos V x.1 x.2
                elt_mem := fun x => x.1.2.2
                cover := hScov V
                ker_le := fun x => ?_ } }⟩
  rw [← (GG V x).span_eq]
  refine Ideal.span_le.mpr fun z hz => ?_
  have hzg : z ∈ (GG V x).gens := Finset.mem_coe.mp hz
  obtain ⟨a, hamem, haeq⟩ := hsections V x ⟨z, hzg⟩
  refine Ideal.subset_span ⟨(GG V x).exp, (GG V x).num ⟨z, hzg⟩,
    (GG V x).num_mem ⟨z, hzg⟩, ?_, ((GG V x).num_mk ⟨z, hzg⟩).symm⟩
  rw [haeq]
  exact Ideal.subset_span ⟨a, hamem, rfl⟩

/-- **The degree and the finite type submodule of Tag 0802.** For a closed subscheme of finite
presentation of a quasi-compact relative Proj over a quasi-compact quasi-separated base there is
a positive degree `d` and a quasi-coherent submodule of finite type of `𝒜_d`, consisting of
equations for the closed subscheme, which cuts it out on the charts. -/
private theorem exists_finiteType_cutsOutOnCharts (A : SheafGradedAlgebra S) {Z : Scheme.{u}}
    {i : Z ⟶ (relativeProj A).scheme} [CompactSpace S] [QuasiSeparatedSpace S]
    [IsClosedImmersion i] [QuasiCompact (relativeProj A).toBase]
    (P : GradedQuotientPresentation A i)
    (hi : AlgebraicGeometry.LocallyOfFinitePresentation i) :
    ∃ d : ℕ, 0 < d ∧ ∃ ℱ : (A.piece (d : ℤ)).Submodule,
      ℱ.toSheafOfModules.IsQuasicoherent ∧
        SheafOfModules.IsFiniteType.{u, u, u} ℱ.toSheafOfModules ∧
          IsEquationSubmodule A ℱ P.hom ∧ CutsOutOnCharts A ℱ P.hom := by
  obtain ⟨d, hdpos, G, hGqc, hGft, hcut⟩ := exists_degreeSubobject A P hi
  exact ⟨d, hdpos, kernelSubobjectSubmodule A P.hom d G,
    isQuasicoherent_kernelSubobjectSubmodule A P.hom d G hGqc,
    isFiniteType_kernelSubobjectSubmodule A P.hom d G hGft,
    isEquationSubmodule_kernelSubobjectSubmodule A P.hom d G, hcut G le_rfl⟩

/-! ### Tag 0802 -/

/-- **Tag 0802, with the relative case of Tag 0801 as an argument.** Given a graded-quotient
presentation of the closed subscheme, a closed subscheme of finite presentation of a quasi-compact
relative Proj over a quasi-compact quasi-separated base is the relative Proj of the quotient of
`𝒜` by the graded ideal generated by a quasi-coherent finite type submodule of a single
homogeneous piece `𝒜_d` with `d > 0`.

The single-degree form of Tag 0801 that the statement concludes with is *not* a second argument:
`…degreeQuotientPresenter_of_gradedQuotientPresentation` derives it from `P`.

The argument `P` is discharged downstream, by
`Stacks.AlgebraicGeometry.RelativeProjTwists.gradedQuotientPresentation`, and the registration of
Tag 0802 is on the resulting statement,
`Stacks.AlgebraicGeometry.RelativeProjTwists.exists_finiteType_degreeQuotientPresentation` in module
`StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.FiniteTypeDegreeQuotientPresentation`.
-/
public theorem exists_finiteType_degreeQuotientPresentation (A : SheafGradedAlgebra S)
    {Z : Scheme.{u}} (i : Z ⟶ (relativeProj A).scheme)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsClosedImmersion i]
    [QuasiCompact (relativeProj A).toBase]
    (hi : AlgebraicGeometry.FinitePresentation i)
    (P : GradedQuotientPresentation A i) :
    ∃ d : ℕ, 0 < d ∧ ∃ ℱ : (A.piece (d : ℤ)).Submodule,
      ℱ.toSheafOfModules.IsQuasicoherent ∧
        SheafOfModules.IsFiniteType.{u, u, u} ℱ.toSheafOfModules ∧
          Nonempty (DegreeQuotientPresentation A i ℱ) := by
  obtain ⟨d, hdpos, ℱ, hqc, hft, heq, hcut⟩ := exists_finiteType_cutsOutOnCharts A P hi.1
  exact ⟨d, hdpos, ℱ, hqc, hft,
    degreeQuotientPresenter_of_gradedQuotientPresentation A P d hdpos ℱ hqc heq hcut⟩


/-! ### Tag 0803 -/

/-- Over an open of the base that the closed subscheme misses, every homogeneous local section of
`𝒜` is an equation for it: this is Tag 0801's identification of the degreewise kernel with the
sections vanishing on the closed subscheme. -/
public def VanishesOver (A : SheafGradedAlgebra S) {Z : Scheme.{u}}
    {i : Z ⟶ (relativeProj A).scheme} (P : GradedQuotientPresentation A i) (U : S.Opens) :
    Prop :=
  ∀ (n : ℕ) (W : S.Opens), W ≤ U → ∀ a : Γ(A.piece (n : ℤ), W), (P.hom.app (n : ℤ)).app W a = 0

/-- **Tag 0801 as an input to Tag 0803.** The closed subscheme is the relative Proj of the
quotient of `𝒜` by a graded ideal `ℐ` containing the sections vanishing on it.

The single-degree form of Tag 0801 is *not* among the fields: it is derived from the `iso`
clause below by `…degreeQuotientPresenter_of_gradedQuotientPresentation`. -/
public structure VanishingIdealPresentation (A : SheafGradedAlgebra S) {Z : Scheme.{u}}
    (i : Z ⟶ (relativeProj A).scheme) where
  /-- The graded ideal of sections vanishing on the closed subscheme. -/
  ideal : GradedIdeal A
  /-- The homogeneous pieces of `𝒜/ℐ` are quasi-coherent. -/
  quotQc : IsQuasicoherentQuotPieces A ideal
  /-- `𝒜 ⟶ 𝒜/ℐ` is surjective on homogeneous sections over the affine opens of the base. -/
  surjective : ProjBundleSurjection.SurjectiveOnAffineSections (quotMk A ideal quotQc)
  /-- The closed subscheme is the relative Proj of `𝒜/ℐ`. -/
  iso : Z ≅ (relativeProj (quotSheafGradedAlgebra A ideal quotQc)).scheme
  /-- The identification is one over the ambient relative Proj. -/
  iso_comp : iso.hom ≫ ProjBundleSurjection.map surjective = i
  /-- The modules on the closed subscheme receiving the restricted homogeneous sections. -/
  restricted (n : ℕ) : Z.Modules
  /-- Restriction of the homogeneous sections of degree `n` to the closed subscheme. -/
  restriction (n : ℕ) : (A.piece (n : ℤ) : S.Modules) ⟶
    (Scheme.Modules.pushforward (i ≫ (relativeProj A).toBase)).obj (restricted n)
  /-- A homogeneous local section restricting to zero on the closed subscheme lies in `ℐ`. -/
  mem_ideal (n : ℕ) (W : S.Opens) (a : Γ(A.piece (n : ℤ), W)) :
    (restriction n).app W a = 0 → a ∈ (ideal.piece (n : ℤ)).toSubmodule.obj (op W)

/-- The graded quotient presentation carried by a vanishing-ideal presentation: the quotient
`𝒜/ℐ` and the quotient homomorphism `𝒜 ⟶ 𝒜/ℐ`. -/
public def VanishingIdealPresentation.toGradedQuotientPresentation {A : SheafGradedAlgebra S}
    {Z : Scheme.{u}} {i : Z ⟶ (relativeProj A).scheme} (P : VanishingIdealPresentation A i) :
    GradedQuotientPresentation A i where
  target := quotSheafGradedAlgebra A P.ideal P.quotQc
  hom := quotMk A P.ideal P.quotQc
  surjective := P.surjective
  iso := P.iso
  iso_comp := P.iso_comp

/-- Over an open of the base missing the image of the closed subscheme, every homogeneous local
section of `𝒜` is an equation for it: the restricted sections live over the empty open, so the
section lies in `ℐ` and already dies in the sectionwise quotient. -/
public theorem vanishesOver_of_disjoint_range (A : SheafGradedAlgebra S) {Z : Scheme.{u}}
    {i : Z ⟶ (relativeProj A).scheme} (P : VanishingIdealPresentation A i) (U : S.Opens)
    (hU : (U : Set S) ∩ Set.range (i ≫ (relativeProj A).toBase).base = ∅) :
    VanishesOver A P.toGradedQuotientPresentation U := by
  intro n W hW a
  have hmem := P.mem_ideal n W a
    (AlgebraicGeometry.Scheme.Modules.pushforward_app_eq_zero_of_disjoint_range _ _ W
      (Set.eq_empty_iff_forall_notMem.2 fun x hx =>
        Set.eq_empty_iff_forall_notMem.1 hU x ⟨hW hx.1, hx.2⟩) a)
  change (quotMkApp A P.ideal (n : ℤ)).app W a = 0
  rw [quotMkApp_app, (preQuotProj_app_eq_zero_iff A P.ideal (n : ℤ) W a).2 hmem]
  exact map_zero _

section Supp

variable {A : SheafGradedAlgebra S} {Z : Scheme.{u}} {i : Z ⟶ (relativeProj A).scheme}
  {U : S.Opens}

/-- Over an open the closed subscheme misses, every section of `𝒜_n` lies in the sectionwise
kernel. -/
private theorem mem_kernelSubmodule_of_vanishesOver (P : GradedQuotientPresentation A i)
    (hvan : VanishesOver A P U) (n : ℕ) {W : S.Opens} (hW : W ≤ U) (a : Γ(A.piece (n : ℤ), W)) :
    a ∈ (Stacks.Algebraization.kernelSubmodule (P.hom.app (n : ℤ))).toSubmodule.obj (op W) :=
  (AlgebraicGeometry.mem_kernelSubmodule_iff (P.hom.app (n : ℤ)) W a).mpr (hvan n W hW a)

/-- Over an open the closed subscheme misses, the inclusion of the sectionwise kernel is
bijective on sections. -/
private theorem isIso_kernelInclusion_app (P : GradedQuotientPresentation A i)
    (hvan : VanishesOver A P U) (n : ℕ) {W : S.Opens} (hW : W ≤ U) :
    IsIso ((kernelInclusion A P.hom n).app W) := by
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨fun a b hab => Subtype.ext hab, fun y => ?_⟩
  exact ⟨⟨y, mem_kernelSubmodule_of_vanishesOver P hvan n hW y⟩, rfl⟩

/-- A quasi-coherent subobject of finite type of the degree-`n` sectionwise kernel which is all
of it over an open the closed subscheme misses: the extension lemma Tag 01PF applied to the top
subobject of the restriction. -/
private theorem exists_subobject_full_over [CompactSpace S] [QuasiSeparatedSpace S]
    (P : GradedQuotientPresentation A i) (hUc : IsCompact (U : Set S))
    (hvan : VanishesOver A P U)
    (hA : ∀ n : ℕ, SheafOfModules.IsFiniteType.{u, u, u} (A.piece (n : ℤ))) (n : ℕ) :
    ∃ G : Subobject (kernelModule A P.hom n), (G : S.Modules).IsQuasicoherent ∧
      SheafOfModules.IsFiniteType.{u, u, u} (G : S.Modules) ∧
        ∀ W : S.Opens, W ≤ U → Function.Surjective (G.arrow.app W) := by
  have hKqc := isQuasicoherent_kernelModule A P.hom n
  have hresIso : IsIso ((Scheme.Modules.restrictFunctor U.ι).map (kernelInclusion A P.hom n)) :=
    AlgebraicGeometry.isIso_restrictFunctor_map_of_range_le _ U.ι (le_of_eq U.range_ι)
      fun W hW => isIso_kernelInclusion_app P hvan n hW
  have hpieceFt := hA n
  have hAres : SheafOfModules.IsFiniteType.{u, u, u} ((A.piece (n : ℤ)).restrict U.ι) :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_restrict U.ι (A.piece (n : ℤ))
  have hKres : SheafOfModules.IsFiniteType.{u, u, u} ((kernelModule A P.hom n).restrict U.ι) :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u} (@asIso _ _ _ _ _ hresIso).symm
  have hKresQc : ((kernelModule A P.hom n).restrict U.ι).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor U.ι _
  have htopqc : ((⊤ : Subobject ((kernelModule A P.hom n).restrict U.ι)) :
      U.toScheme.Modules).IsQuasicoherent :=
    (_root_.SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
      (asIso (⊤ : Subobject ((kernelModule A P.hom n).restrict U.ι)).arrow).symm hKresQc
  have htopft : SheafOfModules.IsFiniteType.{u, u, u}
      ((⊤ : Subobject ((kernelModule A P.hom n).restrict U.ι)) : U.toScheme.Modules) :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      (asIso (⊤ : Subobject ((kernelModule A P.hom n).restrict U.ι)).arrow).symm
  obtain ⟨G, hGqc, hGft, e, he⟩ :=
    @exists_finiteTypeQuasicoherentSubobject_extension S _ _ (kernelModule A P.hom n) hKqc
      U hUc (⊤ : Subobject ((kernelModule A P.hom n).restrict U.ι)) htopqc htopft
  refine ⟨G, hGqc, hGft, fun W hW => ?_⟩
  have hiso : IsIso ((Scheme.Modules.restrictFunctor U.ι).map G.arrow) := by
    rw [he]; infer_instance
  have h0 : IsIso (((Scheme.Modules.restrictFunctor U.ι).map G.arrow).app (U.ι ⁻¹ᵁ W)) :=
    have := hiso
    inferInstance
  have h1 : IsIso (G.arrow.app (U.ι ''ᵁ (U.ι ⁻¹ᵁ W))) := h0
  have himg : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hW]
  rw [himg] at h1
  have := h1
  exact (ConcreteCategory.bijective_of_isIso (G.arrow.app W)).surjective

/-- A quasi-coherent submodule which is all of a quasi-coherent module over an open has quotient
supported away from that open: the quotient has no nonzero sections over the affine opens inside
it, and those compute the germs there. -/
private theorem supp_cokernel_disjoint {M : S.Modules} (hM : M.IsQuasicoherent)
    (ℱ : M.Submodule) (hqc : ℱ.toSheafOfModules.IsQuasicoherent) (V : S.Opens)
    (hfull : ∀ W : S.Opens, W ≤ V → ∀ a : Γ(M, W), a ∈ ℱ.toSubmodule.obj (op W)) :
    (V : Set S) ∩ (⟨(cokernel ℱ.ι).val, (cokernel ℱ.ι).isSheaf⟩ :
        RingedSpace.ModuleSheaf.{u} S.toRingedSpace).supp = ∅ := by
  have := hM
  have := hqc
  have hqc' : (ℱ.toSheafOfModules : S.Modules).IsQuasicoherent := hqc
  have hmono : Mono ℱ.ι := inferInstanceAs (Mono ℱ.ι)
  have hck : (cokernel ℱ.ι).IsQuasicoherent :=
    @Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel S
      (ℱ.toSheafOfModules : S.Modules) M ℱ.ι hqc' hM
  have hzero : ∀ W : S.Opens, IsAffineOpen W → W ≤ V →
      ∀ t : Γ(cokernel ℱ.ι, W), t = 0 := by
    intro W hWaff hWV t
    obtain ⟨s, hs⟩ := @Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen S M
      (cokernel ℱ.ι) (cokernel.π ℱ.ι) hM hck (coequalizer.π_epi) W hWaff t
    rw [← hs]
    exact (AlgebraicGeometry.cokernel_π_val_app_eq_zero_iff ℱ.ι hmono W s).mpr
      ⟨⟨s, hfull W hWV s⟩, rfl⟩
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hxV, a, ha⟩
  refine ha ?_
  obtain ⟨W, hxW, s, hs⟩ :=
    (⟨(cokernel ℱ.ι).val, (cokernel ℱ.ι).isSheaf⟩ :
      RingedSpace.ModuleSheaf.{u} S.toRingedSpace).abPresheaf.exists_germ_eq a
  obtain ⟨-, ⟨W', hW'aff, rfl⟩, hxW', hW'sub⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ ((W ⊓ V : S.Opens) : Set S) from ⟨hxW, hxV⟩) (W ⊓ V).2
  have hW'W : W' ≤ W := le_trans hW'sub inf_le_left
  have hW'V : W' ≤ V := le_trans hW'sub inf_le_right
  rw [← hs, ← TopCat.Presheaf.germ_res_apply _ (homOfLE hW'W) x hxW' s]
  rw [show (⟨(cokernel ℱ.ι).val, (cokernel ℱ.ι).isSheaf⟩ :
        RingedSpace.ModuleSheaf.{u} S.toRingedSpace).abPresheaf.map
      (homOfLE hW'W).op s = 0 from hzero W' hW'aff hW'V _]
  exact map_zero _

end Supp

/-- The construction of Tag 0803 from a graded quotient presentation, a degree presenter and the
vanishing of every homogeneous local section over `U`. -/
private theorem exists_finiteType_presentation_supp_aux (A : SheafGradedAlgebra S)
    {Z : Scheme.{u}} (i : Z ⟶ (relativeProj A).scheme) (U : S.Opens)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsClosedImmersion i]
    [QuasiCompact (relativeProj A).toBase]
    (hi : AlgebraicGeometry.FinitePresentation i) (hUc : IsCompact (U : Set S))
    (hA : ∀ n : ℕ, SheafOfModules.IsFiniteType.{u, u, u} (A.piece (n : ℤ)))
    (P : GradedQuotientPresentation A i) (hvan : VanishesOver A P U)
    (hP : DegreeQuotientPresenter A i P.hom) :
    ∃ d : ℕ, 0 < d ∧ ∃ ℱ : (A.piece (d : ℤ)).Submodule,
      ℱ.toSheafOfModules.IsQuasicoherent ∧
        SheafOfModules.IsFiniteType.{u, u, u} ℱ.toSheafOfModules ∧
          (U : Set S) ∩ (⟨(cokernel ℱ.ι).val, (cokernel ℱ.ι).isSheaf⟩ :
              RingedSpace.ModuleSheaf.{u} S.toRingedSpace).supp = ∅ ∧
            Nonempty (DegreeQuotientPresentation A i ℱ) := by
  classical
  obtain ⟨d, hdpos, G, hGqc, hGft, hcut⟩ := exists_degreeSubobject A P hi.1
  obtain ⟨G', hG'qc, hG'ft, hG'surj⟩ := exists_subobject_full_over P hUc hvan hA d
  have hKqc := isQuasicoherent_kernelModule A P.hom d
  set T : Finset (FiniteTypeQuasicoherentSubobject (kernelModule A P.hom d)) :=
    {⟨G, hGqc, hGft⟩, ⟨G', hG'qc, hG'ft⟩} with hT
  set H := IsFiltered.sup T ∅
  have hGH : G ≤ H.1 :=
    leOfHom (IsFiltered.toSup T ∅ (by rw [hT]; exact Finset.mem_insert_self _ _)).hom
  have hG'H : G' ≤ H.1 :=
    leOfHom (IsFiltered.toSup T ∅
      (by rw [hT]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))).hom
  refine ⟨d, hdpos, kernelSubobjectSubmodule A P.hom d H.1,
    isQuasicoherent_kernelSubobjectSubmodule A P.hom d H.1 H.2.1,
    isFiniteType_kernelSubobjectSubmodule A P.hom d H.1 H.2.2, ?_,
    hP d hdpos _ (isQuasicoherent_kernelSubobjectSubmodule A P.hom d H.1 H.2.1)
      (isEquationSubmodule_kernelSubobjectSubmodule A P.hom d H.1) (hcut H.1 hGH)⟩
  refine supp_cokernel_disjoint (A.isQuasicoherent (d : ℤ)) _
    (isQuasicoherent_kernelSubobjectSubmodule A P.hom d H.1 H.2.1) U fun W hW a => ?_
  rw [kernelSubobjectSubmodule_obj A P.hom d H.1 W]
  obtain ⟨y, hy⟩ := (mem_range_kernelInclusion_app_iff A P.hom d W a).mpr (hvan d W hW a)
  obtain ⟨z, hz⟩ := hG'surj W hW y
  exact ⟨(Subobject.ofLE G' H.1 hG'H).val.app (op W) z,
    (kernelInclusion_app_ofLE A P.hom d hG'H W z).trans ((congrArg _ hz).trans hy)⟩

/-- **Tag 0803, with the relative case of Tag 0801 as an argument.** Given a vanishing-ideal
presentation of the closed subscheme, a quasi-compact open `U` of the base missing its image, and
every `𝒜_n` of finite type, the submodule of Tag 0802 may be chosen so that the support of
`𝒜_d/ℱ` is disjoint from `U`.

The argument `hZ` is discharged downstream, by
`Stacks.AlgebraicGeometry.RelativeProjTwists.vanishingIdealPresentation`, and the registration of
Tag 0803 is on the resulting statement,
`Stacks.AlgebraicGeometry.RelativeProjTwists.exists_finiteType_presentation_supp` in
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/FiniteTypePresentationOffSupport.lean`. -/
public theorem exists_finiteType_presentation_supp_of_vanishingIdeal (A : SheafGradedAlgebra S)
    {Z : Scheme.{u}} (i : Z ⟶ (relativeProj A).scheme) (U : S.Opens)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsClosedImmersion i]
    [QuasiCompact (relativeProj A).toBase]
    (hi : AlgebraicGeometry.FinitePresentation i)
    (hU : (U : Set S) ∩ Set.range (i ≫ (relativeProj A).toBase).base = ∅)
    (hUc : IsCompact (U : Set S))
    (hA : ∀ n : ℕ, SheafOfModules.IsFiniteType.{u, u, u} (A.piece (n : ℤ)))
    (hZ : Nonempty (VanishingIdealPresentation A i)) :
    ∃ d : ℕ, 0 < d ∧ ∃ ℱ : (A.piece (d : ℤ)).Submodule,
      ℱ.toSheafOfModules.IsQuasicoherent ∧
        SheafOfModules.IsFiniteType.{u, u, u} ℱ.toSheafOfModules ∧
          (U : Set S) ∩ (⟨(cokernel ℱ.ι).val, (cokernel ℱ.ι).isSheaf⟩ :
              RingedSpace.ModuleSheaf.{u} S.toRingedSpace).supp = ∅ ∧
            Nonempty (DegreeQuotientPresentation A i ℱ) := by
  obtain ⟨Q⟩ := hZ
  exact exists_finiteType_presentation_supp_aux A i U hi hUc hA Q.toGradedQuotientPresentation
    (vanishesOver_of_disjoint_range A Q U hU)
    (degreeQuotientPresenter_of_gradedQuotientPresentation A Q.toGradedQuotientPresentation)

/-- **The construction behind Stacks Project, Tag 0803.** For a graded-quotient presentation of
the closed subscheme, a degree presenter for it and an open `U` of the base over which every
homogeneous local section of `𝒜` is an equation, the submodule of Tag 0802 may be chosen so that
the support of `𝒜_d/ℱ` is disjoint from `U`.

Tag 0803 itself is
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.exists_finiteType_presentation_supp` of
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/DegreePresenter.lean`, which supplies the
presentation, the presenter and the vanishing from the tag's own hypotheses. This is the step of
the source's proof that enlarges the submodule of Tag 0802 until it generates `𝒜_d` over `U`;
the three arguments it takes are what that step uses and no more, which is why they are stated
here rather than reconstructed. -/
public theorem exists_finiteType_presentation_supp_of_presenter (A : SheafGradedAlgebra S)
    {Z : Scheme.{u}} (i : Z ⟶ (relativeProj A).scheme) (U : S.Opens)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsClosedImmersion i]
    [QuasiCompact (relativeProj A).toBase]
    (hi : AlgebraicGeometry.FinitePresentation i)
    (_hU : (U : Set S) ∩ Set.range (i ≫ (relativeProj A).toBase).base = ∅)
    (hUc : IsCompact (U : Set S))
    (hA : ∀ n : ℕ, SheafOfModules.IsFiniteType.{u, u, u} (A.piece (n : ℤ)))
    (P : GradedQuotientPresentation A i)
    (hvan : VanishesOver A P U)
    (hP : DegreeQuotientPresenter A i P.hom) :
    ∃ d : ℕ, 0 < d ∧ ∃ ℱ : (A.piece (d : ℤ)).Submodule,
      ℱ.toSheafOfModules.IsQuasicoherent ∧
        SheafOfModules.IsFiniteType.{u, u, u} ℱ.toSheafOfModules ∧
          (U : Set S) ∩ (⟨(cokernel ℱ.ι).val, (cokernel ℱ.ι).isSheaf⟩ :
              RingedSpace.ModuleSheaf.{u} S.toRingedSpace).supp = ∅ ∧
            Nonempty (DegreeQuotientPresentation A i ℱ) := by
  exact exists_finiteType_presentation_supp_aux A i U hi hUc hA P hvan hP

end Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

end
