/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.IsomQuasiCompactOfHilbertBound
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveHilbertModelReading
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeMorphismsOpenInHilbert
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange

/-!
# The graph of a relative morphism, read as a closed subscheme of `ℙᴺ_T`

Let `q₁ : Z₁ ⟶ U` and `q₂ : Z₂ ⟶ U` be morphisms of the big fppf site over `Spec ℤ` and let
`i' : Z₁ ×_U Z₂ ⟶ ℙᴺ_U` be a closed immersion over `U`. A relative morphism `(a, b)` over a scheme
`T` — `a : T ⟶ U` and `b : (Z₁)_T ⟶ Z₂` over `U` — has a graph in `(Z₁ ×_U Z₂)_T`, and its image
in `(ℙᴺ_U)_T ≅ ℙᴺ_T` is the image of a closed immersion of schemes
`j : (Z₁)_T ⟶ ℙᴺ_T`: the graph `(Z₁)_T ⟶ (Z₁ ×_U Z₂)_T` followed by the base change of `i'`. This
file builds `j`, identifies its image with the image family of the graph in the Hilbert functor
of `ℙᴺ_U ⟶ U`, and shows that `j` followed by `ℙᴺ_T ⟶ ℙᴺ_U` is `(id, b) ≫ i'`.

## Main definitions

* `AlgebraicGeometry.ProjectiveCurveGraphHilbert.graphEmbedding`: the closed immersion `i'` read
  on the algebraic spaces of the graph construction.
* `AlgebraicGeometry.ProjectiveCurveGraphHilbert.graphClosedMap`: the closed immersion `j`.

## References

* [Stacks Project, Tag 0D1A](https://stacks.math.columbia.edu/tag/0D1A)
* [Stacks Project, Tag 0DPF](https://stacks.math.columbia.edu/tag/0DPF)
* [Stacks Project, Tag 0DSQ](https://stacks.math.columbia.edu/tag/0DSQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local implicit_reducible] AlgebraicGeometry.schemeSpace

universe u

namespace AlgebraicGeometry.ProjectiveCurveGraphHilbert

open Space C1590Private ProjectiveQuot ProjectiveQuotOverSpace ProjectiveHilbertModelReading

variable {B : BigFppfSite.{u}}

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

variable {U Z₁ Z₂ : BigFppfOver B integerBase B.contains_integerBase} (q₁ : Z₁ ⟶ U) (q₂ : Z₂ ⟶ U)
  {N : ℕ} (i' : pullback q₁ q₂ ⟶ projectiveSite B N U)

/-- The closed immersion `i'`, read on the ambient space of the graph construction. -/
def graphEmbedding :
    graphAmbient B integerBase B.contains_integerBase (yoneda.map q₁) (yoneda.map q₂)
      (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase Z₁)
      (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase Z₂)
      (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase U) ⟶
      schemeSpace (projectiveSite B N U) :=
  ObjectProperty.homMk ((PreservesPullback.iso yoneda q₁ q₂).inv ≫ yoneda.map i')

variable {q₁ q₂ i'}

/-- If `i'` lies over `U`, then `graphEmbedding` followed by the structure morphism of `ℙᴺ_U` is
the structure morphism of the graph ambient space. -/
theorem graphEmbedding_comp (hi' : i' ≫ projectiveSiteStructure B N U = pullback.snd q₁ q₂ ≫ q₂) :
    graphEmbedding q₁ q₂ i' ≫ schemeSpaceMap (projectiveSiteStructure B N U) =
      graphAmbientMap B integerBase B.contains_integerBase (yoneda.map q₁) (yoneda.map q₂)
        (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase Z₁)
        (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase Z₂)
        (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase U) := by
  apply ObjectProperty.hom_ext
  change (PreservesPullback.iso yoneda q₁ q₂).inv ≫ yoneda.map i' ≫
      yoneda.map (projectiveSiteStructure B N U) =
    pullback.fst (yoneda.map q₁) (yoneda.map q₂) ≫ yoneda.map q₁
  rw [← Functor.map_comp, hi', Functor.map_comp, ← Category.assoc,
    PreservesPullback.iso_inv_snd]
  exact pullback.condition.symm

/-- If `i'` is a closed immersion of schemes, then `graphEmbedding` is a closed immersion of
algebraic spaces. -/
theorem isClosedImmersion_graphEmbedding (hi'c : IsClosedImmersion ((𝒯).map i')) :
    Space.IsClosedImmersion B integerBase B.contains_integerBase
      (graphEmbedding q₁ q₂ i').hom :=
  MorphismProperty.RespectsIso.precomp _ (PreservesPullback.iso yoneda q₁ q₂).inv _
    (Space.presheaf_yoneda_map_of_inverseImage B integerBase B.contains_integerBase
      inferInstance i' hi'c)

section Graph

variable {T : BigFppfOver B integerBase B.contains_integerBase}
  (p : RelativeMorphism B integerBase B.contains_integerBase (yoneda.obj Z₁) (yoneda.obj Z₂)
    (yoneda.obj U) (yoneda.map q₁) (yoneda.map q₂) (yoneda.obj T))

/-- The morphism `a : T ⟶ U` of a relative morphism `(a, b)`. -/
def graphBase : T ⟶ U := yoneda.preimage p.base

/-- The image of `graphBase p` under the Yoneda embedding is `p.base`. -/
theorem yoneda_map_graphBase : yoneda.map (graphBase p) = p.base := yoneda.map_preimage _

/-- The base change `(Z₁)_T`, as an object of the site, is the presheaf base change. -/
def graphSourceIso : yoneda.obj (pullback (graphBase p) q₁) ≅ pullback p.base (yoneda.map q₁) :=
  PreservesPullback.iso yoneda (graphBase p) q₁ ≪≫
    pullback.congrHom (yoneda_map_graphBase p) rfl

/-- The test scheme `T ⟶ U` of the relative morphism, as a scheme over the base of the Quot
situation of `𝒪_{ℙᴺ_U}/ℙᴺ_U/U`. -/
abbrev graphTestScheme : SchemesOver (projectiveSpaceQuotSituation N U).Y :=
  structureSheafTestScheme (CostructuredArrow.mk p.base)

/-- `h_{ℙᴺ_T} ≅ (ℙᴺ_U)_T`, stated with `T` itself as the base of `ℙᴺ_T`. -/
def graphSpaceIso : schemeSpace (projectiveSite B N T) ≅
    (projectiveSpaceQuotSituation N U).space (graphTestScheme p) :=
  spaceIso (projectiveSpaceFrame N U) (graphTestScheme p)

/-- `h_{ℙᴺ_T} ≅ (ℙᴺ_U)_T` followed by the projection `(ℙᴺ_U)_T ⟶ T` is the structure morphism of
`ℙᴺ_T`. -/
@[reassoc]
theorem graphSpaceIso_hom_projection :
    (graphSpaceIso (N := N) p).hom ≫ (projectiveSpaceQuotSituation N U).projection
      (graphTestScheme p) = schemeSpaceMap (projectiveSiteStructure B N T) :=
  spaceIso_hom_projection (projectiveSpaceFrame N U) (graphTestScheme p)

/-- `h_{ℙᴺ_T} ≅ (ℙᴺ_U)_T` followed by the projections to `ℙᴺ_U` and then to `ℙᴺ` over the base is
the morphism of projective spaces over the morphism from `T` to the base of the site. -/
theorem graphSpaceIso_hom_sourceProjection_toProjective :
    (graphSpaceIso (N := N) p).hom ≫ (projectiveSpaceQuotSituation N U).sourceProjection
      (graphTestScheme p) ≫ (projectiveSpaceFrame N U).toProjective =
        schemeSpaceMap (projectiveSiteMap B N (toSiteBase B T)) :=
  spaceIso_hom_sourceProjection_toProjective (projectiveSpaceFrame N U) (graphTestScheme p)

/-- The underlying presheaf morphism of `graphSpaceIso` is that of `spaceIso'`. -/
theorem graphSpaceIso_hom_hom :
    (graphSpaceIso (N := N) p).hom.hom =
      (spaceIso' (projectiveSpaceFrame N U) (graphTestScheme p)).hom.hom := rfl

variable (hi' : i' ≫ projectiveSiteStructure B N U = pullback.snd q₁ q₂ ≫ q₂)
  (hi'c : IsClosedImmersion ((BigFppfOver.toScheme B integerBase B.contains_integerBase).map i'))

/-- The graph of the relative morphism followed by the base change of `i'`, read on `(Z₁)_T`. -/
def graphSpaceMap :
    yoneda.obj (pullback (graphBase p) q₁) ⟶ ((projectiveSpaceQuotSituation N U).space
      (graphTestScheme p)).obj :=
  (graphSourceIso p).hom ≫ graphMap p ≫
    schemeBaseChangeOfMap (graphEmbedding_comp hi') (CostructuredArrow.mk p.base)

/-- **The closed immersion `j : (Z₁)_T ⟶ ℙᴺ_T` whose image is the graph.** -/
def graphClosedMap : pullback (graphBase p) q₁ ⟶ projectiveSite B N T :=
  yoneda.preimage (graphSpaceMap p hi' ≫
    (spaceIso' (projectiveSpaceFrame N U) (graphTestScheme p)).inv.hom)

/-- `graphClosedMap` followed by `ℙᴺ_T ≅ (ℙᴺ_U)_T` is `graphSpaceMap`. -/
theorem graphClosedMap_spaceIso :
    yoneda.map (graphClosedMap p hi') ≫
        (spaceIso' (projectiveSpaceFrame N U) (graphTestScheme p)).hom.hom =
      graphSpaceMap p hi' := by
  rw [graphClosedMap, yoneda.map_preimage, Category.assoc]
  change _ ≫ ((spaceIso' (projectiveSpaceFrame N U) (graphTestScheme p)).inv ≫
    (spaceIso' (projectiveSpaceFrame N U) (graphTestScheme p)).hom).hom = _
  rw [Iso.inv_hom_id]
  exact Category.comp_id _

variable (hsep : Space.IsSeparated B integerBase B.contains_integerBase (yoneda.map q₂))
  (hfp : Space.IsFinitePresentation B integerBase B.contains_integerBase (yoneda.map q₁))
  (hflat : Space.IsFlat B integerBase B.contains_integerBase (yoneda.map q₁))
  (hproper : Space.IsProper B integerBase B.contains_integerBase (yoneda.map q₁))

/-- **The image of `j` is the image of the graph in the Hilbert functor of `ℙᴺ_U ⟶ U`.** -/
theorem range_graphSpaceMap :
    Subfunctor.range (graphSpaceMap p hi') =
      (hilbertFamilyImageOfClosed (graphEmbedding_comp hi') (isClosedImmersion_graphEmbedding hi'c)
        (CostructuredArrow.mk p.base)
        (graphHilbertFamily (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase Z₁)
          (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase Z₂)
          (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase U) p hsep hfp hflat
          hproper)).Z := by
  change Subfunctor.range ((graphSourceIso p).hom ≫ graphMap p ≫ _) =
    (Subfunctor.range (graphMap p)).image _
  rw [Subfunctor.range_comp, Subfunctor.range_eq_top (p := (graphSourceIso p).hom),
    Subfunctor.image_top]
  exact Subfunctor.range_comp _ _

include hi'c hsep in
/-- `j` is a closed immersion. -/
theorem isClosedImmersion_graphClosedMap :
    IsClosedImmersion ((𝒯).map (graphClosedMap p hi')) := by
  have hg : Space.IsClosedImmersion B integerBase B.contains_integerBase (graphMap p) := by
    have h := MorphismProperty.RespectsIso.precomp
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) (𝒯)))
      (Subfunctor.toRange (graphMap p)) _ (isClosedSubspace_range_graphMap
        (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase Z₁)
        (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase U) p hsep).2
    rwa [Subfunctor.toRange_ι] at h
  have hG : Space.IsClosedImmersion B integerBase B.contains_integerBase
      (graphSpaceMap p hi') :=
    MorphismProperty.RespectsIso.precomp _ (graphSourceIso p).hom _
      (Space.isClosedImmersion_comp B integerBase B.contains_integerBase _ _ hg
        (isClosedImmersion_schemeBaseChangeOfMap (graphEmbedding_comp hi')
          (isClosedImmersion_graphEmbedding hi'c) (CostructuredArrow.mk p.base)))
  have hj : Space.IsClosedImmersion B integerBase B.contains_integerBase
      (yoneda.map (graphClosedMap p hi')) := by
    rw [graphClosedMap, yoneda.map_preimage]
    exact MorphismProperty.RespectsIso.postcomp _ _ _ hG
  have : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (𝒯)).IsStableUnderBaseChange :=
    ⟨fun hsq hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @AlgebraicGeometry.IsClosedImmersion) (hsq.map (𝒯)) hg⟩
  exact (MorphismProperty.relative_map_iff (F := yoneda)
    (P := MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) (𝒯))).mp hj

/-- `h_{ℙᴺ_T} ≅ (ℙᴺ_U)_T` followed by the projection to `ℙᴺ_U` is the morphism of projective
spaces over `a : T ⟶ U`. -/
theorem spaceIso_hom_sourceProjection :
    (graphSpaceIso (N := N) p).hom ≫
        (projectiveSpaceQuotSituation N U).sourceProjection (graphTestScheme p) =
      schemeSpaceMap (projectiveSiteMap B N (graphBase p)) := by
  refine (projectiveSpaceFrame N U).isPullback.hom_ext ?_ ?_
  · rw [Category.assoc, graphSpaceIso_hom_sourceProjection_toProjective]
    change _ = schemeSpaceMap (projectiveSiteMap B N (graphBase p)) ≫
      schemeSpaceMap (projectiveSiteMap B N (toSiteBase B U))
    refine ObjectProperty.hom_ext _ ?_
    change yoneda.map _ = yoneda.map _ ≫ yoneda.map _
    rw [← Functor.map_comp, ← projectiveSiteMap_comp]
    exact congrArg (fun k => yoneda.map (projectiveSiteMap B N k))
      ((isTerminal_siteBase B).hom_ext _ _)
  · have hT : (graphTestScheme (N := N) p).hom = schemeSpaceMap (graphBase p) :=
      ObjectProperty.hom_ext _ (yoneda_map_graphBase p).symm
    have hsq : IsPullback ((projectiveSpaceQuotSituation N U).sourceProjection (graphTestScheme p))
        ((projectiveSpaceQuotSituation N U).projection (graphTestScheme p))
        (projectiveSpaceQuotSituation N U).f (graphTestScheme p).hom :=
      AlgebraicSpaces.isPullback_fiberProduct B integerBase B.contains_integerBase _ _
    rw [Category.assoc, hsq.w, ← Category.assoc, graphSpaceIso_hom_projection, hT]
    change schemeSpaceMap (projectiveSiteStructure B N T) ≫ schemeSpaceMap (graphBase p) =
      schemeSpaceMap (projectiveSiteMap B N (graphBase p)) ≫
        schemeSpaceMap (projectiveSiteStructure B N U)
    rw [← AlgebraicGeometry.schemeSpaceMap_comp, ← AlgebraicGeometry.schemeSpaceMap_comp,
      (isPullback_projectiveSite B N (graphBase p)).w]

/-- `h_{ℙᴺ_T} ≅ (ℙᴺ_U)_T` as an isomorphism of presheaves, with `(ℙᴺ_U)_T` written as the fibre
product it is. -/
def graphSpaceIsoPresheaf : yoneda.obj (projectiveSite B N T) ≅
    pullback (schemeSpaceMap (projectiveSiteStructure B N U)).hom
      (CostructuredArrow.mk (S := yoneda) (T := (schemeSpace U).obj) p.base).hom where
  hom := (graphSpaceIso (N := N) p).hom.hom
  inv := (graphSpaceIso (N := N) p).inv.hom
  hom_inv_id := congrArg (fun k => k.hom) (graphSpaceIso (N := N) p).hom_inv_id
  inv_hom_id := congrArg (fun k => k.hom) (graphSpaceIso (N := N) p).inv_hom_id

/-- `graphSpaceIsoPresheaf` followed by the first projection is the morphism `ℙᴺ_T ⟶ ℙᴺ_U` over
`a : T ⟶ U`. -/
theorem graphSpaceIsoPresheaf_hom_fst :
    (graphSpaceIsoPresheaf (N := N) p).hom ≫ pullback.fst _ _ =
      yoneda.map (projectiveSiteMap B N (graphBase p)) :=
  congrArg (fun k => k.hom) (spaceIso_hom_sourceProjection (N := N) p)

/-- `graphSpaceIsoPresheaf` followed by the second projection is the structure morphism
`ℙᴺ_T ⟶ T`. -/
theorem graphSpaceIsoPresheaf_hom_snd :
    (graphSpaceIsoPresheaf (N := N) p).hom ≫ pullback.snd _ _ =
      yoneda.map (projectiveSiteStructure B N T) :=
  congrArg (fun k => k.hom) (graphSpaceIso_hom_projection (N := N) p)

/-- `graphSpaceMap`, with its target written as the fibre product. -/
abbrev graphSpaceMap' : yoneda.obj (pullback (graphBase p) q₁) ⟶
    pullback (schemeSpaceMap (projectiveSiteStructure B N U)).hom
      (CostructuredArrow.mk (S := yoneda) (T := (schemeSpace U).obj) p.base).hom :=
  (graphSourceIso p).hom ≫ graphMap p ≫
    schemeBaseChangeOfMap (graphEmbedding_comp hi') (CostructuredArrow.mk p.base)

/-- `graphClosedMap` followed by `graphSpaceIsoPresheaf` is `graphSpaceMap'`. -/
theorem graphClosedMap_isoPresheaf :
    yoneda.map (graphClosedMap p hi') ≫ (graphSpaceIsoPresheaf (N := N) p).hom =
      graphSpaceMap' p hi' :=
  graphClosedMap_spaceIso p hi'

/-- `j` lies over `T`: followed by `ℙᴺ_T ⟶ T` it is the projection `(Z₁)_T ⟶ T`. -/
theorem graphClosedMap_comp_structure :
    graphClosedMap p hi' ≫ projectiveSiteStructure B N T = pullback.fst (graphBase p) q₁ := by
  apply yoneda.map_injective
  rw [Functor.map_comp, ← graphSpaceIsoPresheaf_hom_snd (N := N) p, ← Category.assoc,
    graphClosedMap_isoPresheaf, graphSpaceMap', Category.assoc]
  refine (congrArg ((graphSourceIso p).hom ≫ ·) ((Category.assoc _ _ _).trans
    ((congrArg (graphMap p ≫ ·) (schemeBaseChangeOfMap_snd _ _)).trans (graphMap_snd p)))).trans ?_
  simp only [graphSourceIso, Iso.trans_hom, Category.assoc, pullback.congrHom_hom,
    pullback.lift_fst, Category.comp_id, PreservesPullback.iso_hom_fst]

/-- The pair `((Z₁)_T ⟶ Z₁, b) : (Z₁)_T ⟶ Z₁ ×_U Z₂` of the relative morphism. -/
def graphPairMap : pullback (graphBase p) q₁ ⟶ pullback q₁ q₂ :=
  yoneda.preimage ((graphSourceIso p).hom ≫
    pullback.lift (pullback.snd p.base (yoneda.map q₁)) p.morphism p.commutes.symm ≫
      (PreservesPullback.iso yoneda q₁ q₂).inv)

/-- **`j` followed by `ℙᴺ_T ⟶ ℙᴺ_U` is `((Z₁)_T ⟶ Z₁, b)` followed by `i'`.** -/
theorem graphClosedMap_comp_projectiveSiteMap :
    graphClosedMap p hi' ≫ projectiveSiteMap B N (graphBase p) = graphPairMap p ≫ i' := by
  apply yoneda.map_injective
  rw [Functor.map_comp, ← graphSpaceIsoPresheaf_hom_fst (N := N) p, ← Category.assoc,
    graphClosedMap_isoPresheaf, graphSpaceMap', Category.assoc]
  refine (congrArg ((graphSourceIso p).hom ≫ ·) ((Category.assoc _ _ _).trans
    ((congrArg (graphMap p ≫ ·) (schemeBaseChangeOfMap_fst _ _)).trans
      (pullback.lift_fst_assoc _ _ _ _)))).trans ?_
  rw [Functor.map_comp, graphPairMap, yoneda.map_preimage]
  simp only [Category.assoc]
  rfl

/-- `graphPairMap` followed by the projection to `Z₂` is `b`, read through `graphSourceIso`. -/
theorem yoneda_map_graphPairMap_snd :
    yoneda.map (graphPairMap p ≫ pullback.snd q₁ q₂) = (graphSourceIso p).hom ≫ p.morphism := by
  rw [Functor.map_comp, graphPairMap, yoneda.map_preimage]
  simp only [Category.assoc, PreservesPullback.iso_inv_snd, pullback.lift_snd]

/-- `graphPairMap` followed by the projection to `Z₁` is the projection `(Z₁)_T ⟶ Z₁`. -/
theorem graphPairMap_fst : graphPairMap p ≫ pullback.fst q₁ q₂ = pullback.snd (graphBase p) q₁ := by
  apply yoneda.map_injective
  rw [Functor.map_comp, graphPairMap, yoneda.map_preimage]
  simp only [Category.assoc, PreservesPullback.iso_inv_fst, pullback.lift_fst, graphSourceIso,
    Iso.trans_hom, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
    PreservesPullback.iso_hom_snd]

/-- The base change `(Z₂)_T`, as an object of the site, is the presheaf base change. -/
def graphTargetIso : yoneda.obj (pullback (graphBase p) q₂) ≅ pullback p.base (yoneda.map q₂) :=
  PreservesPullback.iso yoneda (graphBase p) q₂ ≪≫
    pullback.congrHom (yoneda_map_graphBase p) rfl

/-- **A relative isomorphism `(a, b)` identifies `(Z₁)_T` with `(Z₂)_T` over `T`.** -/
def graphPairIso (hp : p.IsRelativeIso) : pullback (graphBase p) q₁ ≅ pullback (graphBase p) q₂ :=
  haveI : IsIso p.baseChangeMap := hp
  yoneda.preimageIso ((graphSourceIso p) ≪≫ asIso p.baseChangeMap ≪≫ (graphTargetIso p).symm)

/-- The image of `graphPairIso` under the Yoneda embedding is the base change map of the relative
morphism, read through `graphSourceIso` and `graphTargetIso`. -/
theorem yoneda_map_graphPairIso_hom (hp : p.IsRelativeIso) :
    yoneda.map (graphPairIso p hp).hom =
      (graphSourceIso p).hom ≫ p.baseChangeMap ≫ (graphTargetIso p).inv := by
  rw [graphPairIso, Functor.preimageIso_hom, yoneda.map_preimage]
  rfl

/-- `graphPairIso` followed by the projection `(Z₂)_T ⟶ Z₂` is `b`. -/
theorem graphPairIso_hom_snd (hp : p.IsRelativeIso) :
    (graphPairIso p hp).hom ≫ pullback.snd (graphBase p) q₂ =
      graphPairMap p ≫ pullback.snd q₁ q₂ := by
  apply yoneda.map_injective
  rw [Functor.map_comp, yoneda_map_graphPairMap_snd, yoneda_map_graphPairIso_hom]
  simp only [Category.assoc, graphTargetIso, Iso.trans_inv, pullback.congrHom_inv,
    PreservesPullback.iso_inv_snd, pullback.lift_snd, Category.comp_id,
    RelativeMorphism.baseChangeMap_comp_snd]

/-- `graphPairIso` lies over `T`: followed by `(Z₂)_T ⟶ T` it is the projection `(Z₁)_T ⟶ T`. -/
theorem graphPairIso_hom_fst (hp : p.IsRelativeIso) :
    (graphPairIso p hp).hom ≫ pullback.fst (graphBase p) q₂ = pullback.fst (graphBase p) q₁ := by
  apply yoneda.map_injective
  rw [Functor.map_comp, yoneda_map_graphPairIso_hom]
  simp only [Category.assoc, graphTargetIso, Iso.trans_inv, pullback.congrHom_inv,
    PreservesPullback.iso_inv_fst, pullback.lift_fst, RelativeMorphism.baseChangeMap_comp_fst,
    graphSourceIso, Iso.trans_hom, pullback.congrHom_hom, PreservesPullback.iso_hom_fst,
    Category.comp_id]

end Graph

end AlgebraicGeometry.ProjectiveCurveGraphHilbert

end
