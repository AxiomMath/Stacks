module

public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationAtlasRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSiteObject

/-!
# The normalizations of an étale presentation form an étale equivalence relation

Let `F` be a presheaf on the big fppf site of `S`, let `w : h_U ⟶ F` be an étale chart of `F`
and let `pr₁, pr₂ : R ⟶ U` exhibit `R` as the self-fibre-product `U ×_F U`. The normalizations
`U^ν` and `R^ν` of `StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSiteObject` are then
related by the two morphisms induced by the projections, and this file proves that those two
morphisms are an *étale equivalence relation* of schemes over `S` in the sense of Tag 02WS, so
that Tag 02WW applies to its quotient sheaf.

This is the absolute-normalization counterpart of
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationAtlasRelation`. The structural morphisms of
the relation `R = U ×_F U` — the diagonal, the swap and the composition of the triple fibre
product — involve no normalization and are those of that module.

## Main definitions

* `AlgebraicGeometry.Space.NormSpaceGluing.normRelFst` and
  `AlgebraicGeometry.Space.NormSpaceGluing.normRelSnd` are the two morphisms `R^ν ⇉ U^ν` which
  the projections induce.

## Main results

* `AlgebraicGeometry.Space.NormSpaceGluing.isPullback_normRel₂`: the normalization of `R ×_U R`
  is the fibre product of two copies of that of `R` over that of `U`.
* `AlgebraicGeometry.Space.NormSpaceGluing.equivalenceRelation_normRel`: the two morphisms form
  an internal equivalence relation of presheaves.
* `AlgebraicGeometry.Space.NormSpaceGluing.isEtaleEquivalenceRelation_normRel`: they form an
  étale equivalence relation over `S`.

## Implementation notes

The normalization of an algebraic space is functorial only in the morphisms which carry generic
points to generic points, unlike the relative normalization of Tag 035J, which is functorial in
every morphism of charts. All seven morphisms of the relation do carry generic points to generic
points, and for a reason which is uniform: each of them is a morphism over `U` whose composite
with the étale `pr₁` carries generic points to generic points, and an étale morphism *reflects*
generic points (`AlgebraicGeometry.mem_genericPoints_of_etale`). That is
`AlgebraicGeometry.Space.NormSpaceGluing.mem_genericPoints_of_comp_etale` below, and it is what
replaces the unconditional functoriality the relative case enjoys.

Every identity between morphisms of normalizations is an instance of rigidity,
`AlgebraicGeometry.Space.normSpace_hom_ext`: two such morphisms over the same morphism of the
bases agree. No computation with normalizations occurs.

## References

* [Stacks Project, Tag 02WS](https://stacks.math.columbia.edu/tag/02WS)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 035Q](https://stacks.math.columbia.edu/tag/035Q)
* [Stacks Project, Tag 07TD](https://stacks.math.columbia.edu/tag/07TD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space.NormSpaceGluing

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An étale morphism reflects generic points.** If `g : A ⟶ C` is a morphism of the site
over an étale `p : C ⟶ D` whose composite carries generic points to generic points, then so
does `g`. -/
lemma mem_genericPoints_of_comp_etale {A C D : BigFppfOver B S hS} (g : A ⟶ C) (p : C ⟶ D)
    [Etale ((BigFppfOver.toScheme B S hS).map p)]
    (h : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj A),
      (BigFppfOver.toScheme B S hS).map (g ≫ p) η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj D)) :
    ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj A),
      (BigFppfOver.toScheme B S hS).map g η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj C) := by
  intro η
  refine mem_genericPoints_of_etale ((BigFppfOver.toScheme B S hS).map p) ?_
  have hc := h η
  rwa [Functor.map_comp, Scheme.Hom.comp_apply] at hc

/-- Morphisms of the site which carry generic points to generic points compose. -/
private lemma mem_genericPoints_comp {A C D : BigFppfOver B S hS} (f : A ⟶ C) (g : C ⟶ D)
    (hf : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj A),
      (BigFppfOver.toScheme B S hS).map f η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj C))
    (hg : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj C),
      (BigFppfOver.toScheme B S hS).map g η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj D)) :
    ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj A),
      (BigFppfOver.toScheme B S hS).map (f ≫ g) η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj D) := fun η => by
  rw [Functor.map_comp, Scheme.Hom.comp_apply]
  exact hg ⟨_, hf η⟩

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U R : BigFppfOver B S hS}
  (w : yoneda.obj U ⟶ F) (pr₁ pr₂ : R ⟶ U)
  (hsq : IsPullback (yoneda.map pr₁) (yoneda.map pr₂) w w)
  (hwet : (MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf w)
  (hU : ∀ V : ((BigFppfOver.toScheme B S hS).obj U).Opens,
    IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj U)) →
      (irreducibleComponents V).Finite)
  (hR : ∀ V : ((BigFppfOver.toScheme B S hS).obj R).Opens,
    IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj R)) →
      (irreducibleComponents V).Finite)
  (hR₂ : ∀ V : ((BigFppfOver.toScheme B S hS).obj (Limits.pullback pr₂ pr₁)).Opens,
    IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj (Limits.pullback pr₂ pr₁))) →
      (irreducibleComponents V).Finite)

/-! ### Generic points along the seven morphisms of the relation -/

include hsq hwet in
/-- The first projection `pr₁ : R ⟶ U` carries generic points to generic points. -/
lemma mem_genericPoints_pr₁ :
    ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj R),
      (BigFppfOver.toScheme B S hS).map pr₁ η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj U) :=
  have _ := NormalizationGluing.etale_toScheme_map_pr₁ B S hS w pr₁ pr₂ hsq hwet
  mem_genericPoints_toScheme_map_of_flat B S hS pr₁

include hsq hwet in
/-- The second projection `pr₂ : R ⟶ U` carries generic points to generic points. -/
lemma mem_genericPoints_pr₂ :
    ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj R),
      (BigFppfOver.toScheme B S hS).map pr₂ η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj U) :=
  have _ := NormalizationGluing.etale_toScheme_map_pr₂ B S hS w pr₁ pr₂ hsq hwet
  mem_genericPoints_toScheme_map_of_flat B S hS pr₂

include hsq hwet in
/-- The first projection `R ×_U R ⟶ R` carries generic points to generic points. -/
lemma mem_genericPoints_rel₂Fst :
    ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj (Limits.pullback pr₂ pr₁)),
      (BigFppfOver.toScheme B S hS).map (Limits.pullback.fst pr₂ pr₁) η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj R) :=
  have _ := NormalizationGluing.etale_toScheme_map_rel₂Fst B S hS w pr₁ pr₂ hsq hwet
  mem_genericPoints_toScheme_map_of_flat B S hS (Limits.pullback.fst pr₂ pr₁)

include hsq hwet in
/-- The second projection `R ×_U R ⟶ R` carries generic points to generic points. -/
lemma mem_genericPoints_rel₂Snd :
    ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj (Limits.pullback pr₂ pr₁)),
      (BigFppfOver.toScheme B S hS).map (Limits.pullback.snd pr₂ pr₁) η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj R) :=
  have _ := NormalizationGluing.etale_toScheme_map_rel₂Snd B S hS w pr₁ pr₂ hsq hwet
  mem_genericPoints_toScheme_map_of_flat B S hS (Limits.pullback.snd pr₂ pr₁)

include hsq hwet in
/-- The diagonal `U ⟶ R` of the relation carries generic points to generic points. -/
lemma mem_genericPoints_relDiag :
    ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj U),
      (BigFppfOver.toScheme B S hS).map
          (NormalizationGluing.relDiag B S hS w pr₁ pr₂ hsq) η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj R) := by
  have _ := NormalizationGluing.etale_toScheme_map_pr₁ B S hS w pr₁ pr₂ hsq hwet
  refine mem_genericPoints_of_comp_etale B S hS _ pr₁ ?_
  intro η
  rw [NormalizationGluing.relDiag_comp_pr₁, CategoryTheory.Functor.map_id]
  exact η.2

include hsq hwet in
/-- The swap `R ⟶ R` of the relation carries generic points to generic points. -/
lemma mem_genericPoints_relSwap :
    ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj R),
      (BigFppfOver.toScheme B S hS).map
          (NormalizationGluing.relSwap B S hS w pr₁ pr₂ hsq) η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj R) := by
  have _ := NormalizationGluing.etale_toScheme_map_pr₁ B S hS w pr₁ pr₂ hsq hwet
  refine mem_genericPoints_of_comp_etale B S hS _ pr₁ ?_
  intro η
  rw [NormalizationGluing.relSwap_comp_pr₁]
  exact mem_genericPoints_pr₂ B S hS w pr₁ pr₂ hsq hwet η

include hsq hwet in
/-- The composition `R ×_U R ⟶ R` of the relation carries generic points to generic points. -/
lemma mem_genericPoints_rel₂Outer :
    ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj (Limits.pullback pr₂ pr₁)),
      (BigFppfOver.toScheme B S hS).map
          (NormalizationGluing.rel₂Outer B S hS w pr₁ pr₂ hsq) η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj R) := by
  have _ := NormalizationGluing.etale_toScheme_map_pr₁ B S hS w pr₁ pr₂ hsq hwet
  refine mem_genericPoints_of_comp_etale B S hS _ pr₁ ?_
  rw [NormalizationGluing.rel₂Outer_comp_pr₁]
  exact mem_genericPoints_comp B S hS _ _ (mem_genericPoints_rel₂Fst B S hS w pr₁ pr₂ hsq hwet)
    (mem_genericPoints_pr₁ B S hS w pr₁ pr₂ hsq hwet)

/-! ### The induced morphisms of normalizations -/

/-- The morphism of normalizations induced by the first projection of `R = U ×_F U`. -/
def normRelFst : normSpace B S hS R hR ⟶ normSpace B S hS U hU :=
  normSpaceMap B S hS hU hR pr₁ (mem_genericPoints_pr₁ B S hS w pr₁ pr₂ hsq hwet)

/-- The morphism of normalizations induced by the second projection of `R = U ×_F U`. -/
def normRelSnd : normSpace B S hS R hR ⟶ normSpace B S hS U hU :=
  normSpaceMap B S hS hU hR pr₂ (mem_genericPoints_pr₂ B S hS w pr₁ pr₂ hsq hwet)

/-- The morphism of normalizations induced by the diagonal of `R = U ×_F U`. -/
def normRelDiag : normSpace B S hS U hU ⟶ normSpace B S hS R hR :=
  normSpaceMap B S hS hR hU (NormalizationGluing.relDiag B S hS w pr₁ pr₂ hsq)
    (mem_genericPoints_relDiag B S hS w pr₁ pr₂ hsq hwet)

/-- The morphism of normalizations induced by the swap of `R = U ×_F U`. -/
def normRelSwap : normSpace B S hS R hR ⟶ normSpace B S hS R hR :=
  normSpaceMap B S hS hR hR (NormalizationGluing.relSwap B S hS w pr₁ pr₂ hsq)
    (mem_genericPoints_relSwap B S hS w pr₁ pr₂ hsq hwet)

/-- The morphism of normalizations induced by the first projection of `R ×_U R`. -/
def normRel₂Fst : normSpace B S hS (Limits.pullback pr₂ pr₁) hR₂ ⟶ normSpace B S hS R hR :=
  normSpaceMap B S hS hR hR₂ (Limits.pullback.fst pr₂ pr₁)
    (mem_genericPoints_rel₂Fst B S hS w pr₁ pr₂ hsq hwet)

/-- The morphism of normalizations induced by the second projection of `R ×_U R`. -/
def normRel₂Snd : normSpace B S hS (Limits.pullback pr₂ pr₁) hR₂ ⟶ normSpace B S hS R hR :=
  normSpaceMap B S hS hR hR₂ (Limits.pullback.snd pr₂ pr₁)
    (mem_genericPoints_rel₂Snd B S hS w pr₁ pr₂ hsq hwet)

/-- The morphism of normalizations induced by the composition of `R ×_U R`. -/
def normRel₂Outer : normSpace B S hS (Limits.pullback pr₂ pr₁) hR₂ ⟶ normSpace B S hS R hR :=
  normSpaceMap B S hS hR hR₂ (NormalizationGluing.rel₂Outer B S hS w pr₁ pr₂ hsq)
    (mem_genericPoints_rel₂Outer B S hS w pr₁ pr₂ hsq hwet)

/-! ### The identities of the relation, each by rigidity -/

/-- `normRelFst` lies over the first projection `pr₁`. -/
@[reassoc]
lemma normRelFst_comp_normSpaceProj :
    normRelFst B S hS w pr₁ pr₂ hsq hwet hU hR ≫ normSpaceProj B S hS U hU =
      normSpaceProj B S hS R hR ≫ pr₁ :=
  normSpaceMap_comp_normSpaceProj B S hS hU hR pr₁ _

/-- `normRelSnd` lies over the second projection `pr₂`. -/
@[reassoc]
lemma normRelSnd_comp_normSpaceProj :
    normRelSnd B S hS w pr₁ pr₂ hsq hwet hU hR ≫ normSpaceProj B S hS U hU =
      normSpaceProj B S hS R hR ≫ pr₂ :=
  normSpaceMap_comp_normSpaceProj B S hS hU hR pr₂ _

/-- `normRelDiag` lies over the diagonal of the relation. -/
@[reassoc]
lemma normRelDiag_comp_normSpaceProj :
    normRelDiag B S hS w pr₁ pr₂ hsq hwet hU hR ≫ normSpaceProj B S hS R hR =
      normSpaceProj B S hS U hU ≫ NormalizationGluing.relDiag B S hS w pr₁ pr₂ hsq :=
  normSpaceMap_comp_normSpaceProj B S hS hR hU _ _

/-- `normRelSwap` lies over the swap of the relation. -/
@[reassoc]
lemma normRelSwap_comp_normSpaceProj :
    normRelSwap B S hS w pr₁ pr₂ hsq hwet hR ≫ normSpaceProj B S hS R hR =
      normSpaceProj B S hS R hR ≫ NormalizationGluing.relSwap B S hS w pr₁ pr₂ hsq :=
  normSpaceMap_comp_normSpaceProj B S hS hR hR _ _

/-- `normRel₂Fst` lies over the first projection `R ×_U R ⟶ R`. -/
@[reassoc]
lemma normRel₂Fst_comp_normSpaceProj :
    normRel₂Fst B S hS w pr₁ pr₂ hsq hwet hR hR₂ ≫ normSpaceProj B S hS R hR =
      normSpaceProj B S hS (Limits.pullback pr₂ pr₁) hR₂ ≫ Limits.pullback.fst pr₂ pr₁ :=
  normSpaceMap_comp_normSpaceProj B S hS hR hR₂ _ _

/-- `normRel₂Snd` lies over the second projection `R ×_U R ⟶ R`. -/
@[reassoc]
lemma normRel₂Snd_comp_normSpaceProj :
    normRel₂Snd B S hS w pr₁ pr₂ hsq hwet hR hR₂ ≫ normSpaceProj B S hS R hR =
      normSpaceProj B S hS (Limits.pullback pr₂ pr₁) hR₂ ≫ Limits.pullback.snd pr₂ pr₁ :=
  normSpaceMap_comp_normSpaceProj B S hS hR hR₂ _ _

/-- `normRel₂Outer` lies over the composition `R ×_U R ⟶ R` of the relation. -/
@[reassoc]
lemma normRel₂Outer_comp_normSpaceProj :
    normRel₂Outer B S hS w pr₁ pr₂ hsq hwet hR hR₂ ≫ normSpaceProj B S hS R hR =
      normSpaceProj B S hS (Limits.pullback pr₂ pr₁) hR₂ ≫
        NormalizationGluing.rel₂Outer B S hS w pr₁ pr₂ hsq :=
  normSpaceMap_comp_normSpaceProj B S hS hR hR₂ _ _

include hsq hwet in
/-- The diagonal followed by the first projection is the identity of `U^ν`. -/
lemma normRelDiag_comp_normRelFst :
    normRelDiag B S hS w pr₁ pr₂ hsq hwet hU hR ≫ normRelFst B S hS w pr₁ pr₂ hsq hwet hU hR =
      𝟙 (normSpace B S hS U hU) := by
  refine normSpace_hom_ext B S hS hU hU (𝟙 U)
    (fun η => by rw [CategoryTheory.Functor.map_id]; exact η.2) ?_ ?_
  · rw [Category.assoc, normRelFst_comp_normSpaceProj, normRelDiag_comp_normSpaceProj_assoc,
      NormalizationGluing.relDiag_comp_pr₁]
  · rw [Category.id_comp, Category.comp_id]

include hsq hwet in
/-- The diagonal followed by the second projection is the identity of `U^ν`. -/
lemma normRelDiag_comp_normRelSnd :
    normRelDiag B S hS w pr₁ pr₂ hsq hwet hU hR ≫ normRelSnd B S hS w pr₁ pr₂ hsq hwet hU hR =
      𝟙 (normSpace B S hS U hU) := by
  refine normSpace_hom_ext B S hS hU hU (𝟙 U)
    (fun η => by rw [CategoryTheory.Functor.map_id]; exact η.2) ?_ ?_
  · rw [Category.assoc, normRelSnd_comp_normSpaceProj, normRelDiag_comp_normSpaceProj_assoc,
      NormalizationGluing.relDiag_comp_pr₂]
  · rw [Category.id_comp, Category.comp_id]

include hsq hwet in
/-- The swap followed by the first projection is the second projection. -/
lemma normRelSwap_comp_normRelFst :
    normRelSwap B S hS w pr₁ pr₂ hsq hwet hR ≫ normRelFst B S hS w pr₁ pr₂ hsq hwet hU hR =
      normRelSnd B S hS w pr₁ pr₂ hsq hwet hU hR := by
  refine normSpace_hom_ext B S hS hU hR pr₂
    (mem_genericPoints_pr₂ B S hS w pr₁ pr₂ hsq hwet) ?_
    (normRelSnd_comp_normSpaceProj B S hS w pr₁ pr₂ hsq hwet hU hR)
  rw [Category.assoc, normRelFst_comp_normSpaceProj, normRelSwap_comp_normSpaceProj_assoc,
    NormalizationGluing.relSwap_comp_pr₁]

include hsq hwet in
/-- The swap followed by the second projection is the first projection. -/
lemma normRelSwap_comp_normRelSnd :
    normRelSwap B S hS w pr₁ pr₂ hsq hwet hR ≫ normRelSnd B S hS w pr₁ pr₂ hsq hwet hU hR =
      normRelFst B S hS w pr₁ pr₂ hsq hwet hU hR := by
  refine normSpace_hom_ext B S hS hU hR pr₁
    (mem_genericPoints_pr₁ B S hS w pr₁ pr₂ hsq hwet) ?_
    (normRelFst_comp_normSpaceProj B S hS w pr₁ pr₂ hsq hwet hU hR)
  rw [Category.assoc, normRelSnd_comp_normSpaceProj, normRelSwap_comp_normSpaceProj_assoc,
    NormalizationGluing.relSwap_comp_pr₂]

include hsq hwet in
/-- The square formed by `normRel₂Fst`, `normRel₂Snd`, `normRelFst` and `normRelSnd` commutes. -/
lemma normRel₂Snd_comp_normRelFst :
    normRel₂Snd B S hS w pr₁ pr₂ hsq hwet hR hR₂ ≫
        normRelFst B S hS w pr₁ pr₂ hsq hwet hU hR =
      normRel₂Fst B S hS w pr₁ pr₂ hsq hwet hR hR₂ ≫
        normRelSnd B S hS w pr₁ pr₂ hsq hwet hU hR := by
  refine normSpace_hom_ext B S hS hU hR₂ (Limits.pullback.snd pr₂ pr₁ ≫ pr₁)
    (mem_genericPoints_comp B S hS _ _ (mem_genericPoints_rel₂Snd B S hS w pr₁ pr₂ hsq hwet)
      (mem_genericPoints_pr₁ B S hS w pr₁ pr₂ hsq hwet)) ?_ ?_
  · rw [Category.assoc, normRelFst_comp_normSpaceProj, normRel₂Snd_comp_normSpaceProj_assoc]
  · rw [Category.assoc, normRelSnd_comp_normSpaceProj, normRel₂Fst_comp_normSpaceProj_assoc,
      Limits.pullback.condition]

include hsq hwet in
/-- The composition followed by the first projection equals `normRel₂Fst` followed by the first
projection. -/
lemma normRel₂Outer_comp_normRelFst :
    normRel₂Outer B S hS w pr₁ pr₂ hsq hwet hR hR₂ ≫
        normRelFst B S hS w pr₁ pr₂ hsq hwet hU hR =
      normRel₂Fst B S hS w pr₁ pr₂ hsq hwet hR hR₂ ≫
        normRelFst B S hS w pr₁ pr₂ hsq hwet hU hR := by
  refine normSpace_hom_ext B S hS hU hR₂ (Limits.pullback.fst pr₂ pr₁ ≫ pr₁)
    (mem_genericPoints_comp B S hS _ _ (mem_genericPoints_rel₂Fst B S hS w pr₁ pr₂ hsq hwet)
      (mem_genericPoints_pr₁ B S hS w pr₁ pr₂ hsq hwet)) ?_ ?_
  · rw [Category.assoc, normRelFst_comp_normSpaceProj, normRel₂Outer_comp_normSpaceProj_assoc,
      NormalizationGluing.rel₂Outer_comp_pr₁]
  · rw [Category.assoc, normRelFst_comp_normSpaceProj, normRel₂Fst_comp_normSpaceProj_assoc]

include hsq hwet in
/-- The composition followed by the second projection equals `normRel₂Snd` followed by the
second projection. -/
lemma normRel₂Outer_comp_normRelSnd :
    normRel₂Outer B S hS w pr₁ pr₂ hsq hwet hR hR₂ ≫
        normRelSnd B S hS w pr₁ pr₂ hsq hwet hU hR =
      normRel₂Snd B S hS w pr₁ pr₂ hsq hwet hR hR₂ ≫
        normRelSnd B S hS w pr₁ pr₂ hsq hwet hU hR := by
  refine normSpace_hom_ext B S hS hU hR₂ (Limits.pullback.snd pr₂ pr₁ ≫ pr₂)
    (mem_genericPoints_comp B S hS _ _ (mem_genericPoints_rel₂Snd B S hS w pr₁ pr₂ hsq hwet)
      (mem_genericPoints_pr₂ B S hS w pr₁ pr₂ hsq hwet)) ?_ ?_
  · rw [Category.assoc, normRelSnd_comp_normSpaceProj, normRel₂Outer_comp_normSpaceProj_assoc,
      NormalizationGluing.rel₂Outer_comp_pr₂]
  · rw [Category.assoc, normRelSnd_comp_normSpaceProj, normRel₂Snd_comp_normSpaceProj_assoc]

/-! ### The cartesian squares -/

include hsq hwet in
/-- The square of the first projection of the relation and the two normalization morphisms is
cartesian. -/
lemma isPullback_normRelFst :
    IsPullback (normRelFst B S hS w pr₁ pr₂ hsq hwet hU hR) (normSpaceProj B S hS R hR)
      (normSpaceProj B S hS U hU) pr₁ :=
  have _ := NormalizationGluing.etale_toScheme_map_pr₁ B S hS w pr₁ pr₂ hsq hwet
  isPullback_normSpaceMap_of_etale B S hS hU hR pr₁ _

include hsq hwet in
/-- The square of the second projection of the relation and the two normalization morphisms is
cartesian. -/
lemma isPullback_normRelSnd :
    IsPullback (normRelSnd B S hS w pr₁ pr₂ hsq hwet hU hR) (normSpaceProj B S hS R hR)
      (normSpaceProj B S hS U hU) pr₂ :=
  have _ := NormalizationGluing.etale_toScheme_map_pr₂ B S hS w pr₁ pr₂ hsq hwet
  isPullback_normSpaceMap_of_etale B S hS hU hR pr₂ _

include hsq hwet in
/-- The square of the first projection of `R ×_U R` and the two normalization morphisms is
cartesian. -/
lemma isPullback_normRel₂Fst :
    IsPullback (normRel₂Fst B S hS w pr₁ pr₂ hsq hwet hR hR₂)
      (normSpaceProj B S hS (Limits.pullback pr₂ pr₁) hR₂) (normSpaceProj B S hS R hR)
      (Limits.pullback.fst pr₂ pr₁) :=
  have _ := NormalizationGluing.etale_toScheme_map_rel₂Fst B S hS w pr₁ pr₂ hsq hwet
  isPullback_normSpaceMap_of_etale B S hS hR hR₂ (Limits.pullback.fst pr₂ pr₁) _

include hsq hwet in
/-- The square of the second projection of `R ×_U R` and the two normalization morphisms is
cartesian. -/
lemma isPullback_normRel₂Snd :
    IsPullback (normRel₂Snd B S hS w pr₁ pr₂ hsq hwet hR hR₂)
      (normSpaceProj B S hS (Limits.pullback pr₂ pr₁) hR₂) (normSpaceProj B S hS R hR)
      (Limits.pullback.snd pr₂ pr₁) :=
  have _ := NormalizationGluing.etale_toScheme_map_rel₂Snd B S hS w pr₁ pr₂ hsq hwet
  isPullback_normSpaceMap_of_etale B S hS hR hR₂ (Limits.pullback.snd pr₂ pr₁) _

include hsq hwet in
/-- **The normalization of `R ×_U R` is the fibre product of two copies of that of `R` over
that of `U`.** -/
lemma isPullback_normRel₂ :
    IsPullback (normRel₂Snd B S hS w pr₁ pr₂ hsq hwet hR hR₂)
      (normRel₂Fst B S hS w pr₁ pr₂ hsq hwet hR hR₂)
      (normRelFst B S hS w pr₁ pr₂ hsq hwet hU hR)
      (normRelSnd B S hS w pr₁ pr₂ hsq hwet hU hR) := by
  have hA := isPullback_normRelFst B S hS w pr₁ pr₂ hsq hwet hU hR
  have hB := isPullback_normRelSnd B S hS w pr₁ pr₂ hsq hwet hU hR
  have hC := isPullback_normRel₂Fst B S hS w pr₁ pr₂ hsq hwet hR hR₂
  have hD := isPullback_normRel₂Snd B S hS w pr₁ pr₂ hsq hwet hR hR₂
  have hE : IsPullback (Limits.pullback.snd pr₂ pr₁) (Limits.pullback.fst pr₂ pr₁) pr₁ pr₂ :=
    (IsPullback.of_hasPullback pr₂ pr₁).flip
  have houter := hD.paste_vert hE
  rw [← hC.w, ← hA.w] at houter
  exact houter.of_bot (normRel₂Snd_comp_normRelFst B S hS w pr₁ pr₂ hsq hwet hU hR hR₂) hB

/-! ### The equivalence relation -/

include hsq hwet in
/-- **The two induced morphisms of normalizations are jointly monic.** -/
lemma jointlyMono₂_normRel :
    JointlyMono₂ (yoneda.map (normRelSnd B S hS w pr₁ pr₂ hsq hwet hU hR))
      (yoneda.map (normRelFst B S hS w pr₁ pr₂ hsq hwet hU hR)) := by
  have hA := (isPullback_normRelFst B S hS w pr₁ pr₂ hsq hwet hU hR).map yoneda
  have hB := (isPullback_normRelSnd B S hS w pr₁ pr₂ hsq hwet hU hR).map yoneda
  refine ⟨fun Z a b h₁ h₂ => hA.hom_ext h₂ (hsq.hom_ext ?_ ?_)⟩
  · rw [Category.assoc, Category.assoc, ← hA.w, ← Category.assoc, ← Category.assoc, h₂]
  · rw [Category.assoc, Category.assoc, ← hB.w, ← Category.assoc, ← Category.assoc, h₁]

include hsq hwet in
/-- **The normalizations along the presentation form an internal equivalence relation of
presheaves.** -/
def equivalenceRelation_normRel :
    EquivalenceRelation (yoneda.map (normRelSnd B S hS w pr₁ pr₂ hsq hwet hU hR))
      (yoneda.map (normRelFst B S hS w pr₁ pr₂ hsq hwet hU hR)) where
  __ := jointlyMono₂_normRel B S hS w pr₁ pr₂ hsq hwet hU hR
  r := yoneda.map (normRelDiag B S hS w pr₁ pr₂ hsq hwet hU hR)
  reflexivity₁ := by
    rw [← Functor.map_comp, normRelDiag_comp_normRelSnd, CategoryTheory.Functor.map_id]
  reflexivity₂ := by
    rw [← Functor.map_comp, normRelDiag_comp_normRelFst, CategoryTheory.Functor.map_id]
  s := yoneda.map (normRelSwap B S hS w pr₁ pr₂ hsq hwet hR)
  symmetry₁ := by
    rw [← Functor.map_comp, normRelSwap_comp_normRelSnd]
  symmetry₂ := by
    rw [← Functor.map_comp, normRelSwap_comp_normRelFst]
  c := ((isPullback_normRel₂ B S hS w pr₁ pr₂ hsq hwet hU hR hR₂).map yoneda).cone
  isLimit := ((isPullback_normRel₂ B S hS w pr₁ pr₂ hsq hwet hU hR hR₂).map yoneda).isLimit
  t := yoneda.map (normRel₂Outer B S hS w pr₁ pr₂ hsq hwet hR hR₂)
  transitivity₁ := by
    change yoneda.map (normRel₂Outer B S hS w pr₁ pr₂ hsq hwet hR hR₂) ≫
        yoneda.map (normRelSnd B S hS w pr₁ pr₂ hsq hwet hU hR) =
      yoneda.map (normRel₂Snd B S hS w pr₁ pr₂ hsq hwet hR hR₂) ≫
        yoneda.map (normRelSnd B S hS w pr₁ pr₂ hsq hwet hU hR)
    rw [← Functor.map_comp, ← Functor.map_comp, normRel₂Outer_comp_normRelSnd]
  transitivity₂ := by
    change yoneda.map (normRel₂Outer B S hS w pr₁ pr₂ hsq hwet hR hR₂) ≫
        yoneda.map (normRelFst B S hS w pr₁ pr₂ hsq hwet hU hR) =
      yoneda.map (normRel₂Fst B S hS w pr₁ pr₂ hsq hwet hR hR₂) ≫
        yoneda.map (normRelFst B S hS w pr₁ pr₂ hsq hwet hU hR)
    rw [← Functor.map_comp, ← Functor.map_comp, normRel₂Outer_comp_normRelFst]

include hsq hwet hR₂ in
/-- **The normalizations along an étale presentation of `F` form an étale equivalence relation
over `S`**, in the sense of Tag 02WS. -/
theorem isEtaleEquivalenceRelation_normRel :
    Stacks.Groupoids.IsEtaleEquivalenceRelation
      (relation B S hS (normRelFst B S hS w pr₁ pr₂ hsq hwet hU hR)
        (normRelSnd B S hS w pr₁ pr₂ hsq hwet hU hR)) := by
  have _ := NormalizationGluing.etale_toScheme_map_pr₁ B S hS w pr₁ pr₂ hsq hwet
  have _ := NormalizationGluing.etale_toScheme_map_pr₂ B S hS w pr₁ pr₂ hsq hwet
  refine isEtaleEquivalenceRelation_of_embedding B S hS _ _ yoneda (Iso.refl _) ?_
    (etale_toScheme_map_normSpaceMap B S hS hU hR pr₂ _)
    (etale_toScheme_map_normSpaceMap B S hS hU hR pr₁ _)
  simp only [Iso.refl_hom, Category.id_comp]
  exact (equivalenceRelation_normRel B S hS w pr₁ pr₂ hsq hwet hU hR hR₂).isEquivalenceRelation

end AlgebraicGeometry.Space.NormSpaceGluing

end
