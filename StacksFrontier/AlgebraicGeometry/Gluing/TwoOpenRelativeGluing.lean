module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Gluing.TwoChart
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.BaseChange

/-!
# Relative gluing over a two-member open cover of the base

Let `Y` be a scheme with two opens `U₁` and `U₂`, let `f₁ : X₁ ⟶ U₁` and `f₂ : X₂ ⟶ U₂` be
morphisms of schemes, and let `φ` be an isomorphism between the part of `X₁` lying over
`U₁ ⊓ U₂` and the part of `X₂` lying over `U₁ ⊓ U₂`, compatible with the two maps to `Y`. Then
`X₁` and `X₂` glue along `φ` to a scheme `X` with a morphism `f : X ⟶ Y` whose part over each
`Uᵢ` is `fᵢ`. A two-member cover has no triple overlaps, so no cocycle condition is asked for.

This is the relative gluing of [Stacks, Tag 01LH] for a cover with two members. The glued
morphism is `AlgebraicGeometry.glueChartsHom` applied to the overlap `f₁ ⁻¹ᵁ (U₁.ι ⁻¹ᵁ U₂)` and
its two open immersions, into `X₁` directly and into `X₂` through `φ`.

## The datum

`Stacks.TwoOpenRelativeGluing.Datum Y` bundles `U₁`, `U₂`, `f₁`, `f₂` and the isomorphism
`φ : f₁ ⁻¹ᵁ (U₁.ι ⁻¹ᵁ U₂) ≅ f₂ ⁻¹ᵁ (U₂.ι ⁻¹ᵁ U₁)` of open subschemes, together with the
equation saying that `φ` commutes with the two maps to `Y`. The two opens need not cover `Y`;
the hypothesis `U₁ ⊔ U₂ = ⊤` is an assumption of the results which need it.

## Main definitions

* `Stacks.TwoOpenRelativeGluing.Datum.glued`: the glued scheme `X`.
* `Stacks.TwoOpenRelativeGluing.Datum.hom`: the glued morphism `f : X ⟶ Y`.
* `Stacks.TwoOpenRelativeGluing.Datum.ι₁`, `Stacks.TwoOpenRelativeGluing.Datum.ι₂`: the two
  open immersions `Xᵢ ⟶ X`.
* `Stacks.TwoOpenRelativeGluing.Datum.iso₁`, `Stacks.TwoOpenRelativeGluing.Datum.iso₂`: the
  isomorphisms `f ⁻¹ᵁ Uᵢ ≅ Xᵢ`, with `iso₁_hom_f₁ : iso₁.hom ≫ f₁ = f ∣_ U₁` and its twin.

## Main results

* `Stacks.TwoOpenRelativeGluing.Datum.isPullback₁`, `...isPullback₂`: the square
  `Xᵢ ⟶ X`, `Xᵢ ⟶ Uᵢ`, `Uᵢ ⟶ Y`, `X ⟶ Y` is cartesian.
* `Stacks.TwoOpenRelativeGluing.Datum.glue_condition`: the two charts agree on the overlap
  through `φ`.
* `Stacks.TwoOpenRelativeGluing.Datum.property_hom`: a property local on the target in the
  Zariski topology holds for `f` when it holds for `f₁` and `f₂` and `U₁ ⊔ U₂ = ⊤`; in
  particular `Stacks.TwoOpenRelativeGluing.Datum.isProper_hom`.
* `Stacks.TwoOpenRelativeGluing.Datum.isLocallyProjective_hom`: if `f₁` and `f₂` are projective
  (Tag 01W8, first condition) and `U₁ ⊔ U₂ = ⊤`, then `f` is locally projective (Tag 01W8,
  third condition).

## References

* [Stacks Project, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.TwoOpenRelativeGluing

/-- The image of the inclusion of an open `W` into a larger open `V` is the inverse image of `W`
in `V`. -/
lemma opensRange_homOfLE {Y : Scheme.{u}} {W V : Y.Opens} (h : W ≤ V) :
    (Y.homOfLE h).opensRange = V.ι ⁻¹ᵁ W := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change V.ι (Y.homOfLE h y) ∈ W
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
    exact y.2
  · intro hx
    refine ⟨(⟨V.ι x, hx⟩ : W), V.ι.isOpenEmbedding.injective ?_⟩
    change (Y.homOfLE h ≫ V.ι) _ = V.ι x
    rw [Scheme.homOfLE_ι]
    rfl

/-- Inside `U`, the inverse image of `U ⊓ V` is the inverse image of `V`. -/
lemma ι_preimage_inf_left {Y : Scheme.{u}} (U V : Y.Opens) :
    U.ι ⁻¹ᵁ (U ⊓ V) = U.ι ⁻¹ᵁ V := by
  ext x
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨x.2, h⟩⟩

/-- Inside `V`, the inverse image of `U ⊓ V` is the inverse image of `U`. -/
lemma ι_preimage_inf_right {Y : Scheme.{u}} (U V : Y.Opens) :
    V.ι ⁻¹ᵁ (U ⊓ V) = V.ι ⁻¹ᵁ U := by
  ext x
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, x.2⟩⟩

/-- **A relative gluing datum over a two-member open cover of the base.** Two opens `U₁`, `U₂` of
`Y`, a morphism `fᵢ : Xᵢ ⟶ Uᵢ` for each, and an isomorphism `φ` between the part
`f₁ ⁻¹ᵁ (U₁.ι ⁻¹ᵁ U₂)` of `X₁` over `U₁ ⊓ U₂` and the part `f₂ ⁻¹ᵁ (U₂.ι ⁻¹ᵁ U₁)` of `X₂` over
`U₁ ⊓ U₂`, commuting with the two maps to `Y`. -/
structure Datum (Y : Scheme.{u}) where
  /-- The first open of the base. -/
  U₁ : Y.Opens
  /-- The second open of the base. -/
  U₂ : Y.Opens
  /-- The scheme over the first open. -/
  X₁ : Scheme.{u}
  /-- The scheme over the second open. -/
  X₂ : Scheme.{u}
  /-- The morphism to the first open. -/
  f₁ : X₁ ⟶ U₁.toScheme
  /-- The morphism to the second open. -/
  f₂ : X₂ ⟶ U₂.toScheme
  /-- The identification of the two parts lying over `U₁ ⊓ U₂`. -/
  φ : (f₁ ⁻¹ᵁ (U₁.ι ⁻¹ᵁ U₂)).toScheme ≅ (f₂ ⁻¹ᵁ (U₂.ι ⁻¹ᵁ U₁)).toScheme
  /-- The identification commutes with the two maps to `Y`. -/
  comm : φ.hom ≫ (f₂ ⁻¹ᵁ (U₂.ι ⁻¹ᵁ U₁)).ι ≫ f₂ ≫ U₂.ι =
    (f₁ ⁻¹ᵁ (U₁.ι ⁻¹ᵁ U₂)).ι ≫ f₁ ≫ U₁.ι

namespace Datum

variable {Y : Scheme.{u}} (D : Datum Y)

/-- The part of `X₁` lying over `U₁ ⊓ U₂`. -/
abbrev overlap₁ : D.X₁.Opens := D.f₁ ⁻¹ᵁ (D.U₁.ι ⁻¹ᵁ D.U₂)

/-- The part of `X₂` lying over `U₁ ⊓ U₂`. -/
abbrev overlap₂ : D.X₂.Opens := D.f₂ ⁻¹ᵁ (D.U₂.ι ⁻¹ᵁ D.U₁)

/-- The inclusion of the overlap into `X₂`, through `φ`. -/
abbrev overlapι₂ : D.overlap₁.toScheme ⟶ D.X₂ := D.φ.hom ≫ D.overlap₂.ι

/-- The overlap maps into `U₁ ⊓ U₂`. -/
lemma range_overlap_subset :
    Set.range (D.overlap₁.ι ≫ D.f₁ ≫ D.U₁.ι) ⊆ Set.range (D.U₁ ⊓ D.U₂).ι := by
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact ⟨(D.f₁ x.1).2, x.2⟩

/-- The map from the overlap to `U₁ ⊓ U₂`. -/
noncomputable def overlapToInf : D.overlap₁.toScheme ⟶ (D.U₁ ⊓ D.U₂).toScheme :=
  IsOpenImmersion.lift (D.U₁ ⊓ D.U₂).ι (D.overlap₁.ι ≫ D.f₁ ≫ D.U₁.ι) D.range_overlap_subset

/-- The map from the overlap to `U₁ ⊓ U₂` lifts the map from the overlap to `Y`. -/
@[reassoc (attr := simp)]
lemma overlapToInf_ι : D.overlapToInf ≫ (D.U₁ ⊓ D.U₂).ι = D.overlap₁.ι ≫ D.f₁ ≫ D.U₁.ι :=
  IsOpenImmersion.lift_fac _ _ _

/-- On the overlap, `f₁` factors through `U₁ ⊓ U₂`. -/
lemma overlap_f₁ : D.overlap₁.ι ≫ D.f₁ = D.overlapToInf ≫ Y.homOfLE inf_le_left := by
  rw [← cancel_mono D.U₁.ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι, overlapToInf_ι]

/-- On the overlap, `φ` followed by `f₂` factors through `U₁ ⊓ U₂`. -/
lemma overlap_f₂ : D.overlapι₂ ≫ D.f₂ = D.overlapToInf ≫ Y.homOfLE inf_le_right := by
  rw [← cancel_mono D.U₂.ι, Category.assoc, Category.assoc, Category.assoc, Scheme.homOfLE_ι,
    overlapToInf_ι, D.comm]

/-- The inverse image in `X₁` of `U₁ ⊓ U₂` is the overlap. -/
lemma preimage_opensRange₁ :
    D.f₁ ⁻¹ᵁ (Y.homOfLE (inf_le_left : D.U₁ ⊓ D.U₂ ≤ D.U₁)).opensRange =
      D.overlap₁.ι.opensRange := by
  rw [opensRange_homOfLE, ι_preimage_inf_left, Scheme.Opens.opensRange_ι]

/-- The inverse image in `X₂` of `U₁ ⊓ U₂` is the image of the overlap through `φ`. -/
lemma preimage_opensRange₂ :
    D.f₂ ⁻¹ᵁ (Y.homOfLE (inf_le_right : D.U₁ ⊓ D.U₂ ≤ D.U₂)).opensRange =
      D.overlapι₂.opensRange := by
  rw [opensRange_homOfLE, ι_preimage_inf_right, Scheme.Hom.opensRange_comp_of_isIso,
    Scheme.Opens.opensRange_ι]

/-- **The glued scheme** `X`: `X₁` and `X₂` glued along the overlap, identified through `φ`. -/
noncomputable abbrev glued : Scheme.{u} := Scheme.gluePair D.overlap₁.ι D.overlapι₂

/-- **The glued morphism** `f : X ⟶ Y`. -/
noncomputable def hom : D.glued ⟶ Y :=
  glueChartsHom D.f₁ D.f₂ D.overlapToInf D.overlap₁.ι D.overlapι₂ D.overlap_f₁ D.overlap_f₂

/-- The open immersion of the first chart into the glued scheme. -/
noncomputable abbrev ι₁ : D.X₁ ⟶ D.glued := Scheme.gluePairInl D.overlap₁.ι D.overlapι₂

/-- The open immersion of the second chart into the glued scheme. -/
noncomputable abbrev ι₂ : D.X₂ ⟶ D.glued := Scheme.gluePairInr D.overlap₁.ι D.overlapι₂

/-- The glued morphism restricts to `f₁` on the first chart. -/
@[reassoc (attr := simp)]
lemma ι₁_hom : D.ι₁ ≫ D.hom = D.f₁ ≫ D.U₁.ι :=
  gluePairInl_glueChartsHom _ _ _ _ _ _ _

/-- The glued morphism restricts to `f₂` on the second chart. -/
@[reassoc (attr := simp)]
lemma ι₂_hom : D.ι₂ ≫ D.hom = D.f₂ ≫ D.U₂.ι :=
  gluePairInr_glueChartsHom _ _ _ _ _ _ _

/-- **The two charts agree on the overlap through `φ`.** -/
lemma glue_condition : D.overlap₁.ι ≫ D.ι₁ = D.φ.hom ≫ D.overlap₂.ι ≫ D.ι₂ :=
  (Scheme.gluePair_condition _ _).trans (Category.assoc _ _ _)

/-- **The first chart is the part of the glued scheme over `U₁`.** -/
lemma isPullback₁ : IsPullback D.f₁ D.ι₁ D.U₁.ι D.hom :=
  isPullback_gluePairInl_glueCharts _ _ _ _ _ _ _ D.preimage_opensRange₂

/-- **The second chart is the part of the glued scheme over `U₂`.** -/
lemma isPullback₂ : IsPullback D.f₂ D.ι₂ D.U₂.ι D.hom :=
  isPullback_gluePairInr_glueCharts _ _ _ _ _ _ _ D.preimage_opensRange₁

/-- The image of the first chart is the inverse image of `U₁`. -/
lemma opensRange_ι₁ : D.ι₁.opensRange = D.hom ⁻¹ᵁ D.U₁ :=
  (preimage_glueChartsHom_left _ _ _ _ _ _ _ D.preimage_opensRange₂).symm

/-- The image of the second chart is the inverse image of `U₂`. -/
lemma opensRange_ι₂ : D.ι₂.opensRange = D.hom ⁻¹ᵁ D.U₂ :=
  (preimage_glueChartsHom_right _ _ _ _ _ _ _ D.preimage_opensRange₁).symm

/-- **The part of the glued scheme over `U₁` is `X₁`.** -/
noncomputable def iso₁ : (D.hom ⁻¹ᵁ D.U₁).toScheme ≅ D.X₁ :=
  (isPullback_morphismRestrict D.hom D.U₁).isoIsPullback _ _ D.isPullback₁

/-- **The part of the glued scheme over `U₂` is `X₂`.** -/
noncomputable def iso₂ : (D.hom ⁻¹ᵁ D.U₂).toScheme ≅ D.X₂ :=
  (isPullback_morphismRestrict D.hom D.U₂).isoIsPullback _ _ D.isPullback₂

/-- Under `iso₁`, the restriction of `f` over `U₁` is `f₁`. -/
@[reassoc (attr := simp)]
lemma iso₁_hom_f₁ : D.iso₁.hom ≫ D.f₁ = D.hom ∣_ D.U₁ :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- Under `iso₂`, the restriction of `f` over `U₂` is `f₂`. -/
@[reassoc (attr := simp)]
lemma iso₂_hom_f₂ : D.iso₂.hom ≫ D.f₂ = D.hom ∣_ D.U₂ :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- Under `iso₁`, the first chart is the inclusion of the inverse image of `U₁`. -/
@[reassoc (attr := simp)]
lemma iso₁_hom_ι₁ : D.iso₁.hom ≫ D.ι₁ = (D.hom ⁻¹ᵁ D.U₁).ι :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- Under `iso₂`, the second chart is the inclusion of the inverse image of `U₂`. -/
@[reassoc (attr := simp)]
lemma iso₂_hom_ι₂ : D.iso₂.hom ≫ D.ι₂ = (D.hom ⁻¹ᵁ D.U₂).ι :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- The restriction of `f` over `U₁` is `f₁` after the identification `iso₁`. -/
lemma morphismRestrict_U₁ : D.hom ∣_ D.U₁ = D.iso₁.hom ≫ D.f₁ := D.iso₁_hom_f₁.symm

/-- The restriction of `f` over `U₂` is `f₂` after the identification `iso₂`. -/
lemma morphismRestrict_U₂ : D.hom ∣_ D.U₂ = D.iso₂.hom ≫ D.f₂ := D.iso₂_hom_f₂.symm

/-- The two opens as a family indexed by a type in the universe of the schemes. -/
def cover (b : ULift.{u} Bool) : Y.Opens := cond b.down D.U₁ D.U₂

/-- The family `cover` covers `Y` when `U₁ ⊔ U₂ = ⊤`. -/
lemma iSup_cover (hU : D.U₁ ⊔ D.U₂ = ⊤) : (⨆ b, D.cover b) = ⊤ := by
  refine eq_top_iff.mpr (hU ▸ sup_le ?_ ?_)
  · exact le_iSup_of_le (⟨true⟩ : ULift.{u} Bool) le_rfl
  · exact le_iSup_of_le (⟨false⟩ : ULift.{u} Bool) le_rfl

/-- **A property local on the target holds for the glued morphism** when it holds for `f₁` and
`f₂` and the two opens cover `Y`. -/
theorem property_hom (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (hU : D.U₁ ⊔ D.U₂ = ⊤) (h₁ : P D.f₁) (h₂ : P D.f₂) : P D.hom :=
  property_glueCharts_hom _ _ _ _ _ _ _ P hU D.preimage_opensRange₁ D.preimage_opensRange₂ h₁ h₂

/-- **The glued morphism is proper** when `f₁` and `f₂` are and the two opens cover `Y`. -/
theorem isProper_hom (hU : D.U₁ ⊔ D.U₂ = ⊤) (h₁ : IsProper D.f₁) (h₂ : IsProper D.f₂) :
    IsProper D.hom :=
  D.property_hom @IsProper hU h₁ h₂

/-- **The glued morphism is locally projective** (Tag 01W8, third condition) when `f₁` and `f₂`
are projective (Tag 01W8, first condition) and the two opens cover `Y`. -/
theorem isLocallyProjective_hom (hU : D.U₁ ⊔ D.U₂ = ⊤) (h₁ : IsProjective D.f₁)
    (h₂ : IsProjective D.f₂) : IsLocallyProjective D.hom := by
  refine ⟨ULift.{u} Bool, D.cover, D.iSup_cover hU, fun ⟨b⟩ ↦ ?_⟩
  cases b with
  | true =>
    change IsProjective (D.hom ∣_ D.U₁)
    rw [morphismRestrict_U₁]
    exact IsProjective.comp_iso D.iso₁ h₁
  | false =>
    change IsProjective (D.hom ∣_ D.U₂)
    rw [morphismRestrict_U₂]
    exact IsProjective.comp_iso D.iso₂ h₂

end Datum

end Stacks.TwoOpenRelativeGluing

end
