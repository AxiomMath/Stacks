module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.SchemeTheoreticallyDense
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced
public import StacksCore.Tactic.StacksAttribute

/-!
# Scheme-theoretic image of an immersion

If an immersion is quasi-compact, or if its source is reduced, then its map to its
scheme-theoretic image is an open immersion. Its image is both scheme-theoretically and
topologically dense in the scheme-theoretic image.

## Main results

* `AlgebraicGeometry.isOpenImmersion_toImage` identifies the immersion with an open subscheme
  of its scheme-theoretic image.
* `AlgebraicGeometry.isSchemeTheoreticallyDense_toImage` gives scheme-theoretic density of
  that open subscheme.
* `AlgebraicGeometry.isDominant_toImage` gives its topological density.
* `AlgebraicGeometry.isSchemeTheoreticallyDominant_toImage_of_quasiCompact`: a quasi-compact
  morphism is scheme-theoretically dominant onto its scheme-theoretic image.

## Implementation notes

The scheme-theoretic image is `AlgebraicGeometry.Scheme.Hom.image`, and the canonical map to it
is `AlgebraicGeometry.Scheme.Hom.toImage`. The open subscheme corresponding to this map is
`AlgebraicGeometry.Scheme.Hom.opensRange`; the canonical isomorphism from the source to this
open subscheme is supplied by the open-immersion API. The three conclusions of the source lemma
are stated separately.

`AlgebraicGeometry.isDominant_toImage` carries an `[IsImmersion h]` instance argument that its
proof does not use; the `unusedArguments` linter reports it. The hypothesis is part of the
statement of the source lemma and is kept deliberately, so that the three conclusions share one
set of hypotheses.

## References

* [Stacks Project, Tag 01RG](https://stacks.math.columbia.edu/tag/01RG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A morphism with reduced source is dominant onto its scheme-theoretic image. -/
private instance isDominant_toImage_of_isReduced {Z X : Scheme.{u}} (h : Z ⟶ X)
    [IsReduced Z] : IsDominant h.toImage := by
  refine ⟨?_⟩
  rw [denseRange_iff_closure_range, h.imageι.isEmbedding.closure_eq_preimage_closure_image,
      ← Set.univ_subset_iff, ← Set.image_subset_iff, Set.image_univ,
      Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range h,
      Scheme.IdealSheafData.coe_support_vanishingIdeal, ← Set.range_comp,
      ← TopCat.coe_comp, ← Scheme.Hom.comp_base, h.toImage_imageι]
  rfl

/-- A dominant immersion into a reduced scheme is an open immersion. -/
private lemma isOpenImmersion_of_dominant_reduced {Z X : Scheme.{u}} (f : Z ⟶ X)
    [IsImmersion f] [IsDominant f] [IsReduced X] : IsOpenImmersion f := by
  obtain ⟨W, a, b, ha, hb, hab⟩ :=
    (IsImmersion.isImmersion_iff_exists (f := f)).mp inferInstance
  let : IsClosedImmersion a := ha
  let : IsOpenImmersion b := hb
  have : IsDominant (a ≫ b) := by simpa [hab] using (inferInstance : IsDominant f)
  have : IsDominant a := IsDominant.of_comp_of_isOpenImmersion a b
  have : IsReduced W := AlgebraicGeometry.isReduced_of_isOpenImmersion b
  have : Surjective a :=
    surjective_of_isDominant_of_isClosed_range a a.isClosedEmbedding.isClosed_range
  have : IsIso a := isIso_of_isClosedImmersion_of_surjective a
  rw [← hab]
  infer_instance

/-- A quasi-compact morphism is scheme-theoretically dominant onto its scheme-theoretic
image. -/
lemma isSchemeTheoreticallyDominant_toImage_of_quasiCompact
    {Z X : Scheme.{u}} (h : Z ⟶ X) [QuasiCompact h] :
    IsSchemeTheoreticallyDominant h.toImage := by
  rw [isSchemeTheoreticallyDominant_iff]
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : X.affineOpens ↦ ⟨h.imageι ⁻¹ᵁ U.1, U.2.preimage h.imageι⟩)
    (TopologicalSpace.IsOpenCover.comap (iSup_affineOpens_eq_top X) h.imageι.base.hom)
    fun U ↦ ?_
  simp only [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
  rw [← RingHom.injective_iff_ker_eq_bot]
  exact h.toImage_app_injective U

/-- An immersion which is quasi-compact, or has reduced source, is open in its
scheme-theoretic image. -/
@[stacks 01RG "open immersion", ega "I 9.5.10" "Y open in closure"]
lemma isOpenImmersion_toImage {Z X : Scheme.{u}} (h : Z ⟶ X)
    [IsImmersion h] (hq_or_hr : QuasiCompact h ∨ IsReduced Z) :
    IsOpenImmersion h.toImage := by
  rcases hq_or_hr with _ | _
  · infer_instance
  · exact isOpenImmersion_of_dominant_reduced h.toImage

/-- The open subscheme corresponding to an immersion in its scheme-theoretic image is
scheme-theoretically dense. -/
@[stacks 01RG "scheme-theoretic density"]
lemma isSchemeTheoreticallyDense_toImage {Z X : Scheme.{u}} (h : Z ⟶ X)
    [IsImmersion h] (hq_or_hr : QuasiCompact h ∨ IsReduced Z) :
    (letI : IsOpenImmersion h.toImage := isOpenImmersion_toImage h hq_or_hr
     Scheme.Opens.IsSchemeTheoreticallyDense h.toImage.opensRange) := by
  let : IsOpenImmersion h.toImage := isOpenImmersion_toImage h hq_or_hr
  intro V
  rcases hq_or_hr with _ | _
  · let : IsSchemeTheoreticallyDominant h.toImage :=
      isSchemeTheoreticallyDominant_toImage_of_quasiCompact h
    let p := pullback.snd h.toImage V.ι
    have hp : IsSchemeTheoreticallyDominant p := by infer_instance
    have hp' : IsSchemeTheoreticallyDominant
        (p.isoOpensRange.hom ≫ p.opensRange.ι) := by simpa using hp
    have hker := (isSchemeTheoreticallyDominant_iff _).mp hp'
    rw [Scheme.Hom.ker_comp, Scheme.Hom.ker_eq_bot_of_isIso,
      Scheme.IdealSheafData.map_bot] at hker
    have hdense : IsSchemeTheoreticallyDominant p.opensRange.ι :=
      (isSchemeTheoreticallyDominant_iff _).mpr hker
    have hrange : p.opensRange = V.ι ⁻¹ᵁ h.toImage.opensRange := by
      simpa [p] using Scheme.Hom.opensRange_pullbackSnd (f := h.toImage) (g := V.ι)
    rwa [← hrange]
  · have hU : Dense (h.toImage.opensRange : Set h.image) := by
      simpa only [Scheme.Hom.coe_opensRange] using
        (dense_iff_closure_eq.mpr (denseRange_iff_closure_range.mp h.toImage.denseRange))
    have : IsDominant ((V.ι ⁻¹ᵁ h.toImage.opensRange).ι) :=
      Opens.isDominant_ι (hU.preimage V.ι.isOpenEmbedding.isOpenMap)
    have : IsReduced V.toScheme := inferInstance
    exact IsSchemeTheoreticallyDominant.of_isDominant _

/-- The image of an immersion is topologically dense in its scheme-theoretic image. -/
@[stacks 01RG "topological density", ega "I 9.5.10" "topological density"]
lemma isDominant_toImage {Z X : Scheme.{u}} (h : Z ⟶ X)
    [IsImmersion h] (hq_or_hr : QuasiCompact h ∨ IsReduced Z) :
    IsDominant h.toImage := by
  rcases hq_or_hr with _ | _ <;> infer_instance

end AlgebraicGeometry

end
