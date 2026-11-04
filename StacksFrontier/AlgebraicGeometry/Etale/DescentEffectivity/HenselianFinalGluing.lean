module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.SpanOverBase

/-!
# Recognising a scheme as a glueing, and the final glueing of Tag 0BTP

The last step of [Stacks, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP) glues the finite
piece `U_fin`, finite étale over the base, to the piece `U'` already produced over the open `S'`
of the base, along `U'_fin = U_fin ×_S S'`, which is open in `U_fin` and open and closed in `U'`.
It then has to see that the fibre product of the glued scheme with `X` over the base is the
scheme `V` of the descent datum.

`AlgebraicGeometry.SpanGlue.isPullback_desc` says that the fibre product of a glueing is the
glueing of the fibre products. This file proves that the morphism out of the glueing of two opens
of a scheme which cover it and meet exactly in the glueing datum is an isomorphism, and combines
the two: a scheme `V` covered by two opens which are the fibre products of the two charts is the
fibre product of the glued scheme.

Nothing here is specific to the henselian situation, and no finiteness, étaleness or
separatedness of the pieces is used or asserted; the glueing of two separated schemes along an
open subscheme is in general not separated.

## Main results

* `AlgebraicGeometry.SpanGlue.preimage_opensRange_desc_eq_opensRange_ι₁` and
  `AlgebraicGeometry.SpanGlue.preimage_opensRange_desc_eq_opensRange_ι₂`: each chart of the
  glueing of two opens of a scheme is exactly the part of the glueing lying over that open.
* `AlgebraicGeometry.SpanGlue.isIso_desc`: **a scheme covered by two opens which meet exactly in
  the glueing datum is the glueing of those two opens.**
* `Stacks.Etale.exists_isPullback_desc_of_charts`: **the final glueing.** A scheme covered by two
  opens, each the fibre product of the corresponding chart of a glueing with a fixed scheme over
  the base and overlapping exactly over the common open, is the fibre product of the glued scheme
  with that scheme over the base.

## Implementation notes

The recognition statement takes the two intersection conditions
`m₁ ⁻¹ᵁ m₂.opensRange = k₁.opensRange` and `m₂ ⁻¹ᵁ m₁.opensRange = k₂.opensRange` separately.
They say the same thing — that the two opens meet in the image of the glueing datum — read from
the two sides, and each follows from the other because the two charts are monomorphisms.

Being an isomorphism is Zariski-local on the target, and the restriction of the descended
morphism to each of the two opens is an identity: the identification of the chart with the part
of the glueing over the open is `AlgebraicGeometry.IsOpenImmersion.isPullback`, whose hypothesis
on preimages of ranges is exactly the chart computation above.

The conclusion of the final glueing is an `CategoryTheory.IsPullback` square rather than an
isomorphism onto a chosen model of the fibre product; the isomorphism
`V ≅ pullback (desc j₁ j₂ g₁ g₂ hg) t` the source asks for is its
`CategoryTheory.IsPullback.isoPullback`. The comparison morphism `V ⟶ glued j₁ j₂` is part of the
conclusion, together with its two chart identities.

## References

* [Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace SpanGlue

section Recognition

variable {W V V₁ V₂ : Scheme.{u}} (k₁ : W ⟶ V₁) (k₂ : W ⟶ V₂)
  [IsOpenImmersion k₁] [IsOpenImmersion k₂]
  (m₁ : V₁ ⟶ V) (m₂ : V₂ ⟶ V) [IsOpenImmersion m₁] [IsOpenImmersion m₂]
  (hm : k₁ ≫ m₁ = k₂ ≫ m₂)

/-- If a scheme `G` over `V` is covered by the images of `ia` and `ib`, which agree on `W`, and the
part of `B` over the image of `ma` is the image of `kb`, then the part of `G` over the image of `ma`
is the image of `ia`. -/
private theorem preimage_opensRange_eq_opensRange_of_cover {W A B G V : Scheme.{u}}
    (ka : W ⟶ A) (kb : W ⟶ B) (ma : A ⟶ V) (mb : B ⟶ V) (ia : A ⟶ G) (ib : B ⟶ G) (d : G ⟶ V)
    [IsOpenImmersion kb] [IsOpenImmersion ia] [IsOpenImmersion ma]
    (hda : ia ≫ d = ma) (hdb : ib ≫ d = mb)
    (hglue : ka ≫ ia = kb ≫ ib) (hcov : ∀ x, (∃ a, ia a = x) ∨ ∃ b, ib b = x)
    (hb : mb ⁻¹ᵁ ma.opensRange = kb.opensRange) :
    d ⁻¹ᵁ ma.opensRange = ia.opensRange := by
  ext x
  constructor
  · intro hx
    rcases hcov x with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact ⟨a, rfl⟩
    · have hb' : b ∈ mb ⁻¹ᵁ ma.opensRange := by
        change mb b ∈ ma.opensRange
        rw [← hdb, Scheme.Hom.comp_apply]
        exact hx
      rw [hb] at hb'
      obtain ⟨v, rfl⟩ := hb'
      refine ⟨ka v, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hglue]
  · rintro ⟨a, rfl⟩
    change _ ∈ ma.opensRange
    refine ⟨a, ?_⟩
    rw [← Scheme.Hom.comp_apply, hda]

omit [IsOpenImmersion m₂] in
/-- **The first chart of the glueing of two opens of a scheme is exactly the part of the glueing
lying over the first open.** -/
theorem preimage_opensRange_desc_eq_opensRange_ι₁
    (h₂ : m₂ ⁻¹ᵁ m₁.opensRange = k₂.opensRange) :
    desc k₁ k₂ m₁ m₂ hm ⁻¹ᵁ m₁.opensRange = (ι₁ k₁ k₂).opensRange :=
  preimage_opensRange_eq_opensRange_of_cover k₁ k₂ m₁ m₂ _ _ _ (ι₁_desc k₁ k₂ m₁ m₂ hm)
    (ι₂_desc k₁ k₂ m₁ m₂ hm) (glue_condition k₁ k₂) (ι_jointly_surjective k₁ k₂) h₂

omit [IsOpenImmersion m₁] in
/-- **The second chart of the glueing of two opens of a scheme is exactly the part of the
glueing lying over the second open.** -/
theorem preimage_opensRange_desc_eq_opensRange_ι₂
    (h₁ : m₁ ⁻¹ᵁ m₂.opensRange = k₁.opensRange) :
    desc k₁ k₂ m₁ m₂ hm ⁻¹ᵁ m₂.opensRange = (ι₂ k₁ k₂).opensRange :=
  preimage_opensRange_eq_opensRange_of_cover k₂ k₁ m₂ m₁ _ _ _ (ι₂_desc k₁ k₂ m₁ m₂ hm)
    (ι₁_desc k₁ k₂ m₁ m₂ hm) (glue_condition k₁ k₂).symm
    (fun x => (ι_jointly_surjective k₁ k₂ x).symm) h₁

/-- The restriction of a morphism to the image of an open immersion is an isomorphism as soon as
that open immersion is the projection of a pullback square whose other leg is an identity. -/
private theorem isIso_morphismRestrict_of_isPullback {G A B : Scheme.{u}} (d : G ⟶ B)
    (g : A ⟶ B) [IsOpenImmersion g] (p : A ⟶ G) (hp : IsPullback p (𝟙 A) d g) :
    IsIso (d ∣_ g.opensRange) := by
  rw [← MorphismProperty.isomorphisms.iff,
    (MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff (morphismRestrictOpensRange d g),
    MorphismProperty.isomorphisms.iff,
    show pullback.snd d g = hp.isoPullback.inv ≫ 𝟙 A from by
      rw [Iso.eq_inv_comp, IsPullback.isoPullback_hom_snd]]
  infer_instance

/-- **A scheme covered by two opens which meet exactly in the glueing datum is the glueing of
those two opens.** -/
theorem isIso_desc (hcov : m₁.opensRange ⊔ m₂.opensRange = ⊤)
    (h₁ : m₁ ⁻¹ᵁ m₂.opensRange = k₁.opensRange)
    (h₂ : m₂ ⁻¹ᵁ m₁.opensRange = k₂.opensRange) :
    IsIso (desc k₁ k₂ m₁ m₂ hm) := by
  have hp₁ : IsPullback (ι₁ k₁ k₂) (𝟙 V₁) (desc k₁ k₂ m₁ m₂ hm) m₁ :=
    (IsOpenImmersion.isPullback (𝟙 V₁) (ι₁ k₁ k₂) m₁ (desc k₁ k₂ m₁ m₂ hm)
      (by rw [Category.id_comp, ι₁_desc])
      (preimage_opensRange_desc_eq_opensRange_ι₁ k₁ k₂ m₁ m₂ hm h₂)).flip
  have hp₂ : IsPullback (ι₂ k₁ k₂) (𝟙 V₂) (desc k₁ k₂ m₁ m₂ hm) m₂ :=
    (IsOpenImmersion.isPullback (𝟙 V₂) (ι₂ k₁ k₂) m₂ (desc k₁ k₂ m₁ m₂ hm)
      (by rw [Category.id_comp, ι₂_desc])
      (preimage_opensRange_desc_eq_opensRange_ι₂ k₁ k₂ m₁ m₂ hm h₁)).flip
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme.{u})
    (fun b : Bool => cond b m₂.opensRange m₁.opensRange) ?_ fun b => ?_
  · rw [iSup_bool_eq]
    show m₂.opensRange ⊔ m₁.opensRange = ⊤
    rw [sup_comm]
    exact hcov
  · match b with
    | false => exact isIso_morphismRestrict_of_isPullback _ m₁ _ hp₁
    | true => exact isIso_morphismRestrict_of_isPullback _ m₂ _ hp₂

end Recognition

end SpanGlue

end AlgebraicGeometry

namespace Stacks.Etale

open AlgebraicGeometry AlgebraicGeometry.SpanGlue CategoryTheory CategoryTheory.Limits

/-- **The final glueing of Tag 0BTP.** Let `U` be glued from `U₁` and `U₂` along `Wb`, with
structure morphism to `S`, and let `t : X ⟶ S`. Let `V` be covered by two opens `V₁` and `V₂`
which are the fibre products of `U₁` and `U₂` with `X` over `S`, meeting exactly in the open `W`
lying over `Wb`. Then `V` is the fibre product of `U` with `X` over `S`, by the morphism
`V ⟶ U` glueing the two chart identifications.

In Tag 0BTP, `U₁` is the finite piece `U_fin`, `U₂` is the piece `U'` already produced over the
open `S'` of the base, `Wb` is `U_fin ×_S S'`, and `V` is the scheme of the descent datum. -/
theorem exists_isPullback_desc_of_charts {S X : Scheme.{u}} (t : X ⟶ S)
    {Wb U₁ U₂ : Scheme.{u}} (j₁ : Wb ⟶ U₁) (j₂ : Wb ⟶ U₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (g₁ : U₁ ⟶ S) (g₂ : U₂ ⟶ S) (hg : j₁ ≫ g₁ = j₂ ≫ g₂)
    {W V V₁ V₂ : Scheme.{u}} (k₁ : W ⟶ V₁) (k₂ : W ⟶ V₂)
    [IsOpenImmersion k₁] [IsOpenImmersion k₂]
    (m₁ : V₁ ⟶ V) (m₂ : V₂ ⟶ V) [IsOpenImmersion m₁] [IsOpenImmersion m₂]
    (c₁ : V₁ ⟶ U₁) (c₂ : V₂ ⟶ U₂) (n : V ⟶ X) (hm : k₁ ≫ m₁ = k₂ ≫ m₂)
    (hc : k₁ ≫ (c₁ ≫ ι₁ j₁ j₂) = k₂ ≫ (c₂ ≫ ι₂ j₁ j₂))
    (sq₁ : IsPullback c₁ (m₁ ≫ n) g₁ t) (sq₂ : IsPullback c₂ (m₂ ≫ n) g₂ t)
    (hW₁ : c₁ ⁻¹ᵁ j₁.opensRange = k₁.opensRange)
    (hW₂ : c₂ ⁻¹ᵁ j₂.opensRange = k₂.opensRange)
    (hcov : m₁.opensRange ⊔ m₂.opensRange = ⊤)
    (hV₁ : m₁ ⁻¹ᵁ m₂.opensRange = k₁.opensRange)
    (hV₂ : m₂ ⁻¹ᵁ m₁.opensRange = k₂.opensRange) :
    ∃ ρ : V ⟶ glued j₁ j₂, m₁ ≫ ρ = c₁ ≫ ι₁ j₁ j₂ ∧ m₂ ≫ ρ = c₂ ≫ ι₂ j₁ j₂ ∧
      IsPullback ρ n (desc j₁ j₂ g₁ g₂ hg) t := by
  have hn : k₁ ≫ (m₁ ≫ n) = k₂ ≫ (m₂ ≫ n) := by
    rw [← Category.assoc, ← Category.assoc, hm]
  have hd : IsIso (desc k₁ k₂ m₁ m₂ hm) := isIso_desc k₁ k₂ m₁ m₂ hm hcov hV₁ hV₂
  have hdn : desc k₁ k₂ (m₁ ≫ n) (m₂ ≫ n) hn = desc k₁ k₂ m₁ m₂ hm ≫ n :=
    (eq_desc k₁ k₂ (m₁ ≫ n) (m₂ ≫ n) hn
      (by rw [← Category.assoc, ι₁_desc]) (by rw [← Category.assoc, ι₂_desc])).symm
  have hsq := isPullback_desc j₁ j₂ k₁ k₂ c₁ c₂ (m₁ ≫ n) (m₂ ≫ n) hc g₁ g₂ hg t hn sq₁ sq₂
    hW₁ hW₂
  rw [hdn] at hsq
  refine ⟨CategoryTheory.inv (desc k₁ k₂ m₁ m₂ hm) ≫
    desc k₁ k₂ (c₁ ≫ ι₁ j₁ j₂) (c₂ ≫ ι₂ j₁ j₂) hc, ?_, ?_, ?_⟩
  · rw [← Category.assoc, ← (IsIso.eq_comp_inv _).2 (ι₁_desc k₁ k₂ m₁ m₂ hm), ι₁_desc]
  · rw [← Category.assoc, ← (IsIso.eq_comp_inv _).2 (ι₂_desc k₁ k₂ m₁ m₂ hm), ι₂_desc]
  · refine hsq.of_iso (asIso (desc k₁ k₂ m₁ m₂ hm)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_ <;> simp

end Stacks.Etale

end
