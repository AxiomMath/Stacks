module

public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.CutOut

/-!
# A scheme is the glueing of two covering opens along their intersection

Let `U₁` and `U₂` be opens of a scheme `S` with `U₁ ⊔ U₂ = ⊤`.  Then the canonical morphism from
the glueing of `U₁` and `U₂` along `U₁ ⊓ U₂` to `S` is an isomorphism.

This is the statement that the upper right square in the proof of Tag 07RN is a pushout.
Through this isomorphism a morphism out of the glueing is given by
`AlgebraicGeometry.Scheme.gluePairDesc`, whose condition is a single equation, rather than by
`glueMorphisms` over `AlgebraicGeometry.Scheme.openCoverOfIsOpenCover`, whose condition is one
equation for every ordered pair of members of the cover.

## Main results

* `AlgebraicGeometry.Scheme.gluePairOpensHom` is the canonical morphism, by
  `AlgebraicGeometry.Scheme.gluePairDesc` of the two inclusions; its single condition is that
  both restrictions of the inclusion of the intersection agree, which is
  `AlgebraicGeometry.Scheme.homOfLE_ι` twice.

* `AlgebraicGeometry.Scheme.injective_gluePairOpensHom`: the canonical morphism is injective.
  A point of the glueing is on one of the two legs, and two points on *different* legs with the
  same image in `S` lie over a point of the intersection, which the glueing has already identified
  (`AlgebraicGeometry.Scheme.gluePairInl_eq_gluePairInr_iff`).

* `AlgebraicGeometry.Scheme.isOpenImmersion_gluePairOpensHom` is then Mathlib's
  `AlgebraicGeometry.IsOpenImmersion.of_forall_source_exists` on the two legs, over each of which
  the morphism is an inclusion of an open; and
  `AlgebraicGeometry.Scheme.opensRange_gluePairOpensHom` computes its image as `U₁ ⊔ U₂`.

* `AlgebraicGeometry.Scheme.gluePairOpensIso` is the isomorphism: the morphism is an open
  immersion onto its image, the image is `⊤`, and `AlgebraicGeometry.Scheme.isoOfEq` with
  `AlgebraicGeometry.Scheme.topIso` carry that to `S`.
  `AlgebraicGeometry.Scheme.gluePairOpensIso_hom` records that the forward direction is the
  canonical morphism itself.

## Implementation notes

* `AlgebraicGeometry.Scheme.homOfLE` is defined through `IsOpenImmersion.lift`, so its action on
  a point is **not** reduced by reflexivity.  Mathlib's `AlgebraicGeometry.Scheme.homOfLE_apply`
  is the equation that moves a point through a restriction, and every step here that does so goes
  through it.

* Membership in the image of a morphism is an existential over the source, so the two inclusions
  of `AlgebraicGeometry.Scheme.opensRange_gluePairOpensHom` are proved pointwise; no rewrite
  reaches inside one.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u}) (U₁ U₂ : S.Opens)

/-- The canonical morphism to `S` from the glueing of two opens along their intersection. -/
noncomputable def gluePairOpensHom :
    gluePair (S.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁))
        (S.homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) ⟶ S :=
  gluePairDesc _ _ U₁.ι U₂.ι (by rw [S.homOfLE_ι, S.homOfLE_ι])

/-- The canonical morphism restricts to the inclusion of the first open on the first leg. -/
@[simp]
lemma gluePairInl_gluePairOpensHom :
    gluePairInl (S.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁))
        (S.homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) ≫ gluePairOpensHom S U₁ U₂ = U₁.ι :=
  gluePairInl_desc _ _ _ _ _

/-- The canonical morphism restricts to the inclusion of the second open on the second leg. -/
@[simp]
lemma gluePairInr_gluePairOpensHom :
    gluePairInr (S.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁))
        (S.homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) ≫ gluePairOpensHom S U₁ U₂ = U₂.ι :=
  gluePairInr_desc _ _ _ _ _

/-- The canonical morphism sends a point of the first leg to the underlying point of `S`. -/
lemma gluePairOpensHom_inl_apply (p : (U₁ : Scheme.{u})) :
    gluePairOpensHom S U₁ U₂ (gluePairInl _ _ p) = p.1 :=
  congrArg (fun k : (U₁ : Scheme.{u}) ⟶ S ↦ k p) (gluePairInl_gluePairOpensHom S U₁ U₂)

/-- The canonical morphism sends a point of the second leg to the underlying point of `S`. -/
lemma gluePairOpensHom_inr_apply (q : (U₂ : Scheme.{u})) :
    gluePairOpensHom S U₁ U₂ (gluePairInr _ _ q) = q.1 :=
  congrArg (fun k : (U₂ : Scheme.{u}) ⟶ S ↦ k q) (gluePairInr_gluePairOpensHom S U₁ U₂)

/-- **Two points of the two opens with the same image are already identified in the glueing.** -/
lemma gluePairInl_eq_gluePairInr_of_val_eq (p : (U₁ : Scheme.{u})) (q : (U₂ : Scheme.{u}))
    (hpq : p.1 = q.1) :
    gluePairInl (S.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁))
        (S.homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) p =
      gluePairInr (S.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁))
        (S.homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) q := by
  have hp2 : p.1 ∈ U₂ := by rw [hpq]; exact q.2
  refine (gluePairInl_eq_gluePairInr_iff _ _).mpr
    ⟨⟨p.1, ⟨p.2, hp2⟩⟩, Subtype.ext ?_, Subtype.ext ?_⟩
  · exact Scheme.homOfLE_apply _ _
  · exact (Scheme.homOfLE_apply _ _).trans hpq

/-- **The canonical morphism from the glueing of two opens is injective.**  Two points on
different legs with the same image lie over a point of the intersection, which the glueing has
already identified. -/
lemma injective_gluePairOpensHom : Function.Injective (gluePairOpensHom S U₁ U₂) := by
  have hcross := gluePairInl_eq_gluePairInr_of_val_eq S U₁ U₂
  intro t t' htt
  obtain ⟨p, rfl⟩ | ⟨q, rfl⟩ := gluePair_jointly_surjective _ _ t <;>
    obtain ⟨p', rfl⟩ | ⟨q', rfl⟩ := gluePair_jointly_surjective _ _ t' <;>
    simp only [gluePairOpensHom_inl_apply, gluePairOpensHom_inr_apply] at htt
  · exact congrArg _ (Subtype.ext htt)
  · exact hcross p q' htt
  · exact (hcross p' q htt.symm).symm
  · exact congrArg _ (Subtype.ext htt)

/-- The canonical morphism from the glueing of two opens is an open immersion. -/
instance isOpenImmersion_gluePairOpensHom : IsOpenImmersion (gluePairOpensHom S U₁ U₂) := by
  refine IsOpenImmersion.of_forall_source_exists _ (injective_gluePairOpensHom S U₁ U₂) fun t ↦ ?_
  obtain ⟨p, rfl⟩ | ⟨q, rfl⟩ := gluePair_jointly_surjective _ _ t
  · refine ⟨_, gluePairInl _ _, inferInstance, ⟨p, rfl⟩, ?_⟩
    rw [gluePairInl_gluePairOpensHom]
    infer_instance
  · refine ⟨_, gluePairInr _ _, inferInstance, ⟨q, rfl⟩, ?_⟩
    rw [gluePairInr_gluePairOpensHom]
    infer_instance

/-- **The image of the canonical morphism from the glueing of two opens is their union.** -/
lemma opensRange_gluePairOpensHom : (gluePairOpensHom S U₁ U₂).opensRange = U₁ ⊔ U₂ := by
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨t, rfl⟩ := hx
    obtain ⟨p, rfl⟩ | ⟨q, rfl⟩ := gluePair_jointly_surjective _ _ t
    · exact Opens.mem_sup.mpr (Or.inl ((gluePairOpensHom_inl_apply S U₁ U₂ p) ▸ p.2))
    · exact Opens.mem_sup.mpr (Or.inr ((gluePairOpensHom_inr_apply S U₁ U₂ q) ▸ q.2))
  · rcases Opens.mem_sup.mp hx with h | h
    · exact ⟨gluePairInl _ _ ⟨x, h⟩, gluePairOpensHom_inl_apply S U₁ U₂ ⟨x, h⟩⟩
    · exact ⟨gluePairInr _ _ ⟨x, h⟩, gluePairOpensHom_inr_apply S U₁ U₂ ⟨x, h⟩⟩

/-- **A scheme is the glueing of two covering opens along their intersection.**  This is the
pushout square of the Stacks proof of Tag 07RN. -/
noncomputable def gluePairOpensIso (h : U₁ ⊔ U₂ = ⊤) :
    gluePair (S.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁))
        (S.homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) ≅ S :=
  (gluePairOpensHom S U₁ U₂).isoOpensRange ≪≫
    S.isoOfEq ((opensRange_gluePairOpensHom S U₁ U₂).trans h) ≪≫ S.topIso

/-- The forward direction of `AlgebraicGeometry.Scheme.gluePairOpensIso` is the canonical
morphism. -/
@[simp]
lemma gluePairOpensIso_hom (h : U₁ ⊔ U₂ = ⊤) :
    (gluePairOpensIso S U₁ U₂ h).hom = gluePairOpensHom S U₁ U₂ := by
  simp [gluePairOpensIso]

/-- **The first open is the preimage of the image of the first leg.** -/
lemma preimage_gluePairOpensHom_left :
    gluePairOpensHom S U₁ U₂ ⁻¹ᵁ U₁ =
      (gluePairInl (S.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁))
        (S.homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂))).opensRange := by
  refine le_antisymm (fun t ht ↦ ?_) (fun t ht ↦ ?_)
  · obtain ⟨p, rfl⟩ | ⟨q, rfl⟩ := gluePair_jointly_surjective _ _ t
    · exact ⟨p, rfl⟩
    · have hq : q.1 ∈ U₁ := (gluePairOpensHom_inr_apply S U₁ U₂ q) ▸ ht
      exact ⟨⟨q.1, hq⟩, gluePairInl_eq_gluePairInr_of_val_eq S U₁ U₂ ⟨q.1, hq⟩ q rfl⟩
  · obtain ⟨p, rfl⟩ := ht
    change gluePairOpensHom S U₁ U₂ (gluePairInl _ _ p) ∈ U₁
    rw [gluePairOpensHom_inl_apply]
    exact p.2

/-- **The second open is the preimage of the image of the second leg.** -/
lemma preimage_gluePairOpensHom_right :
    gluePairOpensHom S U₁ U₂ ⁻¹ᵁ U₂ =
      (gluePairInr (S.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁))
        (S.homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂))).opensRange := by
  refine le_antisymm (fun t ht ↦ ?_) (fun t ht ↦ ?_)
  · obtain ⟨p, rfl⟩ | ⟨q, rfl⟩ := gluePair_jointly_surjective _ _ t
    · have hp : p.1 ∈ U₂ := (gluePairOpensHom_inl_apply S U₁ U₂ p) ▸ ht
      exact ⟨⟨p.1, hp⟩, (gluePairInl_eq_gluePairInr_of_val_eq S U₁ U₂ p ⟨p.1, hp⟩ rfl).symm⟩
    · exact ⟨q, rfl⟩
  · obtain ⟨q, rfl⟩ := ht
    change gluePairOpensHom S U₁ U₂ (gluePairInr _ _ q) ∈ U₂
    rw [gluePairOpensHom_inr_apply]
    exact q.2

end AlgebraicGeometry.Scheme
