module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget

/-!
# Universally submersive morphisms are fpqc local on the base

A morphism of schemes is *submersive* when its underlying continuous map is a quotient map, and
*universally submersive* when every base change of it is submersive. This property is local on
the target for the fpqc topology.

## Main results

* `AlgebraicGeometry.universallyQuotientMap_descendsAlong_surjective_inf_flat_inf_quasiCompact`:
  universal submersiveness descends along surjective flat quasi-compact morphisms.
* `AlgebraicGeometry.universallyQuotientMap_isLocalAtTarget_fpqc`: universal submersiveness is
  fpqc local on the base.

## Implementation notes

Submersiveness is the topological property `Topology.IsQuotientMap` of the underlying map, so it
is `AlgebraicGeometry.topologically @Topology.IsQuotientMap`, and universal submersiveness is its
`CategoryTheory.MorphismProperty.universally`. The latter is automatically stable under base
change, and Zariski locality on the target reduces to the same statement for submersiveness
itself, which is the elementary fact that a continuous surjection whose restrictions over an open
cover of the target are quotient maps is a quotient map.

For the descent step along a surjective flat quasi-compact `g`, fix a base change of the
morphism being descended. Its own base change along the base change of `g` is a base change of
the base change of `f` along `g`, hence submersive by hypothesis; composing with the base change
of `g`, which is a quotient map because it is flat and surjective
(`AlgebraicGeometry.Flat.isQuotientMap_of_surjective`), exhibits the original base change
precomposed with a continuous map as a quotient map, and `Topology.IsQuotientMap.of_comp`
finishes.

## References

* [Stacks Project, Tag 0CEW](https://stacks.math.columbia.edu/tag/0CEW)
-/

@[expose] public section

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

universe u

/-- Submersiveness of morphisms of schemes is invariant under isomorphism. -/
private lemma quotientMap_respectsIso :
    (topologically @Topology.IsQuotientMap : MorphismProperty Scheme.{u}).RespectsIso := by
  apply topologically_respectsIso
  · exact fun e ↦ e.isQuotientMap
  · exact fun _ _ hf hg ↦ hg.comp hf

/-- Submersiveness of morphisms of schemes is Zariski local on the target. -/
private lemma quotientMap_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget
      (topologically @Topology.IsQuotientMap : MorphismProperty Scheme.{u}) := by
  have := quotientMap_respectsIso.{u}
  apply topologically_isZariskiLocalAtTarget'
  intro α β _ _ f ι U hU hf
  refine ⟨fun h i ↦ h.restrictPreimage_isOpen (U i).2, fun h ↦ ?_⟩
  rw [Topology.isQuotientMap_iff]
  refine ⟨Topology.IsCoinducing.of_isOpen_preimage_iff_isOpen fun s ↦ ⟨fun hs ↦ ?_,
    fun hs ↦ hs.preimage hf⟩, fun y ↦ ?_⟩
  · refine hU.isOpen_iff_coe_preimage.mpr fun i ↦ ((h i).isCoinducing.isOpen_preimage).mp ?_
    simpa [Set.restrictPreimage, Set.preimage_preimage, Function.comp_def] using
      hs.preimage (continuous_subtype_val : Continuous (Subtype.val : f ⁻¹' (U i : Set β) → α))
  · obtain ⟨i, hy⟩ := hU.exists_mem y
    obtain ⟨x, hx⟩ := (h i).surjective ⟨y, hy⟩
    exact ⟨x.val, congrArg Subtype.val hx⟩

/-- Universal submersiveness of morphisms of schemes is Zariski local on the target. -/
private lemma universallyQuotientMap_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget
      ((topologically @Topology.IsQuotientMap : MorphismProperty Scheme.{u}).universally) := by
  have := quotientMap_isZariskiLocalAtTarget.{u}
  apply universally_isZariskiLocalAtTarget
  intro X Y f ι U hU hf
  exact IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := (topologically @Topology.IsQuotientMap : MorphismProperty Scheme.{u}))
    U hU.iSup_eq_top hf

/-- Universal submersiveness descends along surjective flat quasi-compact morphisms: if the base
change of `g` along such a morphism is universally submersive, then so is `g`. -/
@[ega "IV 15.7.11.1" "partial"]
instance universallyQuotientMap_descendsAlong_surjective_inf_flat_inf_quasiCompact :
    MorphismProperty.DescendsAlong
      ((topologically @Topology.IsQuotientMap : MorphismProperty Scheme.{u}).universally)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have := quotientMap_respectsIso.{u}
  apply MorphismProperty.DescendsAlong.mk'
  intro X Y Z f g _ hf hfst
  apply MorphismProperty.universally_mk'
    (topologically @Topology.IsQuotientMap : MorphismProperty Scheme.{u}) g
  intro T t _
  obtain ⟨⟨hsurj, hflat⟩, hqc⟩ := hf
  have _ : Surjective f := hsurj
  have _ : Flat f := hflat
  have _ : QuasiCompact f := hqc
  let e : pullback (pullback.snd f t) (pullback.snd g t) ≅
      pullback (pullback.fst f g) (pullback.fst f t) :=
    pullbackLeftPullbackSndIso f t (pullback.snd g t) ≪≫
      pullback.congrHom rfl pullback.condition.symm ≪≫
      (pullbackAssoc f g g t).symm ≪≫ pullback.congrHom pullback.condition.symm rfl ≪≫
      (pullbackRightPullbackFstIso f t (pullback.fst f g)).symm
  have heq : e.hom ≫ pullback.snd (pullback.fst f g) (pullback.fst f t) =
      pullback.fst (pullback.snd f t) (pullback.snd g t) := by
    refine pullback.hom_ext ?_ ?_ <;>
      simp only [e, Iso.trans_hom, Iso.symm_hom, pullback.congrHom_hom, pullback.map,
        Category.assoc]
    · rw [pullbackRightPullbackFstIso_inv_snd_fst, pullback.lift_fst_assoc]
      simp only [Category.comp_id]
      rw [pullbackAssoc_inv_fst_fst, pullback.lift_fst]
      simp only [pullbackLeftPullbackSndIso_hom_fst]
    · rw [pullbackRightPullbackFstIso_inv_snd_snd, pullback.lift_snd]
      simp only [Category.comp_id]
      rw [pullbackAssoc_inv_snd]
      simp only [pullback.condition]
      rw [pullback.lift_snd_assoc, pullbackLeftPullbackSndIso_hom_snd_assoc]
  -- The second projection of the pasted square is a base change of `pullback.fst f g`.
  have htop : Topology.IsQuotientMap
      (pullback.snd (pullback.fst f g) (pullback.fst f t)).base :=
    hfst _ _ _ (IsPullback.of_hasPullback _ _).flip
  have he : Topology.IsQuotientMap e.hom.base :=
    (TopCat.homeoOfIso (asIso e.hom.base)).isQuotientMap
  have hright : Topology.IsQuotientMap (pullback.snd f t).base :=
    Flat.isQuotientMap_of_surjective _
  have hcomp : Topology.IsQuotientMap
      (pullback.snd (pullback.snd f t) (pullback.snd g t) ≫ pullback.snd g t).base := by
    rw [show pullback.snd (pullback.snd f t) (pullback.snd g t) ≫ pullback.snd g t =
      pullback.fst (pullback.snd f t) (pullback.snd g t) ≫ pullback.snd f t from
      pullback.condition.symm, Scheme.Hom.comp_base, ← heq, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact hright.comp (htop.comp he)
  have hsnd : Topology.IsQuotientMap (pullback.snd g t).base :=
    Topology.IsQuotientMap.of_comp
      (Scheme.Hom.continuous (pullback.snd (pullback.snd f t) (pullback.snd g t)))
      (Scheme.Hom.continuous _) hcomp
  have hsymm : Topology.IsQuotientMap (pullbackSymmetry g t).hom.base :=
    (TopCat.homeoOfIso (asIso (pullbackSymmetry g t).hom.base)).isQuotientMap
  refine Topology.IsQuotientMap.of_comp_isQuotientMap hsymm ?_
  change Topology.IsQuotientMap ((pullbackSymmetry g t).hom ≫ pullback.fst t g).base
  rw [pullbackSymmetry_hom_comp_fst]
  exact hsnd

/-- **Stacks Project, Tag 0CEW.** Universal submersiveness of morphisms of schemes is fpqc local
on the base. -/
@[stacks 0CEW, ega "IV 15.7.11.1" "partial"]
instance universallyQuotientMap_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget
      ((topologically @Topology.IsQuotientMap : MorphismProperty Scheme.{u}).universally)
      Scheme.fpqcPrecoverage :=
  have := universallyQuotientMap_isZariskiLocalAtTarget.{u}
  have := Stacks.Descent.isStableUnderFlatBaseChange_of_isStableUnderBaseChange
    ((topologically @Topology.IsQuotientMap : MorphismProperty Scheme.{u}).universally)
  Stacks.Descent.isLocalAtTarget_fpqcPrecoverage _

end AlgebraicGeometry

end
