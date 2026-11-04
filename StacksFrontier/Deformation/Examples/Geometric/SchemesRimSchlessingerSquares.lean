module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutAbstractSquares
public import StacksFrontier.Deformation.Examples.Geometric.SchemesRimSchlessinger

/-!
# The Rim-Schlessinger condition for flat families of schemes

Flat families of schemes over `𝒞_Λ` satisfy condition (RS), with no hypothesis. The two gluing
statements used are `Stacks.Pushout.isPullback_of_isPushout_glued` and
`Stacks.Pushout.isPushout_restrictions_of_flat`.

## Main results

* `Deformation.Examples.satisfiesRS_flatSchemeFamilyProjection`: flat families of schemes over
  `𝒞_Λ` satisfy condition (RS).

## References

* [Stacks Project, Tag 07RV](https://stacks.math.columbia.edu/tag/07RV)
* [Stacks Project, Tag 07RX](https://stacks.math.columbia.edu/tag/07RX)
* [Stacks Project, Tag 0DY7](https://stacks.math.columbia.edu/tag/0DY7)
* [Stacks Project, Tag 0DY8](https://stacks.math.columbia.edu/tag/0DY8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace Deformation.Examples

open Deformation.ArtinianLocalAlgCat Stacks.Thickenings

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The category of flat families of schemes over `𝒞_Λ` satisfies the Rim-Schlessinger condition
(RS). -/
@[stacks 0DY8 "condition (RS) for the category of flat scheme families of Example 0DY7, \
unconditionally. The two gluing clauses it rests on are the last assertion of Tag 07RV and the \
equivalence assertion of the closing paragraph of Tag 07RX, both proved in this repository: \
Stacks.Pushout.isPullback_of_isPushout_glued and \
Stacks.Pushout.isPushout_restrictions_of_flat. The pushout of spectra, the existence of the \
glued family, its flatness and both halves of the universal property are proved as well. The \
clause that the deformation category of a fixed scheme over k is a deformation category is \
Deformation.Examples.isDeformationCategory_schemeDeformationCategoryProjection"]
theorem satisfiesRS_flatSchemeFamilyProjection :
    SatisfiesRS (flatSchemeFamilyProjection.{u, v, w} (Λ := Λ) (k := k)) := by
  classical
  refine ⟨flatSchemeFamilyProjection_cofiberedInGroupoids, ?_⟩
  intro X₁ X₂ X f₁ f₂ h₂
  have hsurj : Function.Surjective f₂.base.hom := h₂
  let hor : Function.Surjective f₁.base.hom ∨ Function.Surjective f₂.base.hom := Or.inr hsurj
  let P : ArtinianLocalAlgCat.{u, v, w} Λ k := pullbackObj_of_surjective f₁.base f₂.base hor
  let q₁ : P ⟶ X₁.base := pullbackFst_of_surjective f₁.base f₂.base hor
  let q₂ : P ⟶ X₂.base := pullbackSnd_of_surjective f₁.base f₂.base hor
  have hbp : IsPullback q₁ q₂ f₁.base f₂.base := isPullback_of_surjective _ _ hor
  have hpo : IsPushout (baseSpecMap f₂.base) (baseSpecMap f₁.base)
      (baseSpecMap q₂) (baseSpecMap q₁) :=
    isPushout_baseSpecMap_of_surjective f₁.base f₂.base hsurj
  have hthick : IsFiniteOrderThickening (baseSpecMap f₂.base) :=
    isFiniteOrderThickening_baseSpecMap f₂.base hsurj
  have hiU : IsFiniteOrderThickening f₂.map :=
    isFiniteOrderThickening_of_isPullback f₂.cartesian hthick
  have hfU : IsAffineHom f₁.map :=
    MorphismProperty.of_isPullback f₁.cartesian.flip
      (inferInstanceAs (IsAffineHom (baseSpecMap f₁.base)))
  have : HasPushout f₂.map f₁.map :=
    Stacks.Pushout.hasPushout_of_isFiniteOrderThickening_of_isAffineHom f₂.map f₁.map hiU
  have hZpo : IsPushout f₂.map f₁.map (Limits.pushout.inl f₂.map f₁.map)
      (Limits.pushout.inr f₂.map f₁.map) := IsPushout.of_hasPushout _ _
  have hsq : ∀ {T : Scheme.{v}} (u₂ : _ ⟶ T) (u₁ : _ ⟶ T),
      baseSpecMap f₂.base ≫ u₂ = baseSpecMap f₁.base ≫ u₁ →
        f₂.map ≫ X₂.toBase ≫ u₂ = f₁.map ≫ X₁.toBase ≫ u₁ := fun u₂ u₁ h => by
    rw [← Category.assoc, ← Category.assoc, f₂.cartesian.w, f₁.cartesian.w,
      Category.assoc, Category.assoc, h]
  have hzw := hsq _ _ hpo.w
  set c₂ := Limits.pushout.inl f₂.map f₁.map
  set c₁ := Limits.pushout.inr f₂.map f₁.map
  set z := hZpo.desc (X₂.toBase ≫ baseSpecMap q₂) (X₁.toBase ≫ baseSpecMap q₁) hzw
  have hzc₂ : c₂ ≫ z = X₂.toBase ≫ baseSpecMap q₂ := hZpo.inl_desc _ _ _
  have hzc₁ : c₁ ≫ z = X₁.toBase ≫ baseSpecMap q₁ := hZpo.inr_desc _ _ _
  have hlow : HasPushout (baseSpecMap f₂.base) (baseSpecMap f₁.base) := hpo.hasPushout
  have hdw := hsq (pushout.inl (baseSpecMap f₂.base) (baseSpecMap f₁.base))
    (pushout.inr (baseSpecMap f₂.base) (baseSpecMap f₁.base)) pushout.condition
  have hd : Flat ((IsPushout.of_hasPushout f₂.map f₁.map).desc
      (X₂.toBase ≫ pushout.inl (baseSpecMap f₂.base) (baseSpecMap f₁.base))
      (X₁.toBase ≫ pushout.inr (baseSpecMap f₂.base) (baseSpecMap f₁.base)) hdw) :=
    flat_pushoutDesc_of_isFiniteOrderThickening hthick f₁.cartesian f₂.cartesian
      X₁.flat X₂.flat hdw
  have hzeq : z = (IsPushout.of_hasPushout f₂.map f₁.map).desc
      (X₂.toBase ≫ pushout.inl (baseSpecMap f₂.base) (baseSpecMap f₁.base))
      (X₁.toBase ≫ pushout.inr (baseSpecMap f₂.base) (baseSpecMap f₁.base)) hdw ≫
        hpo.isoPushout.inv := by
    refine hZpo.hom_ext ?_ ?_
    · rw [hzc₂, ← Category.assoc, (IsPushout.of_hasPushout f₂.map f₁.map).inl_desc,
        Category.assoc, hpo.inl_isoPushout_inv]
    · rw [hzc₁, ← Category.assoc, (IsPushout.of_hasPushout f₂.map f₁.map).inr_desc,
        Category.assoc, hpo.inr_isoPushout_inv]
  have hri : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{v}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hzflat : Flat z := by
    rw [hzeq]
    exact (MorphismProperty.cancel_right_of_respectsIso
      (@Flat : MorphismProperty Scheme.{v}) _ hpo.isoPushout.inv).mpr hd
  obtain ⟨hc₁, hc₂⟩ :=
    Stacks.Pushout.isPullback_of_isPushout_glued hthick.isThickening hpo
      f₁.cartesian f₂.cartesian hZpo hzc₁ hzc₂
  let ZF : FlatSchemeFamily.{u, v, w} Λ k :=
    { base := P, scheme := Limits.pushout f₂.map f₁.map, toBase := z, flat := hzflat }
  let a₁ : ZF ⟶ X₁ := { base := q₁, map := c₁, cartesian := hc₁ }
  let a₂ : ZF ⟶ X₂ := { base := q₂, map := c₂, cartesian := hc₂ }
  have hw : a₁ ≫ f₁ = a₂ ≫ f₂ :=
    FlatSchemeFamily.Hom.ext hbp.w hZpo.w.symm
  have hlift : ∀ t : Limits.PullbackCone f₁ f₂, ∃ m : t.pt ⟶ ZF,
      (m ≫ a₁ = t.fst ∧ m ≫ a₂ = t.snd) ∧
        ∀ m' : t.pt ⟶ ZF, (m' ≫ a₁ = t.fst ∧ m' ≫ a₂ = t.snd) → m' = m := by
    intro t
    have hbase : t.fst.base ≫ f₁.base = t.snd.base ≫ f₂.base :=
      congrArg (fun g : t.pt ⟶ X => g.base) t.condition
    have hmaps : f₁.map ≫ t.fst.map = f₂.map ≫ t.snd.map :=
      congrArg (fun g : t.pt ⟶ X => g.map) t.condition
    let b : t.pt.base ⟶ P := hbp.lift t.fst.base t.snd.base hbase
    have hb₁ : b ≫ q₁ = t.fst.base := hbp.lift_fst _ _ _
    have hb₂ : b ≫ q₂ = t.snd.base := hbp.lift_snd _ _ _
    let m : Limits.pushout f₂.map f₁.map ⟶ t.pt.scheme :=
      hZpo.desc t.snd.map t.fst.map hmaps.symm
    have hm₁ : c₁ ≫ m = t.fst.map := hZpo.inr_desc _ _ _
    have hm₂ : c₂ ≫ m = t.snd.map := hZpo.inl_desc _ _ _
    have := t.pt.flat
    have hWpb : IsPullback (Limits.pullback.fst t.pt.toBase (baseSpecMap b))
        (Limits.pullback.snd t.pt.toBase (baseSpecMap b)) t.pt.toBase (baseSpecMap b) :=
      IsPullback.of_hasPullback _ _
    have key : ∀ (Y : FlatSchemeFamily.{u, v, w} Λ k) (g : t.pt ⟶ Y) (q : P ⟶ Y.base),
        b ≫ q = g.base → ∃ e : Y.scheme ⟶ Limits.pullback t.pt.toBase (baseSpecMap b),
          e ≫ Limits.pullback.fst t.pt.toBase (baseSpecMap b) = g.map ∧
          e ≫ Limits.pullback.snd t.pt.toBase (baseSpecMap b) = Y.toBase ≫ baseSpecMap q ∧
          IsPullback e Y.toBase (Limits.pullback.snd t.pt.toBase (baseSpecMap b))
            (baseSpecMap q) := by
      intro Y g q hq
      have hout : IsPullback g.map Y.toBase t.pt.toBase (baseSpecMap q ≫ baseSpecMap b) := by
        rw [← baseSpecMap_comp, hq]
        exact g.cartesian
      refine ⟨hWpb.lift g.map (Y.toBase ≫ baseSpecMap q) (by rw [hout.w, Category.assoc]),
        hWpb.lift_fst _ _ _, hWpb.lift_snd _ _ _, ?_⟩
      exact IsPullback.of_right (by rw [hWpb.lift_fst]; exact hout) (hWpb.lift_snd _ _ _) hWpb
    obtain ⟨e₁, hef₁, hes₁, he₁⟩ := key X₁ t.fst q₁ hb₁
    obtain ⟨e₂, hef₂, hes₂, he₂⟩ := key X₂ t.snd q₂ hb₂
    have hcs : f₂.map ≫ e₂ = f₁.map ≫ e₁ :=
      hWpb.hom_ext (by simp [hef₁, hef₂, hmaps]) (by simp [hes₁, hes₂, hzw])
    have hWpush : IsPushout f₂.map f₁.map e₂ e₁ :=
      Stacks.Pushout.isPushout_restrictions_of_flat hthick.isThickening hpo inferInstance hcs
        he₁ he₂ f₁.cartesian f₂.cartesian
    have hθ : ∀ {T : Scheme.{v}} (r : _ ⟶ T) (s : Limits.pushout f₂.map f₁.map ⟶ T),
        e₂ ≫ r = c₂ ≫ s → e₁ ≫ r = c₁ ≫ s → (hZpo.isoIsPushout _ _ hWpush).hom ≫ r = s :=
      fun r s h₂ h₁ => hZpo.hom_ext
        (by rw [← Category.assoc, hZpo.inl_isoIsPushout_hom, h₂])
        (by rw [← Category.assoc, hZpo.inr_isoIsPushout_hom, h₁])
    have hθfst := hθ _ m (by rw [hef₂, hm₂]) (by rw [hef₁, hm₁])
    have hθsnd := hθ _ z (by rw [hes₂, hzc₂]) (by rw [hes₁, hzc₁])
    have hcart : IsPullback m z t.pt.toBase (baseSpecMap b) :=
      hWpb.of_iso (hZpo.isoIsPushout _ _ hWpush).symm (Iso.refl _) (Iso.refl _)
        (Iso.refl _) (by simp [← hθfst]) (by simp [← hθsnd]) (by simp) (by simp)
    refine ⟨{ base := b, map := m, cartesian := hcart }, ⟨?_, ?_⟩, ?_⟩
    · exact FlatSchemeFamily.Hom.ext hb₁ hm₁
    · exact FlatSchemeFamily.Hom.ext hb₂ hm₂
    · intro m' hm'
      have hb' : m'.base = b := by
        refine hbp.hom_ext ?_ ?_
        · exact (congrArg (fun g : t.pt ⟶ X₁ => g.base) hm'.1).trans hb₁.symm
        · exact (congrArg (fun g : t.pt ⟶ X₂ => g.base) hm'.2).trans hb₂.symm
      refine FlatSchemeFamily.Hom.ext hb' (hZpo.hom_ext ?_ ?_)
      · exact (congrArg (fun g : t.pt ⟶ X₂ => g.map) hm'.2).trans hm₂.symm
      · exact (congrArg (fun g : t.pt ⟶ X₁ => g.map) hm'.1).trans hm₁.symm
  refine ⟨Limits.PullbackCone.mk a₁ a₂ hw, ⟨?_⟩, ?_⟩
  · exact Limits.PullbackCone.IsLimit.mk hw (fun t => (hlift t).choose)
      (fun t => (hlift t).choose_spec.1.1) (fun t => (hlift t).choose_spec.1.2)
      fun t m' h₁ h₂ => (hlift t).choose_spec.2 m' ⟨h₁, h₂⟩
  · refine ⟨Limits.IsLimit.ofIsoLimit hbp.isLimit
      (Limits.PullbackCone.ext (Iso.refl _) ?_ ?_)⟩
    · show q₁ = 𝟙 _ ≫ q₁
      simp
    · show q₂ = 𝟙 _ ≫ q₂
      simp

end Deformation.Examples

end
