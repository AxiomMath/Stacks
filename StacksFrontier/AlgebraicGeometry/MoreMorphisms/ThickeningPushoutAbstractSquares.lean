module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushout07RXFlat
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutGluing

/-!
# Gluing flat schemes across a pushout, in terms of cartesian and cocartesian squares

Let `j₂ : S ⟶ S₂` be a thickening and `j₁ : S ⟶ S₁` an affine morphism of schemes, and let
`T` be presented as their pushout by an arbitrary cocartesian square. A scheme glued over `T`
from a triple of `Stacks.Pushout.gluingData j₂ j₁`, or from a pair of schemes over `S₁` and `S₂`
with cartesian squares identifying their restrictions to `S`, has the given schemes as its
restrictions to `S₁` and `S₂`. Conversely, a flat scheme over `T` is the pushout of its
restrictions.

## Main results

* `Stacks.Pushout.isPullback_restrictions_gluingData`: the two restrictions of the scheme glued
  from a triple are the two components of that triple, for an arbitrary cocartesian square
  presenting `Y'` and an arbitrary presentation of the glued scheme as a pushout.
* `Stacks.Pushout.isPullback_of_isPushout_glued`: the same, with the triple presented as a pair
  of schemes over the two pieces together with cartesian squares identifying their restrictions.
* `Stacks.Pushout.isPushout_restrictions_of_flat`: a flat scheme over the pushout is the pushout
  of its restrictions to the two pieces.

## References

* [Stacks Project, Tag 07RV](https://stacks.math.columbia.edu/tag/07RV)
* [Stacks Project, Tag 07RX](https://stacks.math.columbia.edu/tag/07RX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Pushout

open Stacks.Thickenings

variable {S S₁ S₂ T : Scheme.{u}} {j₂ : S ⟶ S₂} {j₁ : S ⟶ S₁} {b₂ : S₂ ⟶ T} {b₁ : S₁ ⟶ T}

/-- For a cocartesian square `IsPushout j₂ j₁ b₂ b₁` with `j₂` a thickening and `j₁` affine, a
triple `W` of `gluingData j₂ j₁`, a pushout `Z` of the span glued from `W`, and a morphism
`z : Z ⟶ T` restricting to the two structure morphisms of `W`, the two squares formed by `z`, the
structure morphisms of the components of `W` and the coprojections of `Z` are cartesian. -/
theorem isPullback_restrictions_gluingData (hj₂ : IsThickening j₂) [IsAffineHom j₁]
    (hpo : IsPushout j₂ j₁ b₂ b₁) (W : gluingData j₂ j₁)
    [HasPushout (pullback.fst W.obj.right.hom j₂) (gluingSourceMap j₂ j₁ W)]
    {Z : Scheme.{u}} {z : Z ⟶ T}
    {c₁ : W.obj.left.left ⟶ Z} {c₂ : W.obj.right.left ⟶ Z}
    (hZ : IsPushout (pullback.fst W.obj.right.hom j₂) (gluingSourceMap j₂ j₁ W) c₂ c₁)
    (hz₁ : c₁ ≫ z = W.obj.left.hom ≫ b₁) (hz₂ : c₂ ≫ z = W.obj.right.hom ≫ b₂) :
    IsPullback c₁ W.obj.left.hom z b₁ ∧ IsPullback c₂ W.obj.right.hom z b₂ := by
  have := hpo.hasPushout
  let eZ : pushout (pullback.fst W.obj.right.hom j₂) (gluingSourceMap j₂ j₁ W) ≅ Z :=
    (IsPushout.of_hasPushout _ _).isoIsPushout _ _ hZ
  have hinl : pushout.inl (pullback.fst W.obj.right.hom j₂) (gluingSourceMap j₂ j₁ W) ≫
      eZ.hom = c₂ := IsPushout.inl_isoIsPushout_hom _ _ _ _
  have hinr : pushout.inr (pullback.fst W.obj.right.hom j₂) (gluingSourceMap j₂ j₁ W) ≫
      eZ.hom = c₁ := IsPushout.inr_isoIsPushout_hom _ _ _ _
  have hstr : (gluingPushoutData j₂ j₁ W).hom ≫ hpo.isoPushout.inv = eZ.hom ≫ z := by
    apply (IsPushout.of_hasPushout
      (pullback.fst W.obj.right.hom j₂) (gluingSourceMap j₂ j₁ W)).hom_ext
    · rw [← Category.assoc, ← Category.assoc, hinl, gluingPushoutData_inl, hz₂,
        Category.assoc, hpo.inl_isoPushout_inv]
    · rw [← Category.assoc, ← Category.assoc, hinr, gluingPushoutData_inr, hz₁,
        Category.assoc, hpo.inr_isoPushout_inv]
  obtain ⟨hc₁, hc₂⟩ := gluing_components_isPullback j₂ j₁ hj₂ W
  refine ⟨hc₁.of_iso (Iso.refl _) eZ (Iso.refl _) hpo.isoPushout.symm ?_ ?_ hstr ?_,
    hc₂.of_iso (Iso.refl _) eZ (Iso.refl _) hpo.isoPushout.symm ?_ ?_ hstr ?_⟩
  · simpa using hinr
  · simp
  · simp
  · simpa using hinl
  · simp
  · simp

/-- The identification of the restrictions of `Y₁` and `Y₂` to `S` induced by cartesian squares
identifying both with `Y`. -/
private def isoOfPullbacks {Y Y₁ Y₂ : Scheme.{u}} {y : Y ⟶ S} {y₁ : Y₁ ⟶ S₁}
    {y₂ : Y₂ ⟶ S₂} {g₁ : Y ⟶ Y₁} {g₂ : Y ⟶ Y₂} [HasPullback y₁ j₁] [HasPullback y₂ j₂]
    (h₁ : IsPullback g₁ y y₁ j₁) (h₂ : IsPullback g₂ y y₂ j₂) :
    (Over.pullback j₁).obj (Over.mk y₁) ≅ (Over.pullback j₂).obj (Over.mk y₂) :=
  Over.isoMk (h₁.isoPullback.symm ≪≫ h₂.isoPullback)
    (by change (_ ≫ _) ≫ pullback.snd y₂ j₂ = pullback.snd y₁ j₁
        rw [Category.assoc, h₂.isoPullback_hom_snd, Iso.symm_hom, h₁.isoPullback_inv_snd])

/-- The triple of `gluingData j₂ j₁` formed by `Y₁` over `S₁` and `Y₂` over `S₂`. -/
private abbrev gluingDataOfPullbacks {Y Y₁ Y₂ : Scheme.{u}} {y : Y ⟶ S} {y₁ : Y₁ ⟶ S₁}
    {y₂ : Y₂ ⟶ S₂} {g₁ : Y ⟶ Y₁} {g₂ : Y ⟶ Y₂} [HasPullback y₁ j₁] [HasPullback y₂ j₂]
    (h₁ : IsPullback g₁ y y₁ j₁) (h₂ : IsPullback g₂ y y₂ j₂) : gluingData j₂ j₁ :=
  ⟨{ left := Over.mk y₁, right := Over.mk y₂, hom := (isoOfPullbacks h₁ h₂).hom },
    (isoOfPullbacks h₁ h₂).isIso_hom⟩

/-- The source map of `gluingDataOfPullbacks h₁ h₂` is `g₁`
up to the identification of the pullback of `y₂` and `j₂` with `Y`. -/
private theorem isoPullback_inv_comp_eq_gluingSourceMap {Y Y₁ Y₂ : Scheme.{u}} {y : Y ⟶ S}
    {y₁ : Y₁ ⟶ S₁} {y₂ : Y₂ ⟶ S₂} {g₁ : Y ⟶ Y₁} {g₂ : Y ⟶ Y₂} [HasPullback y₁ j₁]
    [HasPullback y₂ j₂] (h₁ : IsPullback g₁ y y₁ j₁) (h₂ : IsPullback g₂ y y₂ j₂) :
    h₂.isoPullback.inv ≫ g₁ = gluingSourceMap j₂ j₁ (gluingDataOfPullbacks h₁ h₂) := by
  change h₂.isoPullback.inv ≫ g₁ = (inv (isoOfPullbacks h₁ h₂).hom).left ≫ pullback.fst y₁ j₁
  rw [IsIso.Iso.inv_hom]
  simp [isoOfPullbacks]

/-- For a cocartesian square `IsPushout j₂ j₁ b₂ b₁` with `j₂` a thickening and `j₁` affine,
schemes `Y₁` over `S₁` and `Y₂` over `S₂` whose restrictions to `S` are identified with a common
scheme `Y` by cartesian squares `h₁` and `h₂`, a pushout `Z` of `Y₂ ← Y → Y₁`, and a morphism
`z : Z ⟶ T` restricting to `y₁` and `y₂`, the two squares formed by `z`, `y₁`, `y₂` and the
coprojections `c₁`, `c₂` are cartesian. -/
theorem isPullback_of_isPushout_glued (hj₂ : IsThickening j₂) [IsAffineHom j₁]
    (hpo : IsPushout j₂ j₁ b₂ b₁)
    {Y Y₁ Y₂ Z : Scheme.{u}} {y : Y ⟶ S} {y₁ : Y₁ ⟶ S₁} {y₂ : Y₂ ⟶ S₂} {z : Z ⟶ T}
    {g₁ : Y ⟶ Y₁} {g₂ : Y ⟶ Y₂} {c₁ : Y₁ ⟶ Z} {c₂ : Y₂ ⟶ Z}
    (h₁ : IsPullback g₁ y y₁ j₁) (h₂ : IsPullback g₂ y y₂ j₂)
    (hZ : IsPushout g₂ g₁ c₂ c₁)
    (hz₁ : c₁ ≫ z = y₁ ≫ b₁) (hz₂ : c₂ ≫ z = y₂ ≫ b₂) :
    IsPullback c₁ y₁ z b₁ ∧ IsPullback c₂ y₂ z b₂ := by
  have := h₁.hasPullback
  have := h₂.hasPullback
  have := hpo.hasPushout
  let W := gluingDataOfPullbacks (j₂ := j₂) h₁ h₂
  have := gluingHasPushout j₂ j₁ hj₂ W
  have hsnd := isoPullback_inv_comp_eq_gluingSourceMap h₁ h₂
  have hZ' : IsPushout (pullback.fst W.obj.right.hom j₂) (gluingSourceMap j₂ j₁ W) c₂ c₁ :=
    hZ.of_iso' h₂.isoPullback.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
          exact h₂.isoPullback_inv_fst)
      (by simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]; exact hsnd)
      (by simp) (by simp)
  exact isPullback_restrictions_gluingData hj₂ hpo W hZ' hz₁ hz₂

/-- For a cocartesian square `IsPushout j₂ j₁ b₂ b₁` with `j₂` a thickening and `j₁` affine, a flat
`w : W ⟶ T` whose restrictions to `S₁`, `S₂` and `S` are given by cartesian squares, with
`d₂ ≫ e₂ = d₁ ≫ e₁`, is the pushout of `W₂ ← W₀ → W₁`. -/
theorem isPushout_restrictions_of_flat (hj₂ : IsThickening j₂) [IsAffineHom j₁]
    (hpo : IsPushout j₂ j₁ b₂ b₁)
    {W W₀ W₁ W₂ : Scheme.{u}} {w : W ⟶ T} {w₀ : W₀ ⟶ S} {w₁ : W₁ ⟶ S₁} {w₂ : W₂ ⟶ S₂}
    {e₁ : W₁ ⟶ W} {e₂ : W₂ ⟶ W} {d₁ : W₀ ⟶ W₁} {d₂ : W₀ ⟶ W₂} (hw : Flat w)
    (hcomm : d₂ ≫ e₂ = d₁ ≫ e₁)
    (he₁ : IsPullback e₁ w₁ w b₁) (he₂ : IsPullback e₂ w₂ w b₂)
    (hd₁ : IsPullback d₁ w₀ w₁ j₁) (hd₂ : IsPullback d₂ w₀ w₂ j₂) :
    IsPushout d₂ d₁ e₂ e₁ := by
  have := hpo.hasPushout
  have := hd₁.hasPullback
  have := hd₂.hasPullback
  have := hw
  let V := gluingDataOfPullbacks (j₂ := j₂) hd₁ hd₂
  have := gluingHasPushout j₂ j₁ hj₂ V
  have hsnd : hd₂.isoPullback.inv ≫ d₁ = gluingSourceMap j₂ j₁ V :=
    isoPullback_inv_comp_eq_gluingSourceMap hd₁ hd₂
  let Z : Over (pushout j₂ j₁) := Over.mk (w ≫ hpo.isoPushout.hom)
  have he₁' : IsPullback e₁ w₁ (w ≫ hpo.isoPushout.hom) (pushout.inr j₂ j₁) :=
    he₁.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) hpo.isoPushout
      (by simp) (by simp) (by simp) (by simp)
  have he₂' : IsPullback e₂ w₂ (w ≫ hpo.isoPushout.hom) (pushout.inl j₂ j₁) :=
    he₂.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) hpo.isoPushout
      (by simp) (by simp) (by simp) (by simp)
  have hk0 : pullback.fst w₂ j₂ ≫ e₂ = gluingSourceMap j₂ j₁ V ≫ e₁ := by
    rw [← hsnd, ← hd₂.isoPullback_inv_fst, Category.assoc, Category.assoc, hcomm]
  have hk : pullback.fst V.obj.right.hom j₂ ≫ e₂ = gluingSourceMap j₂ j₁ V ≫ e₁ := hk0
  have hkw : pushout.desc e₂ e₁ hk ≫ Z.hom = ((gluingFunctor j₂ j₁ hj₂).obj V).hom := by
    refine (IsPushout.of_hasPushout
      (pullback.fst V.obj.right.hom j₂) (gluingSourceMap j₂ j₁ V)).hom_ext ?_ ?_
    · show (pushout.inl _ _ ≫ pushout.desc e₂ e₁ hk) ≫ Z.hom =
        pushout.inl _ _ ≫ (gluingPushoutData j₂ j₁ V).hom
      rw [pushout.inl_desc, gluingPushoutData_inl]
      show e₂ ≫ w ≫ hpo.isoPushout.hom = w₂ ≫ pushout.inl j₂ j₁
      rw [← Category.assoc, he₂.w, Category.assoc, hpo.inl_isoPushout_hom]
    · show (pushout.inr _ _ ≫ pushout.desc e₂ e₁ hk) ≫ Z.hom =
        pushout.inr _ _ ≫ (gluingPushoutData j₂ j₁ V).hom
      rw [pushout.inr_desc, gluingPushoutData_inr]
      show e₁ ≫ w ≫ hpo.isoPushout.hom = w₁ ≫ pushout.inr j₂ j₁
      rw [← Category.assoc, he₁.w, Category.assoc, hpo.inr_isoPushout_hom]
  let k : (gluingFunctor j₂ j₁ hj₂).obj V ⟶ Z := Over.homMk (pushout.desc e₂ e₁ hk) hkw
  have hpair : IsIso (gluingToPair j₂ j₁ hj₂ k) := by
    have hl : (gluingToPair j₂ j₁ hj₂ k).hom.left.left = he₁'.isoPullback.hom := by
      refine pullback.hom_ext ?_ ?_
      · exact (gluingToPair_left_comp_fst j₂ j₁ hj₂ k).trans
          ((pushout.inr_desc e₂ e₁ hk).trans he₁'.isoPullback_hom_fst.symm)
      · exact (gluingToPair_left_comp_snd j₂ j₁ hj₂ k).trans
          he₁'.isoPullback_hom_snd.symm
    have hr : (gluingToPair j₂ j₁ hj₂ k).hom.right.left = he₂'.isoPullback.hom := by
      refine pullback.hom_ext ?_ ?_
      · exact (gluingToPair_right_comp_fst j₂ j₁ hj₂ k).trans
          ((pushout.inl_desc e₂ e₁ hk).trans he₂'.isoPullback_hom_fst.symm)
      · exact (gluingToPair_right_comp_snd j₂ j₁ hj₂ k).trans
          he₂'.isoPullback_hom_snd.symm
    have : IsIso ((Over.forget S₁).map (gluingToPair j₂ j₁ hj₂ k).hom.left) := by
      show IsIso ((gluingToPair j₂ j₁ hj₂ k).hom.left.left)
      rw [hl]
      exact he₁'.isoPullback.isIso_hom
    have : IsIso ((Over.forget S₂).map (gluingToPair j₂ j₁ hj₂ k).hom.right) := by
      show IsIso ((gluingToPair j₂ j₁ hj₂ k).hom.right.left)
      rw [hr]
      exact he₂'.isoPullback.isIso_hom
    have : IsIso ((gluingToPair j₂ j₁ hj₂ k).hom.left) :=
      isIso_of_reflects_iso (gluingToPair j₂ j₁ hj₂ k).hom.left (Over.forget S₁)
    have : IsIso ((gluingToPair j₂ j₁ hj₂ k).hom.right) :=
      isIso_of_reflects_iso (gluingToPair j₂ j₁ hj₂ k).hom.right (Over.forget S₂)
    let ec := Comma.isoMk (asIso (gluingToPair j₂ j₁ hj₂ k).hom.left)
      (asIso (gluingToPair j₂ j₁ hj₂ k).hom.right) (gluingToPair j₂ j₁ hj₂ k).hom.w
    have hec : ec.hom = (gluingToPair j₂ j₁ hj₂ k).hom := by apply Comma.hom_ext <;> rfl
    have : IsIso (gluingToPair j₂ j₁ hj₂ k).hom := hec ▸ ec.isIso_hom
    exact (ObjectProperty.isIso_hom_iff _).mp inferInstance
  have hZflat : Flat Z.hom := by
    show Flat (w ≫ hpo.isoPushout.hom)
    infer_instance
  have : IsIso k := isIso_of_isIso_gluingToPair j₂ j₁ hj₂ k hZflat hpair
  have hkiso : IsIso k.left :=
    inferInstanceAs (IsIso ((Over.forget (pushout j₂ j₁)).map k))
  let eW : pushout (pullback.fst V.obj.right.hom j₂) (gluingSourceMap j₂ j₁ V) ≅ W :=
    @asIso _ _ _ _ k.left hkiso
  have hcan : IsPushout (pullback.fst V.obj.right.hom j₂) (gluingSourceMap j₂ j₁ V) e₂ e₁ := by
    refine (IsPushout.of_hasPushout
      (pullback.fst V.obj.right.hom j₂) (gluingSourceMap j₂ j₁ V)).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) eW (by simp) (by simp) ?_ ?_
    · simp only [Iso.refl_hom, Category.id_comp]
      exact pushout.inl_desc e₂ e₁ hk
    · simp only [Iso.refl_hom, Category.id_comp]
      exact pushout.inr_desc e₂ e₁ hk
  refine hcan.of_iso' hd₂.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    (by simp) (by simp)
  · simp only [Iso.refl_hom, Category.comp_id]
    exact hd₂.isoPullback_hom_fst
  · simp only [Iso.refl_hom, Category.comp_id, ← hsnd, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp]

end Stacks.Pushout

end
