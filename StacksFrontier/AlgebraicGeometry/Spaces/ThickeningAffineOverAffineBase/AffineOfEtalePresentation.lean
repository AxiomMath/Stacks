module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningAffineOverAffineBase.EtaleImageFactorization

/-!
# An algebraic space presented étale-locally over an affine scheme by an affine chart

Let `X` be an algebraic space over `S`, let `φ : X ⟶ h_Y` be a morphism to a represented
presheaf and let `ψ : Y' ⟶ Y` be an étale morphism of the site with affine source.  Suppose
that `X` has a surjective étale chart `w : h_W ⟶ X` whose composite with `φ` factors through
`ψ`, and that the base change `X ×_Y Y'` is an affine algebraic space.  Then `X` is
represented by a scheme: it lies over the open image `Y°` of `ψ`, the cover `Y' ⟶ Y°` is
surjective and étale, and the base change of `X ⟶ Y°` along it is affine, so `X ⟶ Y°` is
affine by Stacks 03WG.

If in addition `X` maps to an affine object `T` of the site and the base change of `X` along a
thickening `T₀ ⟶ T` is affine, then `X` itself is affine, by Stacks 06AD for the scheme
representing `X`.

This is the last step of the proof of Stacks 07SQ in the source, in the form in which it is
used to show that an algebraic space over an affine base whose base change to a thickening of
the base is affine is affine.

## Main results

* `AlgebraicGeometry.Space.exists_iso_yoneda_of_etalePresentation`: `X` is represented.
* `AlgebraicGeometry.Space.isAffineSpace_of_iso_yoneda_of_isThickening`: a represented algebraic
  space over an affine base whose base change to a thickening of the base is affine is affine.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
private instance hasPullbacks_presheaf_affineOfEtalePresentation :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf_affineOfEtalePresentation
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- The image of a morphism of the site into `Y` lies in the image of `ψ` as soon as some
surjective chart composed with it factors through `ψ`. -/
theorem range_subset_range_of_factor {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Y Y' W : BigFppfOver B S hS} (φ : X ⟶ yoneda.obj Y) (ψ : Y' ⟶ Y)
    (w : yoneda.obj W ⟶ X)
    (hw : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf w)
    (β : W ⟶ Y') (hβ : w ≫ φ = yoneda.map (β ≫ ψ))
    {V : BigFppfOver B S hS} (x : yoneda.obj V ⟶ X) :
    Set.range ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (x ≫ φ))) ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map ψ) := by
  rintro _ ⟨v, rfl⟩
  have hsq := hw.rep.isPullback x
  have hsurj : Surjective ((BigFppfOver.toScheme B S hS).map (hw.rep.snd x)) :=
    hw.property_snd x
  obtain ⟨q, rfl⟩ := hsurj.surj v
  have heq : hw.rep.snd x ≫ yoneda.preimage (x ≫ φ) =
      yoneda.preimage (hw.rep.fst x) ≫ β ≫ ψ := by
    apply yoneda.map_injective
    simp only [Functor.map_comp, Functor.map_preimage]
    rw [← Category.assoc, ← hsq.w, Category.assoc, hβ, Functor.map_comp]
  refine ⟨(BigFppfOver.toScheme B S hS).map (yoneda.preimage (hw.rep.fst x) ≫ β) q, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, Category.assoc, ← heq, Functor.map_comp,
    Scheme.Hom.comp_apply]

section Factor

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Y Y' W : BigFppfOver B S hS}
  (φ : X ⟶ yoneda.obj Y) (ψ : Y' ⟶ Y) [Etale ((BigFppfOver.toScheme B S hS).map ψ)]
  (w : yoneda.obj W ⟶ X)
  (hw : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf w)
  (β : W ⟶ Y') (hβ : w ≫ φ = yoneda.map (β ≫ ψ))

/-- The inclusion of the open image of `ψ` into `Y` is a monomorphism of the site. -/
theorem etaleOpenImageι_cancel {V : BigFppfOver B S hS} {a b : V ⟶ etaleOpenImage B S hS ψ}
    (h : a ≫ etaleOpenImageι B S hS ψ = b ≫ etaleOpenImageι B S hS ψ) : a = b := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [← cancel_mono ((BigFppfOver.toScheme B S hS).map (etaleOpenImageι B S hS ψ)),
    ← Functor.map_comp, ← Functor.map_comp, h]

omit [Etale ((BigFppfOver.toScheme B S hS).map ψ)] in
include hw hβ in
/-- The image of `φ.app V x`, as a morphism of schemes into `Y`, lies in the image of `ψ`. -/
theorem range_app_subset (V : (BigFppfOver B S hS)ᵒᵖ) (x : X.obj V) :
    Set.range ((BigFppfOver.toScheme B S hS).map (φ.app V x)) ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map ψ) := by
  have h := range_subset_range_of_factor B S hS φ ψ w hw β hβ (yonedaEquiv.symm x)
  have he : yoneda.preimage (yonedaEquiv.symm x ≫ φ) = φ.app V x := by
    apply yoneda.map_injective
    rw [Functor.map_preimage]
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]
  rwa [he] at h

/-- The factorization of `φ` through the open image of `ψ`. -/
def factorThroughEtaleOpenImage : X ⟶ yoneda.obj (etaleOpenImage B S hS ψ) where
  app V := TypeCat.ofHom fun x : X.obj V ↦
    etaleOpenImageFactor B S hS ψ (φ.app V x) (range_app_subset B S hS φ ψ w hw β hβ V x)
  naturality V V' g := by
    ext x
    apply etaleOpenImageι_cancel B S hS ψ
    have hn := NatTrans.naturality_apply φ g x
    change etaleOpenImageFactor B S hS ψ (φ.app V' (X.map g x))
        (range_app_subset B S hS φ ψ w hw β hβ V' (X.map g x)) ≫ etaleOpenImageι B S hS ψ =
      (g.unop ≫ etaleOpenImageFactor B S hS ψ (φ.app V x)
        (range_app_subset B S hS φ ψ w hw β hβ V x)) ≫ etaleOpenImageι B S hS ψ
    rw [Category.assoc, etaleOpenImageFactor_comp_ι, etaleOpenImageFactor_comp_ι]
    exact hn

/-- The factorization of `φ` through the open image of `ψ`, followed by the inclusion of the open
image into `Y`, is `φ`. -/
theorem factorThroughEtaleOpenImage_comp :
    factorThroughEtaleOpenImage B S hS φ ψ w hw β hβ ≫ yoneda.map (etaleOpenImageι B S hS ψ) =
      φ := by
  ext V x
  show etaleOpenImageFactor B S hS ψ (φ.app V x)
    (range_app_subset B S hS φ ψ w hw β hβ V x) ≫ etaleOpenImageι B S hS ψ = φ.app V x
  exact etaleOpenImageFactor_comp_ι B S hS ψ _ _

end Factor

set_option synthInstance.maxHeartbeats 400000 in
/-- **An algebraic space presented étale-locally by an affine chart is represented by a
scheme.** -/
theorem exists_iso_yoneda_of_etalePresentation {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {Y Y' W : BigFppfOver B S hS}
    (φ : X ⟶ yoneda.obj Y) (ψ : Y' ⟶ Y) [Etale ((BigFppfOver.toScheme B S hS).map ψ)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Y')]
    (w : yoneda.obj W ⟶ X)
    (hw : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf w)
    (β : W ⟶ Y') (hβ : w ≫ φ = yoneda.map (β ≫ ψ))
    (hV : IsAffineSpace B S hS (pullback φ (yoneda.map ψ))) :
    ∃ Z : BigFppfOver B S hS, Nonempty (X ≅ yoneda.obj Z) := by
  set φ' := factorThroughEtaleOpenImage B S hS φ ψ w hw β hβ
  set ι := etaleOpenImageι B S hS ψ
  set ψ' := etaleOpenImageLift B S hS ψ
  have hφ' : φ' ≫ yoneda.map ι = φ := factorThroughEtaleOpenImage_comp B S hS φ ψ w hw β hβ
  have hψ' : ψ' ≫ ι = ψ := etaleOpenImageLift_comp_ι B S hS ψ
  -- the base change along `ψ'` is the base change along `ψ`
  have hmono : Mono (yoneda.map ι) := by
    constructor
    intro Z a b h
    ext V x
    exact etaleOpenImageι_cancel B S hS ψ (congrArg (fun k ↦ k.app V x) h)
  have hpb : IsPullback (pullback.fst φ' (yoneda.map ψ')) (pullback.snd φ' (yoneda.map ψ'))
      φ (yoneda.map ψ) := by
    have h0 := IsPullback.of_hasPullback φ' (yoneda.map ψ')
    have hψy : yoneda.map ψ' ≫ yoneda.map ι = yoneda.map ψ := by
      rw [← Functor.map_comp]; exact congrArg _ hψ'
    have hw0 : pullback.fst φ' (yoneda.map ψ') ≫ φ = pullback.snd φ' (yoneda.map ψ') ≫
        yoneda.map ψ := by
      rw [← hφ', ← hψy, ← Category.assoc, h0.w, Category.assoc]
    refine ⟨⟨hw0⟩, ⟨PullbackCone.IsLimit.mk _ (fun s ↦ pullback.lift s.fst s.snd ?_) ?_ ?_ ?_⟩⟩
    · rw [← cancel_mono (yoneda.map ι), Category.assoc, Category.assoc, hφ', hψy]
      exact s.condition
    · intro s; exact pullback.lift_fst _ _ _
    · intro s; exact pullback.lift_snd _ _ _
    · intro s m h1 h2
      exact pullback.hom_ext (h1.trans (pullback.lift_fst _ _ _).symm)
        (h2.trans (pullback.lift_snd _ _ _).symm)
  obtain ⟨Z₀, hZ₀, ⟨e⟩⟩ := hV
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj Z₀) := hZ₀
  let e' : pullback φ' (yoneda.map ψ') ≅ yoneda.obj Z₀ := hpb.isoPullback ≪≫ e
  have haff : IsAffineHom B S hS (pullback.snd φ' (yoneda.map ψ')) := by
    have h : pullback.snd φ' (yoneda.map ψ') =
        e'.hom ≫ yoneda.map (yoneda.preimage (e'.inv ≫ pullback.snd φ' (yoneda.map ψ'))) := by
      rw [Functor.map_preimage, Iso.hom_inv_id_assoc]
    rw [h]
    exact isAffineHom_iso_comp e'.hom (isAffineHom_yoneda_map B S hS _)
  have hsurj : IsSurjective B S hS (yoneda.map ψ') :=
    isSurjective_yoneda_map B S hS ψ' (surjective_etaleImageLift B S hS ψ)
  have het : IsEtale B S hS (yoneda.map ψ') :=
    (isEtale_iff_presheaf_of_yoneda B S hS _).2
      ((presheaf_yoneda_map_etale_iff B S hS ψ').2 (etale_etaleImageLift B S hS ψ))
  have htfae := isAffineHom_tfae_of_isAlgebraicSpace B S hS φ' hX
    (isAlgebraicSpace_yoneda B S hS _)
  have h4 : ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ yoneda.obj (etaleOpenImage B S hS ψ)),
      IsSurjective B S hS g ∧ IsEtale B S hS g ∧ IsAffineHom B S hS (pullback.snd φ' g) :=
    ⟨Y', yoneda.map ψ', hsurj, het, haff⟩
  obtain ⟨hrep, -⟩ := (htfae.out 4 1).mp h4
  obtain ⟨a, snd, fst, hsq⟩ := hrep (𝟙 (yoneda.obj (etaleOpenImage B S hS ψ)))
  have : IsIso fst := hsq.isIso_fst_of_isIso
  exact ⟨a, ⟨(asIso fst).symm⟩⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- **A represented algebraic space over an affine base whose base change to a thickening of
the base is affine is affine.**  This is Stacks 06AD for the representing scheme. -/
theorem isAffineSpace_of_iso_yoneda_of_isThickening {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Z T₀ T : BigFppfOver B S hS} (e : X ≅ yoneda.obj Z) (ρ : X ⟶ yoneda.obj T) (k : T₀ ⟶ T)
    (hk : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k))
    (h₀ : IsAffineSpace B S hS (pullback ρ (yoneda.map k))) :
    IsAffineSpace B S hS X := by
  set r : Z ⟶ T := yoneda.preimage (e.inv ≫ ρ)
  have hr : yoneda.map r = e.inv ≫ ρ := Functor.map_preimage _ _
  have hsite := IsPullback.of_hasPullback r k
  have hyon : IsPullback (yoneda.map (pullback.fst r k) ≫ e.inv) (yoneda.map (pullback.snd r k))
      ρ (yoneda.map k) := by
    have h := hsite.map yoneda
    rw [hr] at h
    exact IsPullback.of_iso h (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simp) (by simp)
  obtain ⟨O, hO, ⟨eO⟩⟩ := h₀
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj O) := hO
  let eP : yoneda.obj (pullback r k) ≅ yoneda.obj O := hyon.isoPullback ≪≫ eO
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (pullback r k)) :=
    .of_isIso ((BigFppfOver.toScheme B S hS).mapIso (Yoneda.fullyFaithful.preimageIso eP)).hom
  have hpres : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) := by
    dsimp [BigFppfOver.toScheme]
    infer_instance
  have hsch := hsite.map (BigFppfOver.toScheme B S hS)
  have hthick : Stacks.Thickenings.IsThickening
      ((BigFppfOver.toScheme B S hS).map (pullback.fst r k)) := by
    have hci : _root_.AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme B S hS).map k) := hk.1
    have hsu : Surjective ((BigFppfOver.toScheme B S hS).map k) := ⟨hk.2⟩
    refine ⟨MorphismProperty.of_isPullback hsch.flip hci, ?_⟩
    exact (MorphismProperty.of_isPullback (P := @Surjective) hsch.flip hsu).surj
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj Z) :=
    Stacks.Thickenings.isAffine_of_isThickening hthick
  exact ⟨Z, this, ⟨e⟩⟩

end AlgebraicGeometry.Space

end
