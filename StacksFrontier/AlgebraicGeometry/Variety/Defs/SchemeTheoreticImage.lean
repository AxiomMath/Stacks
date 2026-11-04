module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import StacksCore.Tactic.StacksAttribute

/-!
# Scheme-theoretic images of products over a field

The scheme-theoretic image of the product of two quasi-compact morphisms of schemes over a field
is the product of their scheme-theoretic images.

## Main definitions

* `AlgebraicGeometry.productMap`: the morphism induced on fibre products by two morphisms over
  the same base.

## Main results

* `AlgebraicGeometry.toImage_isSchemeTheoreticallyDominant`: a quasi-compact morphism is
  scheme-theoretically dominant onto its scheme-theoretic image.
* `AlgebraicGeometry.existsUnique_imageProductMapIso`: for quasi-compact morphisms over a field,
  there is a unique isomorphism from the image of the product map to the product of the images
  whose composite with the product of the image inclusions is the image inclusion of the product
  map.

## References

* [Stacks Project, Tag 04Q1](https://stacks.math.columbia.edu/tag/04Q1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A quasi-compact morphism is scheme-theoretically dominant onto its scheme-theoretic image. -/
public theorem toImage_isSchemeTheoreticallyDominant {X Y : Scheme} (f : X ⟶ Y)
    [QuasiCompact f] : IsSchemeTheoreticallyDominant f.toImage := by
  rw [isSchemeTheoreticallyDominant_iff]
  let W : Y.affineOpens → f.image.affineOpens := fun U =>
    ⟨f.imageι ⁻¹ᵁ U.1, U.2.preimage f.imageι⟩
  have hW : ⨆ U, (W U).1 = ⊤ :=
    f.imageι.iSup_preimage_eq_top (iSup_affineOpens_eq_top Y)
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top W hW fun U => ?_
  simp only [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
  apply (RingHom.injective_iff_ker_eq_bot (f.toImage.app (W U)).hom).mp
  simpa [W] using f.toImage_app_injective U

/-- Base change of a scheme-theoretically dominant quasi-compact morphism in the left factor
along a flat morphism stays dominant. -/
private theorem isSchemeTheoreticallyDominant_pullback_map_left {X X' Y S : Scheme}
    (f : X ⟶ S) (f' : X' ⟶ S) (g : Y ⟶ S) (i : X ⟶ X') (hi : i ≫ f' = f)
    [IsSchemeTheoreticallyDominant i] [QuasiCompact i] [Flat g] :
    IsSchemeTheoreticallyDominant
      (pullback.map f g f' g i (𝟙 _) (𝟙 _) (by simp [hi]) (by simp)) := by
  subst hi
  have h₁ : pullback.map (i ≫ f') g f' g i (𝟙 _) (𝟙 _) (by simp) (by simp) ≫
      pullback.fst f' g = pullback.fst _ _ ≫ i := pullback.lift_fst _ _ _
  have h₂ : pullback.map (i ≫ f') g f' g i (𝟙 _) (𝟙 _) (by simp) (by simp) ≫
      pullback.snd f' g = pullback.snd _ _ := by
    rw [pullback.map, pullback.lift_snd, Category.comp_id]
  have : IsPullback (pullback.map (i ≫ f') g f' g i (𝟙 _) (𝟙 _) (by simp) (by simp))
      (pullback.fst _ _) (pullback.fst f' g) i :=
    .of_right (by rw [h₂]; exact (IsPullback.of_hasPullback ..).flip) h₁
      (.flip <| .of_hasPullback ..)
  exact IsSchemeTheoreticallyDominant.of_isPullback this.flip

/-- Base change of a scheme-theoretically dominant quasi-compact morphism in the right factor
along a flat morphism stays dominant. -/
private theorem isSchemeTheoreticallyDominant_pullback_map_right {X Y Y' S : Scheme}
    (f : X ⟶ S) (g : Y ⟶ S) (g' : Y' ⟶ S) (i : Y ⟶ Y') (hi : i ≫ g' = g)
    [IsSchemeTheoreticallyDominant i] [QuasiCompact i] [Flat f] :
    IsSchemeTheoreticallyDominant
      (pullback.map f g f g' (𝟙 _) i (𝟙 _) (by simp) (by simp [hi])) := by
  subst hi
  have h₁ : pullback.map f (i ≫ g') f g' (𝟙 _) i (𝟙 _) (by simp) (by simp) ≫
      pullback.snd f g' = pullback.snd _ _ ≫ i := pullback.lift_snd _ _ _
  have h₂ : pullback.map f (i ≫ g') f g' (𝟙 _) i (𝟙 _) (by simp) (by simp) ≫
      pullback.fst f g' = pullback.fst _ _ := by
    rw [pullback.map, pullback.lift_fst, Category.comp_id]
  have : IsPullback (pullback.map f (i ≫ g') f g' (𝟙 _) i (𝟙 _) (by simp) (by simp))
      (pullback.snd _ _) (pullback.snd f g') i :=
    .of_right (by rw [h₂]; exact .of_hasPullback ..) h₁ (.of_hasPullback ..)
  exact IsSchemeTheoreticallyDominant.of_isPullback this.flip

/-- The morphism induced on fiber products by two morphisms over the same base. -/
public noncomputable abbrev productMap {S A B X Y : Scheme.{u}}
    (pX : X ⟶ S) (pY : Y ⟶ S) (f : A ⟶ X) (g : B ⟶ Y) :
    pullback (f ≫ pX) (g ≫ pY) ⟶ pullback pX pY :=
  pullback.map (f ≫ pX) (g ≫ pY) pX pY f g (𝟙 _) (by rfl) (by rfl)

/-- The image of the product of two quasi-compact maps over a field is canonically isomorphic,
over the product of their targets, to the product of their scheme-theoretic images. -/
@[stacks 04Q1]
public theorem existsUnique_imageProductMapIso
    {k : Type u} [Field k] {A B X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    (f : A ⟶ X) (g : B ⟶ Y) [QuasiCompact f] [QuasiCompact g] :
    ∃! e : (productMap pX pY f g).image ≅
        pullback (f.imageι ≫ pX) (g.imageι ≫ pY),
      e.hom ≫ productMap pX pY f.imageι g.imageι =
        (productMap pX pY f g).imageι := by
  let pZ : f.image ⟶ Spec (.of k) := f.imageι ≫ pX
  let pZ' : g.image ⟶ Spec (.of k) := g.imageι ≫ pY
  let P := pullback (f ≫ pX) (g ≫ pY)
  let T := pullback pZ pZ'
  let h : P ⟶ pullback pX pY := productMap pX pY f g
  let j : T ⟶ pullback pX pY := productMap pX pY f.imageι g.imageι
  let q : P ⟶ T := pullback.map (f ≫ pX) (g ≫ pY) pZ pZ'
    f.toImage g.toImage (𝟙 _) (by simp [pZ]) (by simp [pZ'])
  let M : Scheme := pullback pZ (g ≫ pY)
  let q₁ : P ⟶ M := pullback.map (f ≫ pX) (g ≫ pY) pZ (g ≫ pY)
    f.toImage (𝟙 _) (𝟙 _) (by simp [pZ]) (by simp)
  let q₂ : M ⟶ T := pullback.map pZ (g ≫ pY) pZ pZ'
    (𝟙 _) g.toImage (𝟙 _) (by simp) (by simp [pZ'])
  have hq : q = q₁ ≫ q₂ := by
    dsimp [q, q₁, q₂]
    rw [pullback.map_comp]
    rfl
  have hq₁ : IsSchemeTheoreticallyDominant q₁ := by
    have : IsSchemeTheoreticallyDominant f.toImage := toImage_isSchemeTheoreticallyDominant f
    exact isSchemeTheoreticallyDominant_pullback_map_left _ pZ (g ≫ pY) f.toImage (by simp [pZ])
  have hq₂ : IsSchemeTheoreticallyDominant q₂ := by
    have : IsSchemeTheoreticallyDominant g.toImage := toImage_isSchemeTheoreticallyDominant g
    exact isSchemeTheoreticallyDominant_pullback_map_right pZ _ pZ' g.toImage (by simp [pZ'])
  have hqDom : IsSchemeTheoreticallyDominant q := by
    rw [hq]
    infer_instance
  have : IsClosedImmersion j := by
    dsimp [j, productMap]
    have : MorphismProperty.IsStableUnderComposition
        (@IsClosedImmersion : MorphismProperty Scheme.{u}) := ⟨fun _ _ _ _ => inferInstance⟩
    exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
      (f := f.imageι ≫ pX) (g := g.imageι ≫ pY) (f' := pX) (g' := pY)
      (i₁ := f.imageι) (i₂ := g.imageι) inferInstance inferInstance rfl rfl
  have hfac : h = q ≫ j := by
    dsimp [h, q, j, productMap]
    rw [pullback.map_comp]
    simp
  have hjle : j.ker ≤ h.imageι.ker := by
    have himker : h.imageι.ker = h.ker := Scheme.IdealSheafData.ker_subschemeι h.ker
    rw [himker, hfac]
    exact Scheme.Hom.le_ker_comp q j
  let e : h.image ⟶ T := IsClosedImmersion.lift j h.imageι hjle
  have hefac : e ≫ j = h.imageι := IsClosedImmersion.lift_fac j h.imageι hjle
  have hqfac : q = h.toImage ≫ e := (cancel_mono j).1 <| by
    rw [Category.assoc, hefac, Scheme.Hom.toImage_imageι]
    exact hfac.symm
  have heker : e.ker = ⊥ := by
    refine le_bot_iff.mp ((Scheme.Hom.le_ker_comp h.toImage e).trans ?_)
    rw [← hqfac, Scheme.Hom.ker_eq_bot q]
  have : IsClosedImmersion (e ≫ j) := by
    rw [hefac]
    infer_instance
  have : IsClosedImmersion e := IsClosedImmersion.of_comp_isClosedImmersion e j
  have : IsIso e := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr heker
  exact ⟨asIso e, by simpa [h, j] using hefac,
    fun e' he' => Iso.ext ((cancel_mono j).1 (he'.trans hefac.symm))⟩

end AlgebraicGeometry

end
