module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Characterization
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.StableCompactRange
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.WeaklyEtale

/-!
# Refining a flat map to an affine weakly étale scheme by a weakly étale affine base change

Let `T` be affine, let `U ⟶ T` be weakly étale with `U` affine, let `W ⟶ T` be flat with `W`
affine, and let `φ : W ⟶ U` be a morphism over `T`. This file produces an affine `U'` with a
weakly étale `U' ⟶ T` and a morphism `U' ⟶ U` over `T` whose base change `W ×_U U' ⟶ W` is
surjective and weakly étale, and whose other projection `W ×_U U' ⟶ U'` is surjective as well.

## Main results

* `AlgebraicGeometry.ProEtale.exists_weaklyEtale_affine_range_eq`: on an affine scheme, a
  quasi-compact subset stable under generalization is the image of a weakly étale morphism from
  an affine scheme.
* `AlgebraicGeometry.ProEtale.exists_weaklyEtale_affine_surjective_pullback`: the refinement
  described above.

## Implementation notes

The morphism `φ` is flat: it is flat after postcomposition with the weakly étale `U ⟶ T`, and
flatness has the of-postcomp property with respect to weak étaleness, since the diagonal of a
weakly étale morphism is flat. Hence the image `E` of `φ` is stable under generalization, and it
is quasi-compact because `W` is. So `E` is realized as the image of a weakly étale morphism
`h : U' ⟶ U` with `U'` affine, which is what the refinement is built from: the projections of
`W ×_U U'` have images `φ ⁻¹' E = W` and `h ⁻¹' E = U'`, so both are surjective.

The realization of `E` is the ind-Zariski algebra of
`AlgebraicGeometry.ProEtale.exists_indZariski_range_comap_eq`; an ind-Zariski algebra is weakly
étale, and for affine schemes weak étaleness of the morphism is weak étaleness of the ring map.
Only the spectrum of a ring is treated there, so a general affine `U` is moved to
`Spec Γ(U, ⊤)` along `Scheme.isoSpec`, which changes neither quasi-compactness nor stability
under generalization of the image of `φ`, since an isomorphism is an open embedding.

## References

* [Stacks Project, Tag 0A31](https://stacks.math.columbia.edu/tag/0A31)
* [Stacks Project, Tag 0951](https://stacks.math.columbia.edu/tag/0951)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProEtale

/-- Flatness can be cancelled by a weakly étale postcomposition: the diagonal of a weakly étale
morphism is flat. -/
theorem flat_hasOfPostcompProperty_weaklyEtale :
    MorphismProperty.HasOfPostcompProperty (@Flat : MorphismProperty Scheme.{u}) @WeaklyEtale :=
  MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ hf ↦ WeaklyEtale.flat_diagonal (f := _) (self := hf)

/-- The image of a composite of morphisms of schemes is the image of the image. -/
private theorem range_comp_base {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Set.range (f ≫ g) = g '' Set.range f := by
  have hfun : (⇑(f ≫ g) : X → Z) = ⇑g ∘ ⇑f := funext fun x ↦ Scheme.Hom.comp_apply f g x
  rw [hfun, Set.range_comp]

/-- On the spectrum of a ring, a quasi-compact subset stable under generalization is the image of
a weakly étale morphism from an affine scheme. -/
theorem exists_weaklyEtale_specRange_eq (R : CommRingCat.{u}) (E : Set (Spec R))
    (hcomp : IsCompact E) (hgen : StableUnderGeneralization E) :
    ∃ (U' : Scheme.{u}) (_ : IsAffine U') (h : U' ⟶ Spec R),
      WeaklyEtale h ∧ Set.range h = E := by
  have hE : SpectralSubset.IsStableCompact (show Set (PrimeSpectrum R) from E) :=
    ⟨hcomp, hgen⟩
  obtain ⟨B, _, _, hiz, hrange⟩ := exists_indZariski_range_comap_eq _ hE
  refine ⟨Spec (CommRingCat.of B), inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap R B)), ?_, hrange⟩
  have hwe : Algebra.WeaklyEtale R B := Algebra.WeaklyEtale.of_isIndZariski hiz
  have heq : (CommRingCat.ofHom (algebraMap R B)).hom.toAlgebra =
      (inferInstance : Algebra R B) := Algebra.algebra_ext _ _ fun _ ↦ rfl
  rw [weaklyEtale_specMap_iff]
  exact heq ▸ hwe

/-- On an affine scheme, a quasi-compact subset stable under generalization is the image of a
weakly étale morphism from an affine scheme. -/
theorem exists_weaklyEtale_affine_range_eq (U : Scheme.{u}) [IsAffine U] (E : Set U)
    (hcomp : IsCompact E) (hgen : StableUnderGeneralization E) :
    ∃ (U' : Scheme.{u}) (_ : IsAffine U') (h : U' ⟶ U),
      WeaklyEtale h ∧ Set.range h = E := by
  obtain ⟨U', _, g, hg, hgrange⟩ := exists_weaklyEtale_specRange_eq Γ(U, ⊤)
    (U.isoSpec.hom '' E) (hcomp.image U.isoSpec.hom.continuous)
    (GeneralizingMap.stableUnderGeneralization_image
      U.isoSpec.hom.isOpenEmbedding.generalizingMap hgen)
  have : WeaklyEtale g := hg
  refine ⟨U', inferInstance, g ≫ U.isoSpec.inv, inferInstance, ?_⟩
  rw [range_comp_base, hgrange, ← Set.image_comp]
  refine (Set.image_congr fun x _ ↦ ?_).trans (Set.image_id E)
  exact (Scheme.Hom.comp_apply U.isoSpec.hom U.isoSpec.inv x).symm.trans
    (congrFun (congrArg (fun k : U ⟶ U ↦ (⇑k : U → U)) U.isoSpec.hom_inv_id) x)

/-- **The refinement.** Let `T` be affine, let `a : U ⟶ T` be weakly étale with `U` affine, let
`b : W ⟶ T` be flat with `W` affine, and let `φ : W ⟶ U` be a morphism over `T`. Then there is an
affine `U'` and a morphism `h : U' ⟶ U` over `T` with `U' ⟶ T` weakly étale, such that
`W' = W ×_U U'` is affine, `W' ⟶ W` is surjective and weakly étale, and `W' ⟶ U'` is
surjective. -/
theorem exists_weaklyEtale_affine_surjective_pullback {T U W : Scheme.{u}} [IsAffine T]
    [IsAffine U] [IsAffine W] (a : U ⟶ T) (b : W ⟶ T) (φ : W ⟶ U) [WeaklyEtale a] [Flat b]
    (hφ : φ ≫ a = b) :
    ∃ (U' : Scheme.{u}) (_ : IsAffine U') (h : U' ⟶ U),
      WeaklyEtale (h ≫ a) ∧ IsAffine (pullback φ h) ∧
        WeaklyEtale (pullback.fst φ h) ∧ Surjective (pullback.fst φ h) ∧
          Surjective (pullback.snd φ h) := by
  have := flat_hasOfPostcompProperty_weaklyEtale.{u}
  have hcomp : Flat (φ ≫ a) := by rw [hφ]; infer_instance
  have hflat : Flat φ :=
    MorphismProperty.of_postcomp (W' := @WeaklyEtale) _ φ a inferInstance hcomp
  obtain ⟨U', _, h, hwe, hrange⟩ := exists_weaklyEtale_affine_range_eq U (Set.range φ)
    (isCompact_range φ.continuous) (Flat.generalizingMap φ).stableUnderGeneralization_range
  have : WeaklyEtale h := hwe
  refine ⟨U', inferInstance, h, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · rw [surjective_iff, ← Set.range_eq_univ, Scheme.Pullback.range_fst, hrange]
    exact Set.eq_univ_of_forall fun x ↦ ⟨x, rfl⟩
  · rw [surjective_iff, ← Set.range_eq_univ, Scheme.Pullback.range_snd]
    refine Set.eq_univ_of_forall fun x ↦ ?_
    rw [Set.mem_preimage, ← hrange]
    exact ⟨x, rfl⟩

end AlgebraicGeometry.ProEtale

end
