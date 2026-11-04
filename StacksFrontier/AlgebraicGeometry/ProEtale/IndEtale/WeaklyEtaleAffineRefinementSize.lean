module

public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtale.WeaklyEtaleAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff

/-!
# Size bounds for the weakly étale affine refinement

The weakly étale morphisms `U' ⟶ U` of
`StacksFrontier.AlgebraicGeometry.ProEtale.IndEtale.WeaklyEtaleAffineRefinement` can be chosen with
`U'` no larger than `U`: on the spectrum of a ring `R` the scheme `U'` is the spectrum of the
ind-Zariski algebra of `AlgebraicGeometry.ProEtale.exists_indZariski_range_comap_eq_and_mk_le`,
which has at most `max ℵ₀ #R` elements. This keeps `U'` inside any chosen category of schemes
which contains `U` and is closed under the size bound of a scheme.

## Main results

* `AlgebraicGeometry.ProEtale.exists_weaklyEtale_specRange_eq_and_size_le`: on `Spec R`, a
  quasi-compact subset stable under generalization is the image of a weakly étale morphism from
  an affine scheme of size at most `max ℵ₀ #R`.
* `AlgebraicGeometry.ProEtale.exists_weaklyEtale_affine_range_eq_and_size_le`: the same on an
  affine scheme `U`, with the size bounded by that of `U`.
* `AlgebraicGeometry.ProEtale.exists_weaklyEtale_affine_surjective_pullback_and_size_le`: the
  refinement of `AlgebraicGeometry.ProEtale.exists_weaklyEtale_affine_surjective_pullback` with
  `U'` no larger than `U`.

## References

* [Stacks Project, Tag 0A31](https://stacks.math.columbia.edu/tag/0A31)
* [Stacks Project, Tag 0951](https://stacks.math.columbia.edu/tag/0951)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProEtale

/-- On the spectrum of a ring, a quasi-compact subset stable under generalization is the image of
a weakly étale morphism from an affine scheme of size at most `max ℵ₀ #R`. -/
theorem exists_weaklyEtale_specRange_eq_and_size_le (R : CommRingCat.{u}) (E : Set (Spec R))
    (hcomp : IsCompact E) (hgen : StableUnderGeneralization E) :
    ∃ (U' : Scheme.{u}) (_ : IsAffine U') (h : U' ⟶ Spec R),
      WeaklyEtale h ∧ Set.range h = E ∧ U'.size ≤ max Cardinal.aleph0 (Cardinal.mk R) := by
  have hE : SpectralSubset.IsStableCompact (show Set (PrimeSpectrum R) from E) :=
    ⟨hcomp, hgen⟩
  obtain ⟨B, _, _, hiz, hrange, hcard⟩ := exists_indZariski_range_comap_eq_and_mk_le _ hE
  refine ⟨Spec (CommRingCat.of B), inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap R B)), ?_, hrange, ?_⟩
  · have hwe : Algebra.WeaklyEtale R B := Algebra.WeaklyEtale.of_isIndZariski hiz
    have heq : (CommRingCat.ofHom (algebraMap R B)).hom.toAlgebra =
        (inferInstance : Algebra R B) := Algebra.algebra_ext _ _ fun _ ↦ rfl
    rw [weaklyEtale_specMap_iff]
    exact heq ▸ hwe
  · rw [Scheme.size_Spec]
    exact max_le (le_max_left _ _) hcard

/-- On an affine scheme, a quasi-compact subset stable under generalization is the image of a
weakly étale morphism from an affine scheme of size at most that of `U`. -/
theorem exists_weaklyEtale_affine_range_eq_and_size_le (U : Scheme.{u}) [IsAffine U]
    (E : Set U) (hcomp : IsCompact E) (hgen : StableUnderGeneralization E) :
    ∃ (U' : Scheme.{u}) (_ : IsAffine U') (h : U' ⟶ U),
      WeaklyEtale h ∧ Set.range h = E ∧ U'.size ≤ U.size := by
  obtain ⟨U', _, g, hg, hgrange, hsize⟩ := exists_weaklyEtale_specRange_eq_and_size_le Γ(U, ⊤)
    (U.isoSpec.hom '' E) (hcomp.image U.isoSpec.hom.continuous)
    (GeneralizingMap.stableUnderGeneralization_image
      U.isoSpec.hom.isOpenEmbedding.generalizingMap hgen)
  have : WeaklyEtale g := hg
  refine ⟨U', inferInstance, g ≫ U.isoSpec.inv, inferInstance, ?_,
    hsize.trans (max_le (Scheme.aleph0_le_size U)
      (Scheme.mk_sections_le_size U ⟨⊤, isAffineOpen_top U⟩))⟩
  have hfun : (⇑(g ≫ U.isoSpec.inv) : U' → U) = ⇑U.isoSpec.inv ∘ ⇑g :=
    funext fun x ↦ Scheme.Hom.comp_apply g U.isoSpec.inv x
  rw [hfun, Set.range_comp, hgrange, ← Set.image_comp]
  refine (Set.image_congr fun x _ ↦ ?_).trans (Set.image_id E)
  exact (Scheme.Hom.comp_apply U.isoSpec.hom U.isoSpec.inv x).symm.trans
    (congrFun (congrArg (fun k : U ⟶ U ↦ (⇑k : U → U)) U.isoSpec.hom_inv_id) x)

/-- **The refinement, with a size bound.** Let `T` be affine, let `a : U ⟶ T` be weakly étale
with `U` affine, let `b : W ⟶ T` be flat with `W` affine, and let `φ : W ⟶ U` be a morphism over
`T`. Then there is an affine `U'`, no larger than `U`, and a morphism `h : U' ⟶ U` over `T` with
`U' ⟶ T` weakly étale, such that `W' = W ×_U U'` is affine, `W' ⟶ W` is surjective and weakly
étale, and `W' ⟶ U'` is surjective. -/
theorem exists_weaklyEtale_affine_surjective_pullback_and_size_le {T U W : Scheme.{u}}
    [IsAffine T] [IsAffine U] [IsAffine W] (a : U ⟶ T) (b : W ⟶ T) (φ : W ⟶ U) [WeaklyEtale a]
    [Flat b] (hφ : φ ≫ a = b) :
    ∃ (U' : Scheme.{u}) (_ : IsAffine U') (h : U' ⟶ U),
      WeaklyEtale (h ≫ a) ∧ IsAffine (pullback φ h) ∧
        WeaklyEtale (pullback.fst φ h) ∧ Surjective (pullback.fst φ h) ∧
          Surjective (pullback.snd φ h) ∧ U'.size ≤ U.size := by
  have := flat_hasOfPostcompProperty_weaklyEtale.{u}
  have hcomp : Flat (φ ≫ a) := by rw [hφ]; infer_instance
  have hflat : Flat φ :=
    MorphismProperty.of_postcomp (W' := @WeaklyEtale) _ φ a inferInstance hcomp
  obtain ⟨U', _, h, hwe, hrange, hsize⟩ :=
    exists_weaklyEtale_affine_range_eq_and_size_le U (Set.range φ)
      (isCompact_range φ.continuous) (Flat.generalizingMap φ).stableUnderGeneralization_range
  have : WeaklyEtale h := hwe
  refine ⟨U', inferInstance, h, inferInstance, inferInstance, inferInstance, ?_, ?_, hsize⟩
  · rw [surjective_iff, ← Set.range_eq_univ, Scheme.Pullback.range_fst, hrange]
    exact Set.eq_univ_of_forall fun x ↦ ⟨x, rfl⟩
  · rw [surjective_iff, ← Set.range_eq_univ, Scheme.Pullback.range_snd]
    refine Set.eq_univ_of_forall fun x ↦ ?_
    rw [Set.mem_preimage, ← hrange]
    exact ⟨x, rfl⟩

end AlgebraicGeometry.ProEtale

end
