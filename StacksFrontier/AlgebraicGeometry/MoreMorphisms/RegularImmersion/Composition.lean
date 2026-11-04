module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.RegularOpenIndependence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The composite of two regular immersions is a regular immersion

The composite of two regular immersions of schemes is a regular immersion. This is part (1) of
Stacks tag 067Q.

## Main results

* `Stacks.AlgebraicGeometry.ker_ideal_of_open_pullback`: the kernel ideal of the restriction of a
  closed immersion to an open of its target, over an affine open, is the extension of the kernel
  ideal of the closed immersion.
* `Stacks.AlgebraicGeometry.isRegularIdealSheaf_of_isPullback_of_isOpenImmersion`: regularity of
  the defining ideal of a closed immersion is inherited by its restriction to an open subscheme
  of the target.
* `Stacks.AlgebraicGeometry.exists_open_isPullback_liftCoborder`: an immersion restricts to a
  closed immersion over a suitable open of its target.
* `Stacks.AlgebraicGeometry.isRegularImmersion_comp`: the composite of two regular immersions is a
  regular immersion.

## References

* [Stacks Project, Lemma 31.21.5 (Tag 067Q)](https://stacks.math.columbia.edu/tag/067Q)
* [Stacks Project, Definition 31.21.1 (Tag 063J)](https://stacks.math.columbia.edu/tag/063J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry RingTheory.Sequence
open Stacks.AlgebraicGeometry.QuasiRegular
open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace Stacks.AlgebraicGeometry

universe u

section Restriction

/-- Contracting along the inverse of a ring isomorphism is extending along the isomorphism. -/
private theorem comap_iso_inv {R S : CommRingCat.{u}} (e : R ≅ S) (I : Ideal R) :
    I.comap e.inv.hom = I.map e.hom.hom := by
  let e' := e.commRingCatIsoToRingEquiv
  show I.comap (e'.symm : S →+* R) = I.map (e' : R →+* S)
  rw [Ideal.comap_coe, Ideal.comap_symm, Ideal.map_coe]

/-- Extending the ideal spanned by a finite family is the ideal spanned by its images. -/
private theorem map_span_range {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) {r : ℕ}
    (f : Fin r → A) :
    (Ideal.span (Set.range f)).map φ = Ideal.span (Set.range fun i => φ (f i)) := by
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

/-- If `i' : Z' ⟶ X'` is the base change of a closed immersion `i : Z ⟶ X` along an open immersion
`b : X' ⟶ X`, then over an affine open `V` of `X'` inside `b ⁻¹ᵁ U` the kernel ideal of `i'` is
the extension of the kernel ideal of `i` over `U` along `b.appLE U V`. -/
theorem ker_ideal_of_open_pullback {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    (a : Z' ⟶ Z) (b : X' ⟶ X) [IsClosedImmersion i] [IsOpenImmersion b]
    (H : IsPullback i' a b i) (U : X.affineOpens) (V : X'.affineOpens)
    (hVU : V.1 ≤ b ⁻¹ᵁ U.1) :
    i'.ker.ideal V = (i.ker.ideal U).map (b.appLE U.1 V.1 hVU).hom := by
  rw [Scheme.ker_ideal_of_isPullback_of_isOpenImmersion i i' a b H V, comap_iso_inv]
  have hWU : b ''ᵁ V.1 ≤ U.1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact hVU hx
  rw [← i.ker.map_ideal (U := ⟨b ''ᵁ V.1, V.2.image_of_isOpenImmersion b⟩) (V := U) hWU,
    Ideal.map_map]
  congr 1
  refine CommRingCat.hom_ext_iff.mp ?_
  show X.presheaf.map (homOfLE hWU).op ≫ (b.appIso V.1).hom = b.appLE U.1 V.1 hVU
  refine (cancel_mono (b.appIso V.1).inv).mp ?_
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Scheme.Hom.appLE_appIso_inv]

/-- If `i' : Z' ⟶ X'` is the base change of a closed immersion `i : Z ⟶ X` along an open
immersion `b : X' ⟶ X` and the defining ideal of `i` is regular, then so is the defining ideal of
`i'`. -/
theorem isRegularIdealSheaf_of_isPullback_of_isOpenImmersion {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X)
    (i' : Z' ⟶ X') (a : Z' ⟶ Z) (b : X' ⟶ X) [IsClosedImmersion i] [IsClosedImmersion i']
    [IsOpenImmersion b] (H : IsPullback i' a b i)
    (hi : IsRegularIdealSheaf X.toRingedSpace (definingIdealOfHom i)) :
    IsRegularIdealSheaf X'.toRingedSpace (definingIdealOfHom i') := by
  refine (isRegularIdealSheaf_iff_exists_affine_generators X' _).mpr fun x hx => ?_
  rw [definingIdealQuotient_support_eq_range i'] at hx
  obtain ⟨z, rfl⟩ := hx
  have hz : b (i' z) = i (a z) := congrArg (fun k : Z' ⟶ X => k z) H.w
  have hmem : b (i' z) ∈ idealQuotientSupport X.toRingedSpace (definingIdealOfHom i) := by
    rw [definingIdealQuotient_support_eq_range i]
    exact ⟨a z, hz.symm⟩
  obtain ⟨U, hzU, r, f, hfgen, hf⟩ :=
    (isRegularIdealSheaf_iff_exists_affine_generators X _).mp hi (b (i' z)) hmem
  obtain ⟨V, hV, hzV, hVU⟩ :=
    exists_isAffineOpen_mem_and_subset (show i' z ∈ b ⁻¹ᵁ U.1 from hzU)
  refine ⟨⟨V, hV⟩, hzV, r, (fun k => b.appLE U.1 V hVU (f k)), ?_, ?_⟩
  · refine isGeneratedByOn_definingIdealOfHom_of_ker_app_eq_span i' hV _ ?_
    rw [← Scheme.Hom.ker_apply i' ⟨V, hV⟩,
      ker_ideal_of_open_pullback i i' a b H U ⟨V, hV⟩ hVU, Scheme.Hom.ker_apply i U,
      ker_app_eq_span_range i U.2 f hfgen, map_span_range]
  · exact isWeaklyRegular_ofFn_map_of_flat (b.appLE U.1 V hVU).hom
      (b.flat_appLE U.2 hV hVU) f hf

end Restriction

section Composition

/-- For an immersion `j : Y ⟶ X` and an open `V` of `Y`, there are an open `W` of `X`, an open
immersion `b : W ⟶ j.coborderRange` and a morphism `j' : V ⟶ W` with `j' ≫ W.ι = V.ι ≫ j` that
is the base change of the closed immersion `j.liftCoborder` along `b`. -/
theorem exists_open_isPullback_liftCoborder {Y X : Scheme.{u}} (j : Y ⟶ X) [IsImmersion j]
    (V : Y.Opens) :
    ∃ (W : X.Opens) (b : W.toScheme ⟶ j.coborderRange.toScheme)
      (j' : V.toScheme ⟶ W.toScheme) (_ : IsOpenImmersion b),
      IsPullback j' V.ι b j.liftCoborder ∧ j' ≫ W.ι = V.ι ≫ j := by
  let U := j.coborderRange
  let j₀ := j.liftCoborder
  have hclosed : IsClosed (j₀ '' (Vᶜ : Set Y)) :=
    (IsClosedImmersion.isClosedEmbedding j₀).isClosedMap _ (isClosed_compl_iff.mpr V.isOpen)
  let W : U.toScheme.Opens := ⟨(j₀ '' (Vᶜ : Set Y))ᶜ, hclosed.isOpen_compl⟩
  have hpre : j₀ ⁻¹ᵁ W = V := by
    ext y
    exact ⟨fun hy => Classical.byContradiction fun hyV => hy (Set.mem_image_of_mem j₀ hyV),
      fun hy ⟨_, hy', heq⟩ => hy' ((IsClosedImmersion.isClosedEmbedding j₀).injective heq ▸ hy)⟩
  let W' : X.Opens := U.ι ''ᵁ W
  have hWU : W' ≤ U := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  let b : W'.toScheme ⟶ U.toScheme := X.homOfLE hWU
  have hb : b.opensRange = W := by
    rw [Scheme.opensRange_homOfLE]
    exact U.ι.preimage_image_eq W
  have hrange : Set.range (V.ι ≫ j) ⊆ Set.range W'.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    have hyW : j₀ y.val ∈ W := by
      show y.val ∈ j₀ ⁻¹ᵁ W
      rw [hpre]
      exact y.property
    exact ⟨j₀ y.val, hyW, congrArg (fun k : Y ⟶ X => k y.val) j.liftCoborder_ι⟩
  let j' : V.toScheme ⟶ W'.toScheme := IsOpenImmersion.lift W'.ι (V.ι ≫ j) hrange
  have hj' : j' ≫ W'.ι = V.ι ≫ j := IsOpenImmersion.lift_fac _ _ _
  have hcomm : V.ι ≫ j₀ = j' ≫ b := by
    refine (cancel_mono U.ι).mp ?_
    show (V.ι ≫ j.liftCoborder) ≫ U.ι = (j' ≫ X.homOfLE hWU) ≫ U.ι
    rw [Category.assoc, j.liftCoborder_ι, Category.assoc, X.homOfLE_ι hWU, hj']
  have H : IsPullback j' V.ι b j₀ := by
    refine IsOpenImmersion.isPullback j' V.ι b j₀ hcomm ?_
    rw [hb, hpre, Scheme.Opens.opensRange_ι]
  exact ⟨W', b, j', inferInstance, H, hj'⟩

/-- The composite of two regular immersions of schemes is a regular immersion. -/
@[stacks 067Q "composition_regular", ega "IV 19.1.5", sga "6 VIII 1.1" "special case"]
theorem isRegularImmersion_comp {Z Y X : Scheme.{u}} (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i]
    [IsImmersion j] (hi : IsRegularImmersion i) (hj : IsRegularImmersion j) :
    IsRegularImmersion (i ≫ j) := by
  obtain ⟨W, b, j', _, H, hj'⟩ := exists_open_isPullback_liftCoborder j i.coborderRange
  have : IsClosedImmersion j' := MorphismProperty.of_isPullback H.flip inferInstance
  have hjreg : IsRegularIdealSheaf W.toScheme.toRingedSpace (definingIdealOfHom j') :=
    isRegularIdealSheaf_of_isPullback_of_isOpenImmersion j.liftCoborder j' i.coborderRange.ι b
      H hj
  have hcomp := isRegularIdealSheaf_comp_of_isClosedImmersion i.liftCoborder j' hi hjreg
  refine (isRegularImmersion_iff_of_open (i ≫ j) W (i.liftCoborder ≫ j') ?_).mpr hcomp
  rw [Category.assoc, hj', ← Category.assoc, i.liftCoborder_ι]

end Composition

end Stacks.AlgebraicGeometry

end
