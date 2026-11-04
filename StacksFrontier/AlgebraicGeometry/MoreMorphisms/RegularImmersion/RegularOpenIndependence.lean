module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.ClosedComposition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Regularity of an immersion does not depend on the chosen open

By definition `Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion i` refers to the
canonical open `i.coborderRange` and its closed factor `i.liftCoborder`. Regularity may instead be
tested on any open subscheme `U` of the target through which `i` factors as a closed immersion.

## Main results

* `Stacks.AlgebraicGeometry.closedFactor_comp_resLE_eq_liftCoborder`: the closed factor through
  such an open, composed with the inclusion into the coborder, is the canonical closed factor.
* `Stacks.AlgebraicGeometry.isRegularIdealSheaf_comp_open_iff`: regularity of the defining ideal
  of a closed immersion is the same on an open subscheme and on the ambient scheme.
* `Stacks.AlgebraicGeometry.isRegularImmersion_iff_of_open`: an immersion is regular if and only
  if the defining ideal of its closed factor through any such open is regular.

## References

* [Stacks Project, Definition 31.21.1 (Tag 063J)](https://stacks.math.columbia.edu/tag/063J)
* [Stacks Project, Lemma 31.20.3 (Tag 063G)](https://stacks.math.columbia.edu/tag/063G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry RingTheory.Sequence
open Stacks.AlgebraicGeometry.QuasiRegular
open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace Stacks.AlgebraicGeometry

universe u

section Factorization

/-- The closed factor through an arbitrary open in which the immersion is closed, followed by the
inclusion of that open into `i.coborderRange`, is the canonical closed factor. -/
theorem closedFactor_comp_resLE_eq_liftCoborder {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (U : X.Opens) (j : Z ⟶ U.toScheme) [IsClosedImmersion j] (hij : j ≫ U.ι = i) :
    j ≫ Scheme.Hom.resLE (𝟙 X) i.coborderRange U
      (RegularIdealSheaf.le_coborderRange_of_isClosedImmersion i U j hij) = i.liftCoborder := by
  apply (cancel_mono i.coborderRange.ι).1
  calc
    (j ≫ Scheme.Hom.resLE (𝟙 X) i.coborderRange U
      (RegularIdealSheaf.le_coborderRange_of_isClosedImmersion i U j hij)) ≫
        i.coborderRange.ι = j ≫ U.ι := by simp
    _ = i := hij
    _ = i.liftCoborder ≫ i.coborderRange.ι := i.liftCoborder_ι.symm

end Factorization

section Flat

/-- Weak regularity of a finite sequence is inherited by its image under a flat ring map. -/
theorem isWeaklyRegular_map_of_flat {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (hφ : φ.Flat) {l : List A} (h : IsWeaklyRegular A l) : IsWeaklyRegular B (l.map φ) := by
  let _ : Algebra A B := φ.toAlgebra
  let _ : Module.Flat A B := hφ
  exact h.of_flat

/-- Weak regularity of a finite family `List.ofFn s` is inherited by its image under a flat ring
map. -/
theorem isWeaklyRegular_ofFn_map_of_flat {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (hφ : φ.Flat) {r : ℕ} (s : Fin r → A) (h : IsWeaklyRegular A (List.ofFn s)) :
    IsWeaklyRegular B (List.ofFn fun i => φ (s i)) := by
  simpa only [List.map_ofFn, Function.comp_def] using isWeaklyRegular_map_of_flat φ hφ h

end Flat

section CompOpen

/-- A point in the image of a closed immersion lies in the support of its defining ideal. -/
private theorem apply_mem_idealQuotientSupport {Z W : Scheme.{u}} (g : Z ⟶ W)
    [IsClosedImmersion g] (z : Z) :
    g z ∈ idealQuotientSupport W.toRingedSpace (definingIdealOfHom g) := by
  rw [definingIdealQuotient_support_eq_range]
  exact ⟨z, rfl⟩

variable {Z X Y : Scheme.{u}} (j : Z ⟶ X) [IsClosedImmersion j] (f : X ⟶ Y) [IsOpenImmersion f]

/-- Let `j : Z ⟶ X` be a closed immersion, `f : X ⟶ Y` an open immersion and suppose `j ≫ f` is
again a closed immersion. Then the defining ideal of `j ≫ f` on `Y` is regular if and only if the
defining ideal of `j` on `X` is. -/
@[ega "IV 16.9.2" "independence of U"]
theorem isRegularIdealSheaf_comp_open_iff [IsClosedImmersion (j ≫ f)] :
    IsRegularIdealSheaf Y.toRingedSpace (definingIdealOfHom (j ≫ f)) ↔
      IsRegularIdealSheaf X.toRingedSpace (definingIdealOfHom j) := by
  rw [isRegularIdealSheaf_iff_exists_affine_generators,
    isRegularIdealSheaf_iff_exists_affine_generators]
  constructor
  · intro h x hx
    rw [definingIdealQuotient_support_eq_range] at hx
    obtain ⟨z, rfl⟩ := hx
    obtain ⟨U, hxU, r, s, hgen, hs⟩ := h (f (j z)) (apply_mem_idealQuotientSupport (j ≫ f) z)
    obtain ⟨V, hV, hxV, hVU⟩ :=
      exists_isAffineOpen_mem_and_subset (show j z ∈ f ⁻¹ᵁ U.1 from hxU)
    refine ⟨⟨V, hV⟩, hxV, r, (fun i ↦ f.appLE U.1 V hVU (s i)), ?_, ?_⟩
    · have hg := isGeneratedByOn_mono _ hVU _ (isGeneratedByOn_restriction f _ U.1 s hgen)
      rwa [definingIdealOfHom_comp_open] at hg
    · exact isWeaklyRegular_ofFn_map_of_flat (f.appLE U.1 V hVU).hom
        (f.flat_appLE U.2 hV hVU) s hs
  · intro h y hy
    rw [definingIdealQuotient_support_eq_range] at hy
    obtain ⟨z, rfl⟩ := hy
    obtain ⟨U, hxU, r, s, hgen, hs⟩ := h (j z) (apply_mem_idealQuotientSupport j z)
    refine ⟨⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩, ⟨j z, hxU, rfl⟩, r,
      (fun i ↦ (f.appIso U.1).inv (s i)), ?_, ?_⟩
    · exact (isGeneratedByOn_image_iff f _ U.1 s).2 (by rwa [definingIdealOfHom_comp_open])
    · exact isWeaklyRegular_ofFn_map_of_flat (f.appIso U.1).inv.hom
        (RingHom.Flat.of_bijective
          (f.appIso U.1).commRingCatIsoToRingEquiv.symm.bijective) s hs

end CompOpen

section ArbitraryOpen

/-- An immersion `i : Z ⟶ X` is regular if and only if, for one — equivalently any — open
subscheme `U` of `X` through which `i` factors as a closed immersion `j : Z ⟶ U`, the defining
ideal of `j` is a regular ideal sheaf on `U`. -/
@[stacks 063J "part (1): independence of the chosen open"]
theorem isRegularImmersion_iff_of_open {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (U : X.Opens) (j : Z ⟶ U.toScheme) [IsClosedImmersion j] (hij : j ≫ U.ι = i) :
    IsRegularImmersion i ↔
      IsRegularIdealSheaf U.toScheme.toLocallyRingedSpace.toRingedSpace
        (definingIdealOfHom j) := by
  let f : U.toScheme ⟶ i.coborderRange.toScheme :=
    Scheme.Hom.resLE (𝟙 X) i.coborderRange U
      (RegularIdealSheaf.le_coborderRange_of_isClosedImmersion i U j hij)
  have hfι : f ≫ i.coborderRange.ι = U.ι := by simp [f]
  have : IsOpenImmersion f := by
    have : IsOpenImmersion (f ≫ i.coborderRange.ι) := hfι ▸ inferInstance
    exact IsOpenImmersion.of_comp f i.coborderRange.ι
  have hf : j ≫ f = i.liftCoborder := closedFactor_comp_resLE_eq_liftCoborder i U j hij
  have : IsClosedImmersion (j ≫ f) := hf ▸ inferInstance
  show IsRegularIdealSheaf _ (definingIdealOfHom i.liftCoborder) ↔ _
  rw [← hf]
  exact isRegularIdealSheaf_comp_open_iff j f

end ArbitraryOpen

end Stacks.AlgebraicGeometry

end
