module

public import Mathlib.CategoryTheory.Balanced
public import Mathlib.CategoryTheory.Subobject.Limits
public import StacksCore.CategoryTheory.Subobject.Basic
public import StacksCore.CategoryTheory.Subobject.Lattice
import StacksCore.Tactic.StacksAttribute

/-! ## Images, kernels and `Subobject.exists`.

The section `Own lemmas` at the end computes `Subobject.exists f` and `Subobject.pullback f` on
`⊤`, on the image of `f` and on the kernel of `f`, characterises the identity
`(m ∘ e)(X') = Im(m ∘ e) ⊓ Z'` for a strong epi–mono composite (`exists_comp_eq_inf_iff`), and
records how `Subobject.exists` of an isomorphism interacts with images and intersections.
The image-subobject API it builds on (`Subobject.exists_eq_imageSubobject`,
`Subobject.sup_eq_imageSubobject`, `Subobject.pullback_kernelSubobject`,
`Limits.imageSubobject_comp_of_strongEpi`, ...) is mathlib#42759, which mathlib now contains;
the temporary port of it that used to live here has been removed.
-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C]

/-! ### Own lemmas -/

namespace Subobject

variable {X Y : C}

/-- `f(X)`, the image of the top subobject under `exists f`, is the image of `f`. -/
lemma exists_obj_top [HasImages C] (f : X ⟶ Y) : («exists» f).obj ⊤ = imageSubobject f := by
  rw [← mk_eq_top_of_isIso (𝟙 X), exists_mk_eq_imageSubobject, Category.id_comp]

/-- An isomorphism maps the top subobject to the top subobject. -/
lemma exists_obj_top_of_isIso [HasImages C] (φ : X ⟶ Y) [IsIso φ] : («exists» φ).obj ⊤ = ⊤ := by
  rw [exists_obj_top, imageSubobject_mono, mk_eq_top_of_isIso]

/-- `Im(x ≫ φ) = φ(Im x)`. -/
lemma imageSubobject_comp_eq_exists [HasImages C] [HasPullbacks C] {Z : C} (x : X ⟶ Y)
    (φ : Y ⟶ Z) : imageSubobject (x ≫ φ) = («exists» φ).obj (imageSubobject x) := by
  rw [← exists_obj_top, exists_comp, exists_obj_top]

/-- Mathlib's `imageSubobject_iso_comp`, with pullbacks in place of equalizers. -/
lemma imageSubobject_iso_comp' [HasImages C] [HasPullbacks C] {X' : C} (h : X' ⟶ X) [IsIso h]
    (f : X ⟶ Y) : imageSubobject (h ≫ f) = imageSubobject f := by
  rw [← exists_obj_top, exists_comp, exists_obj_top_of_isIso, exists_obj_top]

/-- `f⁻¹(f(X)) = X`. -/
lemma pullback_imageSubobject_eq_top [HasImages C] [HasPullbacks C] (f : X ⟶ Y) :
    (pullback f).obj (imageSubobject f) = ⊤ :=
  top_le_iff.1 (by rw [← exists_obj_top]; exact le_pullback_exists f ⊤)

/-- `f(Ker f) = 0`. -/
lemma exists_kernelSubobject [HasZeroMorphisms C] [HasZeroObject C] [HasImages C] (f : X ⟶ Y)
    [HasKernel f] : («exists» f).obj (kernelSubobject f) = ⊥ := by
  rw [exists_eq_imageSubobject, kernelSubobject_arrow_comp, imageSubobject_zero]

/-- `Ker f ⊆ f⁻¹(Y')` for every subobject `Y'` of the target. -/
lemma kernelSubobject_le_pullback [HasZeroMorphisms C] [HasZeroObject C] [HasImages C]
    [HasPullbacks C] (f : X ⟶ Y) [HasKernel f] (Y' : Subobject Y) :
    kernelSubobject f ≤ (pullback f).obj Y' :=
  (exists_le_iff_le_pullback f _ _).1 (by rw [exists_kernelSubobject]; exact bot_le)

/-- The preimage of `⊥` under `f` is the kernel of `f`. -/
lemma pullback_bot [HasZeroMorphisms C] [HasZeroObject C] [HasImages C] [HasPullbacks C]
    (f : X ⟶ Y) [HasKernel f] : (pullback f).obj ⊥ = kernelSubobject f :=
  le_antisymm (le_kernelSubobject f _ (by rw [← (isPullback f ⊥).w, bot_arrow, comp_zero]))
    (kernelSubobject_le_pullback f ⊥)

/-- In a balanced category, an epimorphism has image `⊤`. -/
lemma imageSubobject_eq_top_of_epi [HasImages C] [Balanced C] (f : X ⟶ Y) [Epi f] :
    imageSubobject f = ⊤ :=
  have : Epi (image.ι f) := epi_of_epi_fac (image.fac f)
  (isIso_iff_mk_eq_top _).1 (isIso_of_mono_of_epi _)

/-- A monomorphism has kernel `⊥`. -/
lemma kernelSubobject_eq_bot_of_mono [HasZeroMorphisms C] [HasZeroObject C] (f : X ⟶ Y)
    [HasKernel f] [Mono f] : kernelSubobject f = ⊥ :=
  mk_eq_bot_iff_zero.2 (kernel.ι_of_mono f)

/-- For a strong epimorphism `e : X ⟶ Y` and a monomorphism `m : Y ⟶ Z`, the identity
`(m ∘ e)(X') = Im(m ∘ e) ⊓ Z'` holds if and only if `e(X') = m⁻¹(Z')`: the image of `m ∘ e` is
`m`, and `m` is injective on subobjects. -/
lemma exists_comp_eq_inf_iff [HasPullbacks C] [HasStrongEpiMonoFactorisations C] {Z : C}
    (e : X ⟶ Y) (m : Y ⟶ Z) [StrongEpi e] [Mono m] (X' : Subobject X) (Z' : Subobject Z) :
    («exists» (e ≫ m)).obj X' = imageSubobject (e ≫ m) ⊓ Z' ↔
      («exists» e).obj X' = (pullback m).obj Z' := by
  rw [exists_comp, imageSubobject_comp_of_strongEpi, imageSubobject_mono, inf_comm,
    ← exists_pullback_eq_inf_of_mono, le_antisymm_iff, le_antisymm_iff,
    exists_le_exists_iff_of_mono, exists_le_exists_iff_of_mono]

/-- The image functor of an isomorphism preserves intersections. -/
lemma exists_obj_inf_of_isIso [HasImages C] [HasPullbacks C] (φ : X ⟶ Y) [IsIso φ]
    (P Q : Subobject X) :
    («exists» φ).obj (P ⊓ Q) = («exists» φ).obj P ⊓ («exists» φ).obj Q := by
  rw [exists_iso_map]
  exact (mapIsoToOrderIso (asIso φ)).map_inf P Q

/-- The image functor of a monomorphism is injective. -/
lemma exists_obj_eq_exists_obj_iff_of_mono [HasImages C] (f : X ⟶ Y) [Mono f]
    (P Q : Subobject X) : («exists» f).obj P = («exists» f).obj Q ↔ P = Q := by
  simp [le_antisymm_iff, exists_le_exists_iff_of_mono]

end Subobject

end CategoryTheory
