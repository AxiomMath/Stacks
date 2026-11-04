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
Everything else in this file is a temporary port; see the section header below.

## Relation to mathlib

**The section `Ported from mathlib#42759` is temporary and is expected to be deleted.** It is
the `Limits` part of mathlib#42759 (mckoen, `feat(CategoryTheory/Subobject): extend image
subobject API`, merged 2026-09-25, after our pinned revision of 2026-09-01), ported with the
upstream names, statements and proofs:
`Subobject.exists f` computed as an image subobject, `X ⊔ Y` as the image of `X ⨿ Y ⟶ A`, the
pullback of a kernel subobject, and the image of a strong epi–mono composite. The only
deviation in statements is `supIsoImage_hom`, which upstream generates with `@[simps!]` and
which is stated by hand here so that its right-hand side does not unfold `supIsImage`; a few
terminal `simp only` calls of the upstream proofs are replaced by rewrites. Delete the section once
the pin includes that pull request; every name then resolves to the mathlib declaration.
-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C]

/-! ### Ported from mathlib#42759 -/

namespace Subobject

variable {X Y : C}

section Exists

variable [HasImages C]

lemma exists_eq_imageSubobject (f : X ⟶ Y) (X' : Subobject X) :
    («exists» f).obj X' = imageSubobject (X'.arrow ≫ f) := by
  apply eq_of_comm ((existsIsoImage f X').trans (imageSubobjectIso (X'.arrow ≫ f)).symm)
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, imageSubobject_arrow']
  exact Over.w ((Subobject.existsCompRepresentativeIso f).app X').hom.hom

lemma exists_mk_eq_imageSubobject {A : C} (g : A ⟶ X) [Mono g] (f : X ⟶ Y) :
    («exists» f).obj (mk g) = imageSubobject (g ≫ f) := by rfl

end Exists

section Sup

variable [HasImages C] [HasBinaryCoproducts C]

/-- If `C` has binary coproducts and `f g : Subobject A`, then `f ⨿ g ⟶ A` factors as
`f ⨿ g ⟶ f ⊔ g ⟶ A`. Ported from mathlib#42759; delete when the pin includes it. -/
@[implicit_reducible, simps]
noncomputable def supMonoFactorisation {A : C} (f g : Subobject A) :
    MonoFactorisation (coprod.desc f.arrow g.arrow) where
  I := underlying.obj (f ⊔ g)
  m := (f ⊔ g).arrow
  e := coprod.desc (f.ofLE (f ⊔ g) le_sup_left) (g.ofLE (f ⊔ g) le_sup_right)

/-- If `C` has binary coproducts, then `f ⊔ g` is an image of `f ⨿ g ⟶ A`.
Ported from mathlib#42759; delete when the pin includes it. -/
noncomputable def supIsImage {A : C} (f g : Subobject A) :
    IsImage (supMonoFactorisation f g) where
  lift F := by
    refine (f ⊔ g).ofLEMk F.m (sup_le ?_ ?_)
    · refine le_mk_of_comm (coprod.inl ≫ F.e) ?_
      · rw [Category.assoc, MonoFactorisation.fac, coprod.inl_desc]
    · refine le_mk_of_comm (coprod.inr ≫ F.e) ?_
      · rw [Category.assoc, MonoFactorisation.fac, coprod.inr_desc]
  lift_fac := by simp [supMonoFactorisation]

/-- If `C` has binary coproducts, then `f ⊔ g ≅ image (f ⨿ g ⟶ A)`.
Ported from mathlib#42759; delete when the pin includes it. -/
@[simps! inv]
noncomputable def supIsoImage {A : C} (f g : Subobject A) :
    underlying.obj (f ⊔ g) ≅ image (coprod.desc f.arrow g.arrow) :=
  IsImage.isoExt (supIsImage ..) <| Image.isImage _

@[simp]
lemma supIsoImage_hom {A : C} (f g : Subobject A) :
    (supIsoImage f g).hom = (supIsImage f g).lift (Image.monoFactorisation _) :=
  rfl

lemma sup_eq_imageSubobject {A : C} (X Y : Subobject A) :
    X ⊔ Y = imageSubobject (coprod.desc X.arrow Y.arrow) :=
  eq_mk_of_comm (image.ι (coprod.desc X.arrow Y.arrow)) (supIsoImage X Y) (ofLEMk_comp _)

end Sup

lemma pullback_kernelSubobject [HasZeroMorphisms C] (f : X ⟶ Y) [HasKernel f] {W : C}
    (h : W ⟶ X) [HasPullbacks C] [HasKernel (h ≫ f)] :
    (Subobject.pullback h).obj (kernelSubobject f) = kernelSubobject (h ≫ f) := by
  simpa only [kernelSubobject, comp_zero] using pullback_equalizer f 0 h

lemma mk_eq_imageSubobject_of_mono [HasStrongEpiMonoFactorisations C]
    {X Y : C} {f : X ⟶ Y} {I' : C} (e : X ⟶ I') (m : I' ⟶ Y)
    (comm : e ≫ m = f := by cat_disch) [StrongEpi e] [Mono m] :
    mk m = imageSubobject f :=
  mk_eq_mk_of_comm m (image.ι f) (image.isoStrongEpiMono e m comm)
    (image.isoStrongEpiMono_hom_comp_ι e m comm)

end Subobject

namespace Limits

theorem imageSubobject_comp_of_strongEpi [HasStrongEpiMonoFactorisations C] {X Y X' : C}
    (e : X' ⟶ X) (f : X ⟶ Y) [StrongEpi e] [Mono f] :
    imageSubobject (e ≫ f) = imageSubobject f :=
  (Subobject.mk_eq_imageSubobject_of_mono e f).symm.trans (imageSubobject_mono f).symm

end Limits

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
