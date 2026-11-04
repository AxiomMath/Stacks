module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Exact
public import StacksCore.CategoryTheory.Subobject.Basic

/-! ## Subobjects of the middle term of a short exact sequence.

Let `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be a short exact sequence in an abelian category, and let `Z`
be a subobject of `X₂`. The composite `Z ⟶ X₂ ⟶ X₃` has cycles `ker (Z ⟶ X₃)` and opcycles
`coim (Z ⟶ X₃)`, and they sit in a short exact sequence
`0 ⟶ ker (Z ⟶ X₃) ⟶ Z ⟶ coim (Z ⟶ X₃) ⟶ 0`.

Since the map from the cycles to `X₂` is a monomorphism it factors through `X₁`, and since
the map from the opcycles to `X₃` is a monomorphism, these two ends are subobjects of `X₁`
and of `X₃`: they are the intersection `Z ∩ X₁` (`interX₁`) and the image of `Z` in `X₃`
(`imageInX₃`).

The main result, `eq_of_le_of_interX₁_eq_of_imageInX₃_eq`, is the short five lemma applied
to this sequence: among the subobjects of `X₂` containing it, `Z` is determined by its
intersection with `X₁` together with its image in `X₃`.
-/

@[expose] public section

namespace CategoryTheory.ShortComplex.ShortExact

open Limits

variable {C : Type*} [Category* C] [Abelian C] {S : ShortComplex C}

/-- The cycles of `Z ⟶ X₂ ⟶ X₃` map monomorphically to `X₂`, hence factor through `X₁`.
The resulting monomorphism exhibits the intersection of `Z` with `X₁` as a subobject
of `X₁`. -/
noncomputable def kerToX₁ (hS : S.ShortExact) (Z : Subobject S.X₂) :
    kernel (Z.arrow ≫ S.g) ⟶ S.X₁ :=
  (KernelFork.IsLimit.lift' hS.fIsKernel (kernel.ι (Z.arrow ≫ S.g) ≫ Z.arrow)
    (by rw [Category.assoc]; exact kernel.condition _)).1

@[reassoc (attr := simp)]
lemma kerToX₁_comp_f (hS : S.ShortExact) (Z : Subobject S.X₂) :
    kerToX₁ hS Z ≫ S.f = kernel.ι (Z.arrow ≫ S.g) ≫ Z.arrow :=
  (KernelFork.IsLimit.lift' hS.fIsKernel (kernel.ι (Z.arrow ≫ S.g) ≫ Z.arrow)
    (by rw [Category.assoc]; exact kernel.condition _)).2

instance (hS : S.ShortExact) (Z : Subobject S.X₂) : Mono (kerToX₁ hS Z) := by
  have : Mono (kerToX₁ hS Z ≫ S.f) := by rw [kerToX₁_comp_f]; infer_instance
  exact mono_of_mono _ S.f

/-- The intersection of a subobject `Z` of `X₂` with `X₁`, as a subobject of `X₁`. -/
noncomputable def interX₁ (hS : S.ShortExact) (Z : Subobject S.X₂) : Subobject S.X₁ :=
  Subobject.mk (kerToX₁ hS Z)

/-- The image of a subobject `Z` of `X₂` in `X₃`, as a subobject of `X₃`: the opcycles of
`Z ⟶ X₂ ⟶ X₃` map monomorphically to `X₃`. -/
noncomputable def imageInX₃ (Z : Subobject S.X₂) : Subobject S.X₃ :=
  Subobject.mk (Abelian.factorThruCoimage (Z.arrow ≫ S.g))

variable {Z W : Subobject S.X₂}

/-- The map induced on cycles by an inclusion of subobjects of `X₂`. -/
noncomputable def kerMap (h : Z ≤ W) :
    kernel (Z.arrow ≫ S.g) ⟶ kernel (W.arrow ≫ S.g) :=
  kernel.lift _ (kernel.ι (Z.arrow ≫ S.g) ≫ Subobject.ofLE Z W h) (by
    rw [Category.assoc, Subobject.ofLE_arrow_assoc]; exact kernel.condition _)

@[reassoc (attr := simp)]
lemma kerMap_ι (h : Z ≤ W) :
    kerMap h ≫ kernel.ι (W.arrow ≫ S.g) = kernel.ι (Z.arrow ≫ S.g) ≫ Subobject.ofLE Z W h :=
  kernel.lift_ι _ _ _

lemma kerMap_comp_kerToX₁ (hS : S.ShortExact) (h : Z ≤ W) :
    kerMap h ≫ kerToX₁ hS W = kerToX₁ hS Z := by
  have := hS.mono_f
  rw [← cancel_mono S.f, Category.assoc, kerToX₁_comp_f, ← Category.assoc, kerMap_ι,
    Category.assoc, Subobject.ofLE_arrow, kerToX₁_comp_f]

lemma interX₁_le (hS : S.ShortExact) (h : Z ≤ W) : interX₁ hS Z ≤ interX₁ hS W :=
  Subobject.mk_le_mk_of_comm (kerMap h) (kerMap_comp_kerToX₁ hS h)

/-- The map induced on opcycles by an inclusion of subobjects of `X₂`. -/
noncomputable def coimageMap (h : Z ≤ W) :
    Abelian.coimage (Z.arrow ≫ S.g) ⟶ Abelian.coimage (W.arrow ≫ S.g) :=
  cokernel.desc _ (Subobject.ofLE Z W h ≫ Abelian.coimage.π (W.arrow ≫ S.g)) (by
    rw [← Category.assoc, ← kerMap_ι h, Category.assoc, cokernel.condition, comp_zero])

@[reassoc (attr := simp)]
lemma coimage_π_comp_coimageMap (h : Z ≤ W) :
    Abelian.coimage.π (Z.arrow ≫ S.g) ≫ coimageMap h
      = Subobject.ofLE Z W h ≫ Abelian.coimage.π (W.arrow ≫ S.g) :=
  cokernel.π_desc _ _ _

lemma coimageMap_comp_factorThruCoimage (h : Z ≤ W) :
    coimageMap h ≫ Abelian.factorThruCoimage (W.arrow ≫ S.g)
      = Abelian.factorThruCoimage (Z.arrow ≫ S.g) := by
  rw [← cancel_epi (Abelian.coimage.π (Z.arrow ≫ S.g)), ← Category.assoc,
    coimage_π_comp_coimageMap, Category.assoc, Abelian.coimage.fac, Abelian.coimage.fac,
    Subobject.ofLE_arrow_assoc]

lemma imageInX₃_le (h : Z ≤ W) : imageInX₃ Z ≤ imageInX₃ W :=
  Subobject.mk_le_mk_of_comm (coimageMap h) (coimageMap_comp_factorThruCoimage h)

/-- Among the subobjects of `X₂` that contain it, a subobject is determined by its cycles
(its intersection with `X₁`) together with its opcycles (its image in `X₃`). This is the
short five lemma applied to `0 ⟶ Z ∩ X₁ ⟶ Z ⟶ Z/(Z ∩ X₁) ⟶ 0` and its counterpart
for `W`. -/
lemma eq_of_le_of_interX₁_eq_of_imageInX₃_eq (hS : S.ShortExact) (h : Z ≤ W)
    (h₁ : interX₁ hS Z = interX₁ hS W) (h₃ : imageInX₃ Z = imageInX₃ W) : Z = W := by
  have sex (V : Subobject S.X₂) :
      (ShortComplex.mk (kernel.ι (V.arrow ≫ S.g)) (Abelian.coimage.π (V.arrow ≫ S.g))
        (by simp)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  have : IsIso (Subobject.ofLE Z W h) :=
    ShortComplex.isIso₂_of_shortExact_of_isIso₁₃'
      { τ₁ := kerMap h
        τ₂ := Subobject.ofLE Z W h
        τ₃ := coimageMap h
        comm₁₂ := kerMap_ι h
        comm₂₃ := (coimage_π_comp_coimageMap h).symm }
      (sex Z) (sex W)
      (Subobject.isIso_of_mk_eq_mk _ (kerMap_comp_kerToX₁ hS h) h₁)
      (Subobject.isIso_of_mk_eq_mk _ (coimageMap_comp_factorThruCoimage h) h₃)
  exact Subobject.eq_of_comm (asIso (Subobject.ofLE Z W h)) (by simp)

end CategoryTheory.ShortComplex.ShortExact
