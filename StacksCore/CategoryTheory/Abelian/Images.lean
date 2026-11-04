module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.Images
public import Mathlib.CategoryTheory.Preadditive.Basic
public import StacksCore.CategoryTheory.Limits.Shapes.Kernels
public import StacksCore.CategoryTheory.Subobject.Limits
import StacksCore.Tactic.StacksAttribute

/-! # Images in abelian categories

Mirror lemmas about images: the uniqueness of the factorisation through the coimage-image
comparison (Stacks 0107), and, in an abelian category, the image of a base change
`snd : X ×_Z Y ⟶ Y` of `f : X ⟶ Z` along `g`, which is the preimage `g⁻¹(Im f)`
(`IsPullback.imageSubobject_snd`, `Abelian.imageSubobject_pullback_snd`), together with the
Beck–Chevalley identity `snd(fst⁻¹(X')) = g⁻¹(f(X'))` (`IsPullback.exists_pullback`); dually the
kernel of a cobase change `inr : Z ⟶ Y ⊔_X Z` of `f : X ⟶ Y` along `g` is the image `g(Ker f)`
(`IsPushout.kernelSubobject_inr`, `Abelian.kernelSubobject_pushout_inr`), with the dual identity
`inr⁻¹(inl(Y')) = g(f⁻¹(Y'))` (`IsPushout.pullback_exists`). Also: the kernel of any cokernel of
`k` is the image of `k` (`Abelian.kernelSubobject_eq_imageSubobject_of_isColimit`).
-/

@[expose] public section

add_to_stacks 0106 CategoryTheory.Abelian.image
add_to_stacks 0106 CategoryTheory.Abelian.coimage

open CategoryTheory Limits

@[stacks 0107]
lemma unique_factorThru {C : Type*} [Category* C] [Preadditive C] {X Y : C} (f : X ⟶ Y)
    [HasKernel f] [HasCokernel f] [HasKernel (cokernel.π f)] [HasCokernel (kernel.ι f)]
    (φ : Abelian.coimage f ⟶ Abelian.image f) (hφ : Abelian.coimage.π f ≫ φ ≫
    Abelian.image.ι f = f) : φ = Abelian.coimageImageComparison f := by
  conv_rhs at hφ => rw [← Abelian.coimage_image_factorisation f]
  rwa [cancel_epi, cancel_mono] at hφ

namespace CategoryTheory.Abelian

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {P Q : C} (f : P ⟶ Q)
  [HasCokernel f] [HasKernel f] [HasKernel (cokernel.π f)] [HasCokernel (kernel.ι f)]

/-- The projection onto the coimage followed by the comparison `Coim(f) ⟶ Im(f)` is the
canonical morphism `P ⟶ Im(f)`. -/
@[reassoc (attr := simp)]
theorem coimage_π_comp_coimageImageComparison :
    coimage.π f ≫ coimageImageComparison f = Abelian.factorThruImage f := by
  rw [← cancel_mono (Abelian.image.ι f), Category.assoc, coimage_image_factorisation, image.fac]

/-- The comparison `Coim(f) ⟶ Im(f)` followed by the inclusion of the image is the canonical
morphism `Coim(f) ⟶ Q`. -/
@[reassoc (attr := simp)]
theorem coimageImageComparison_comp_image_ι :
    coimageImageComparison f ≫ Abelian.image.ι f = Abelian.factorThruCoimage f := by
  rw [← cancel_epi (coimage.π f), coimage_image_factorisation, coimage.fac]

end CategoryTheory.Abelian

namespace CategoryTheory.IsPullback

variable {C : Type*} [Category* C] [Abelian C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}
  {g : Y ⟶ Z}

/-- In an abelian category, the image of the base change `snd : X ×_Z Y ⟶ Y` of `f : X ⟶ Z`
along `g : Y ⟶ Z` is the preimage `g⁻¹(Im f)` of the image of `f`: writing `f = e ≫ m` with
`m : Im f ⟶ Z`, the fibre product `X ×_Z Y` is also the base change of the epimorphism `e`
along `g⁻¹(Im f) ⟶ Im f`, so it maps onto `g⁻¹(Im f) ⊆ Y`. -/
theorem imageSubobject_snd (h : IsPullback fst snd f g) :
    imageSubobject snd = (Subobject.pullback g).obj (imageSubobject f) := by
  have t := Subobject.isPullback g (imageSubobject f)
  have h' : IsPullback fst snd (factorThruImageSubobject f ≫ (imageSubobject f).arrow) g := by
    rwa [imageSubobject_arrow_comp]
  have w : (fst ≫ factorThruImageSubobject f) ≫ (imageSubobject f).arrow = snd ≫ g := by
    rw [Category.assoc]; exact h'.w
  -- `X ×_Z Y ⟶ g⁻¹(Im f)` is the base change of the epimorphism `X ⟶ Im f`, so an epimorphism
  have : Epi (t.lift _ _ w) := Abelian.epi_snd_of_isLimit _ _ (h'.of_bot' t).isLimit
  rw [← t.lift_snd _ _ w, Subobject.imageSubobject_comp_eq_exists,
    Subobject.imageSubobject_eq_top_of_epi (t.lift _ _ w), Subobject.exists_obj_top,
    imageSubobject_mono ((Subobject.pullback g).obj (imageSubobject f)).arrow, Subobject.mk_arrow]

/-- The image of the base change `fst : X ×_Z Y ⟶ X` of `g` along `f` is `f⁻¹(Im g)`. -/
theorem imageSubobject_fst (h : IsPullback fst snd f g) :
    imageSubobject fst = (Subobject.pullback f).obj (imageSubobject g) :=
  h.flip.imageSubobject_snd

/-- The Beck–Chevalley identity for a pullback square in an abelian category:
`snd(fst⁻¹(X')) = g⁻¹(f(X'))` for every subobject `X'` of `X`. -/
theorem exists_pullback (h : IsPullback fst snd f g) (X' : Subobject X) :
    (Subobject.exists snd).obj ((Subobject.pullback fst).obj X') =
      (Subobject.pullback g).obj ((Subobject.exists f).obj X') := by
  rw [Subobject.exists_eq_imageSubobject, Subobject.exists_eq_imageSubobject]
  exact ((Subobject.isPullback fst X').paste_vert h).imageSubobject_snd

end CategoryTheory.IsPullback

namespace CategoryTheory.Abelian

variable {C : Type*} [Category* C] [Abelian C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)

/-- In an abelian category, `Im(X ×_Z Y ⟶ Y) = g⁻¹(Im f)`. -/
theorem imageSubobject_pullback_snd :
    imageSubobject (pullback.snd f g) = (Subobject.pullback g).obj (imageSubobject f) :=
  (IsPullback.of_hasPullback f g).imageSubobject_snd

/-- In an abelian category, `Im(X ×_Z Y ⟶ X) = f⁻¹(Im g)`. -/
theorem imageSubobject_pullback_fst :
    imageSubobject (pullback.fst f g) = (Subobject.pullback f).obj (imageSubobject g) :=
  (IsPullback.of_hasPullback f g).imageSubobject_fst

end CategoryTheory.Abelian

namespace CategoryTheory.Abelian

variable {C : Type*} [Category* C] [Abelian C]

/-- In an abelian category, the kernel of any cokernel of `k` is the image of `k`. -/
theorem kernelSubobject_eq_imageSubobject_of_isColimit {X Y Z : C} {k : X ⟶ Y} {p : Y ⟶ Z}
    {w : k ≫ p = 0} (hp : IsColimit (CokernelCofork.ofπ p w)) :
    kernelSubobject p = imageSubobject k := by
  have hφ : cokernel.π k ≫ ((cokernelIsCokernel k).coconePointUniqueUpToIso hp).hom = p :=
    (cokernelIsCokernel k).comp_coconePointUniqueUpToIso_hom hp WalkingParallelPair.one
  rw [← hφ, kernelSubobject_comp_mono]
  exact Subobject.mk_eq_mk_of_comm _ _ (imageIsoImage k) (imageIsoImage_hom_comp_image_ι k)

end CategoryTheory.Abelian

namespace CategoryTheory.IsPushout

variable {C : Type*} [Category* C] [Abelian C] {X Y Z P : C} {f : X ⟶ Y} {g : X ⟶ Z} {inl : Y ⟶ P}
  {inr : Z ⟶ P}

/-- In an abelian category, the kernel of the cobase change `inr : Z ⟶ Y ⊔_X Z` of `f : X ⟶ Y`
along `g : X ⟶ Z` is the image `g(Ker f)` of the kernel of `f`: writing `f = e ≫ m` with
`e : X ⟶ Coim f` a cokernel of `Ker f ⟶ X` and `m : Coim f ⟶ Y` a monomorphism, the pushout
`Y ⊔_X Z` is also the pushout of `m` along `Coim f ⟶ Coim f ⊔_X Z`, so `inr` factors as
`Z ⟶ Coim f ⊔_X Z`, a cokernel of `Ker f ⟶ X ⟶ Z`, followed by a monomorphism. The dual of
`IsPullback.imageSubobject_snd`, and the `Subobject` form of Mathlib's
`Abelian.epi_kernel_map_of_isPushout` (`Ker f ⟶ Ker inr` is an epimorphism). -/
theorem kernelSubobject_inr (h : IsPushout f g inl inr) :
    kernelSubobject inr = (Subobject.exists g).obj (kernelSubobject f) := by
  have t := IsPushout.of_hasPushout (Abelian.coimage.π f) g
  have h' : IsPushout (Abelian.coimage.π f ≫ Abelian.factorThruCoimage f) g inl inr := by
    rwa [Abelian.coimage.fac]
  have w : Abelian.coimage.π f ≫ Abelian.factorThruCoimage f ≫ inl = g ≫ inr := by
    rw [← Category.assoc, h'.w]
  -- `Coim f ⊔_X Z ⟶ Y ⊔_X Z` is the cobase change of the monomorphism `Coim f ⟶ Y`, so a mono
  have : Mono (t.desc _ _ w) := Abelian.mono_inr_of_isColimit _ _ (h'.of_left' t).isColimit
  -- `Z ⟶ Coim f ⊔_X Z` is a cokernel of `Ker f ⟶ X ⟶ Z`, so its kernel is the image `g(Ker f)`
  have hc := CokernelCofork.IsColimit.ofIsPushout (w := cokernel.condition (kernel.ι f)) t.flip
    (cokernelIsCokernel (kernel.ι f))
  rw [← t.inr_desc _ _ w, kernelSubobject_comp_mono,
    Abelian.kernelSubobject_eq_imageSubobject_of_isColimit hc,
    Subobject.imageSubobject_comp_eq_exists, imageSubobject_mono]

/-- The kernel of the cobase change `inl : Y ⟶ Y ⊔_X Z` of `g` along `f` is `f(Ker g)`. -/
theorem kernelSubobject_inl (h : IsPushout f g inl inr) :
    kernelSubobject inl = (Subobject.exists f).obj (kernelSubobject g) :=
  h.flip.kernelSubobject_inr

/-- The Beck–Chevalley identity for a pushout square in an abelian category:
`inr⁻¹(inl(Y')) = g(f⁻¹(Y'))` for every subobject `Y'` of `Y`. The dual of
`IsPullback.exists_pullback`. -/
theorem pullback_exists (h : IsPushout f g inl inr) (Y' : Subobject Y) :
    (Subobject.pullback inr).obj ((Subobject.exists inl).obj Y') =
      (Subobject.exists g).obj ((Subobject.pullback f).obj Y') := by
  -- `Y ⟶ Y/Y'`, `Y ⟶ P`, `Y/Y' ⟶ P/inl(Y')`, `P ⟶ P/inl(Y')` is a pushout square
  have t : IsPushout inl (cokernel.π Y'.arrow) (cokernel.π (Y'.arrow ≫ inl))
      (cokernel.desc Y'.arrow (inl ≫ cokernel.π (Y'.arrow ≫ inl))
        (by rw [← Category.assoc, cokernel.condition])) :=
    of_isCokernel (w := cokernel.condition Y'.arrow) (w' := cokernel.condition (Y'.arrow ≫ inl))
      (cokernel.π_desc _ _ _).symm (cokernelIsCokernel Y'.arrow)
      (cokernelIsCokernel (Y'.arrow ≫ inl))
  -- `inl(Y')` is the kernel of `P ⟶ P/inl(Y')` and `f⁻¹(Y')` the kernel of `X ⟶ Y ⟶ Y/Y'`
  have e₁ : (Subobject.exists inl).obj Y' = kernelSubobject (cokernel.π (Y'.arrow ≫ inl)) := by
    rw [Abelian.kernelSubobject_eq_imageSubobject_of_isColimit (w := cokernel.condition _)
      (cokernelIsCokernel _), Subobject.imageSubobject_comp_eq_exists, imageSubobject_mono,
      Subobject.mk_arrow]
  have e₂ : (Subobject.pullback f).obj Y' = kernelSubobject (f ≫ cokernel.π Y'.arrow) := by
    rw [← Subobject.pullback_kernelSubobject,
      Abelian.kernelSubobject_eq_imageSubobject_of_isColimit (w := cokernel.condition _)
        (cokernelIsCokernel Y'.arrow), imageSubobject_mono, Subobject.mk_arrow]
  -- paste `t` to the right of `h` and take the kernel of the bottom composite
  rw [e₁, Subobject.pullback_kernelSubobject, e₂]
  exact (h.paste_horiz t.flip).kernelSubobject_inr

end CategoryTheory.IsPushout

namespace CategoryTheory.Abelian

variable {C : Type*} [Category* C] [Abelian C] {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)

/-- In an abelian category, `Ker(Z ⟶ Y ⊔_X Z) = g(Ker f)`. -/
theorem kernelSubobject_pushout_inr :
    kernelSubobject (pushout.inr f g) = (Subobject.exists g).obj (kernelSubobject f) :=
  (IsPushout.of_hasPushout f g).kernelSubobject_inr

/-- In an abelian category, `Ker(Y ⟶ Y ⊔_X Z) = f(Ker g)`. -/
theorem kernelSubobject_pushout_inl :
    kernelSubobject (pushout.inl f g) = (Subobject.exists f).obj (kernelSubobject g) :=
  (IsPushout.of_hasPushout f g).kernelSubobject_inl

end CategoryTheory.Abelian
