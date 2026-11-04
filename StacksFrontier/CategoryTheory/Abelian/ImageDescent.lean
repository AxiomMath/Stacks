module

public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Descending a morphism along the factorisation through an image

In an abelian category the map `A ⟶ Abelian.image a` of the canonical factorisation of
`a : A ⟶ B` is an epimorphism with kernel `kernel.ι a`, so a morphism `b : A ⟶ D` killing
`kernel.ι a` descends uniquely to the image of `a`. That descent is constructed here, together
with the criterion for it to be a monomorphism: the two kernels annihilate each other's
morphism, which makes the descents in the two directions mutually inverse.

This is the universal property that pins down the canonical map out of a product `I · F`: the
product is the image of an action map `a`, and the second map out of it is the descent of
multiplication by a section.

## Main definitions

* `CategoryTheory.Abelian.imageDesc`: the descent `Abelian.image a ⟶ D` of `b` along the
  factorisation of `a` through its image.

## Main results

* `CategoryTheory.Abelian.factorThruImage_imageDesc`: the descent composed with the
  factorisation recovers `b`, which is the property characterising it.
* `CategoryTheory.Abelian.mono_imageDesc`: the descent is a monomorphism as soon as each of
  the two morphisms kills the other's kernel.

## Implementation notes

The descent is built from `Abelian.coimageIsoImage`, which identifies the image of `a` with
`cokernel (kernel.ι a)`; the descent is then `cokernel.desc`. Monomorphy is obtained by
exhibiting a one-sided inverse: the descent of `Abelian.factorThruImage b` along `a` and the
descent of `Abelian.factorThruImage a` along `b` compose to the identity, since both
composites are determined by their restriction along the epimorphism
`Abelian.factorThruImage a`.
-/

@[expose] public section

open CategoryTheory.Limits

universe v w

namespace CategoryTheory.Abelian

variable {C : Type v} [Category.{w} C] [Abelian C] {A B D : C}

/-- The descent of `b : A ⟶ D` to the image of `a : A ⟶ B`, available when `b` kills the
kernel of `a`: the image of `a` is the cokernel of `kernel.ι a`, and the descent is the one
provided by that cokernel. -/
noncomputable def imageDesc (a : A ⟶ B) (b : A ⟶ D) (h : kernel.ι a ≫ b = 0) :
    Abelian.image a ⟶ D :=
  (Abelian.coimageIsoImage a).inv ≫ cokernel.desc (kernel.ι a) b h

/-- The descent of `b` to the image of `a`, composed with the factorisation of `a` through
that image, is `b` again. Since `Abelian.factorThruImage a` is an epimorphism this property
determines the descent. -/
theorem factorThruImage_imageDesc (a : A ⟶ B) (b : A ⟶ D) (h : kernel.ι a ≫ b = 0) :
    Abelian.factorThruImage a ≫ imageDesc a b h = b := by
  have he : cokernel.π (kernel.ι a) ≫ (Abelian.coimageIsoImage a).hom =
      Abelian.factorThruImage a := by
    simp [Abelian.coimageIsoImage, Abelian.coimageImageComparison]
  rw [← he]
  simp [imageDesc]

/-- If `b` kills the kernel of `a`, so does the factorisation of `b` through its image. -/
private theorem kernel_ι_comp_factorThruImage {a : A ⟶ B} {b : A ⟶ D} (h : kernel.ι a ≫ b = 0) :
    kernel.ι a ≫ Abelian.factorThruImage b = 0 := by
  apply (cancel_mono (Abelian.image.ι b)).1
  simpa using h

/-- The descent of `b` to the image of `a` is a monomorphism as soon as `b` kills the kernel
of `a` and `a` kills the kernel of `b`. Under those hypotheses the two images have the same
descent data in both directions, and the resulting pair of morphisms between them composes to
the identity. -/
theorem mono_imageDesc (a : A ⟶ B) (b : A ⟶ D)
    (hab : kernel.ι a ≫ b = 0) (hba : kernel.ι b ≫ a = 0) :
    Mono (imageDesc a b hab) := by
  let f := imageDesc a (Abelian.factorThruImage b) (kernel_ι_comp_factorThruImage hab)
  let g := imageDesc b (Abelian.factorThruImage a) (kernel_ι_comp_factorThruImage hba)
  have hfg : f ≫ g = 𝟙 _ := by
    apply (cancel_epi (Abelian.factorThruImage a)).1
    simp only [← Category.assoc, f, factorThruImage_imageDesc, g, Category.comp_id]
  have _ : Mono f := mono_of_mono_fac hfg
  have he : f ≫ Abelian.image.ι b = imageDesc a b hab := by
    apply (cancel_epi (Abelian.factorThruImage a)).1
    simp only [← Category.assoc, f, factorThruImage_imageDesc, Abelian.image.fac]
  rw [← he]
  infer_instance

end CategoryTheory.Abelian

end
