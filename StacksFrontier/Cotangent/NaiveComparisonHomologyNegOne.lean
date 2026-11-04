module

public import StacksFrontier.Algebra.Homology.ExtendShortExact
public import StacksFrontier.Algebra.Homology.MappingConeOfKernel
public import StacksFrontier.Cotangent.CotangentComplexHomologyNegOne
public import StacksFrontier.Cotangent.NaiveComparisonCone

/-!
# `Ker(d)`, `Im(d)` and `Coker(d)` in cohomological degrees

`StacksFrontier/Cotangent/SurjectivePresentationHigherHomology.lean` studies the kernel, image and
cokernel of the map `d : 𝒥/𝒥² ⟶ Ω` on the standard resolution as *Moore* complexes, indexed by
`ℕ`. This file carries that factorisation over to the cochain complexes in cohomological degrees
`≤ 0` that `Stacks.Cotangent.conormalToCotangentComplex` lives in, by extending along
`ComplexShape.embeddingUpIntLE 0`: extension preserves short exactness
(`HomologicalComplex.shortExact_extend`) and changes no homology
(`HomologicalComplex.extendHomologyIso`).

The point of doing so is `Stacks.Cotangent.isIso_homologyMap_kernelConeToCotangentCone`: the
mapping cone of `d` has, in cohomological degree `-1`, the homology of the cone of
`Ker(d) ⟶ 0`, by `CochainComplex.mappingCone.isIso_homologyMap_mapFromZero` applied to the
factorisation. Its two inputs are exactly the vanishing of `H₁(Coker d)` and `H₂(Coker d)` of
Remark 09D5, which `Stacks.Cotangent.isZero_homology_cokernel_conormalToCotangentMoore` provides.

## Main definitions

* `Stacks.Cotangent.conormalKernelComplex`, `Stacks.Cotangent.conormalImageComplex` and
  `Stacks.Cotangent.conormalCokernelComplex`: `Ker(d)`, `Im(d)` and `Coker(d)` in cohomological
  degrees, with the four maps between them and the two complexes of `d`.
* `Stacks.Cotangent.kernelConeToCotangentCone`: the comparison
  `cone (Ker(d) ⟶ 0) ⟶ cone(d)`.

## Main results

* `Stacks.Cotangent.shortExact_conormalKernelImage` and
  `Stacks.Cotangent.shortExact_conormalImageCokernel`: the two short exact sequences
  `0 → Ker(d) → 𝒥/𝒥² → Im(d) → 0` and `0 → Im(d) → Ω → Coker(d) → 0` of cochain complexes.
* `Stacks.Cotangent.conormalKernelComplex_d`: the differential of `Ker(d)` out of cohomological
  degree `-2` vanishes, `Ker(d)` being a *constant* simplicial module.
* `Stacks.Cotangent.isIso_homologyMap_kernelConeToCotangentCone`: **the cone of `d` has the
  homology of the cone of `Ker(d) ⟶ 0` in cohomological degree `-1`.**

## References

* [Stacks Project, Tag 09D5](https://stacks.math.columbia.edu/tag/09D5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

open scoped ZeroObject

universe u v

namespace Stacks.Cotangent

open CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A)

/-! ### The factorisation of `d` through its image, on Moore complexes -/

/-- The projection of `𝒥/𝒥²` onto the image of `d`, on Moore complexes: the projection onto the
coimage followed by the coimage-image comparison, which is an isomorphism. -/
abbrev conormalToImageMoore :
    conormalMooreComplex A B ⟶ Abelian.image (conormalToCotangentMoore A B) :=
  Abelian.coimage.π (conormalToCotangentMoore A B) ≫
    Abelian.coimageImageComparison (conormalToCotangentMoore A B)

/-- The factorisation `d = (𝒥/𝒥² ↠ Im d) ≫ (Im d ↪ Ω)`. -/
theorem conormalToImageMoore_comp :
    conormalToImageMoore A B ≫ Abelian.image.ι (conormalToCotangentMoore A B) =
      conormalToCotangentMoore A B := by
  rw [Category.assoc, Abelian.coimage_image_factorisation]

/-- `Ker(d)` is killed by the projection onto the image. -/
theorem kernelι_comp_conormalToImageMoore :
    kernel.ι (conormalToCotangentMoore A B) ≫ conormalToImageMoore A B = 0 := by
  rw [← Category.assoc]
  simp

/-- The short exact sequence `0 → Ker(d) → 𝒥/𝒥² → Im(d) → 0` of Moore complexes. -/
theorem shortExact_kernelImageMoore :
    (ShortComplex.mk (kernel.ι (conormalToCotangentMoore A B)) (conormalToImageMoore A B)
      (kernelι_comp_conormalToImageMoore A B)).ShortExact := by
  refine ShortComplex.shortExact_of_iso ?_ (shortExact_kernelConormalToCotangentMoore A B)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (asIso (Abelian.coimageImageComparison (conormalToCotangentMoore A B))) (by simp) (by simp)

/-! ### The same in cohomological degrees -/

/-- `Ker(d)` in cohomological degrees `≤ 0`. -/
abbrev conormalKernelComplex : CochainComplex (ModuleCat.{max u v} B) ℤ :=
  (kernel (conormalToCotangentMoore A B)).extend (ComplexShape.embeddingUpIntLE (0 : ℤ))

/-- `Im(d)` in cohomological degrees `≤ 0`. -/
abbrev conormalImageComplex : CochainComplex (ModuleCat.{max u v} B) ℤ :=
  (Abelian.image (conormalToCotangentMoore A B)).extend (ComplexShape.embeddingUpIntLE (0 : ℤ))

/-- `Coker(d)` in cohomological degrees `≤ 0`. -/
abbrev conormalCokernelComplex : CochainComplex (ModuleCat.{max u v} B) ℤ :=
  (cokernel (conormalToCotangentMoore A B)).extend (ComplexShape.embeddingUpIntLE (0 : ℤ))

/-- The inclusion `Ker(d) ⟶ 𝒥/𝒥²` in cohomological degrees. -/
abbrev conormalKernelIota : conormalKernelComplex A B ⟶ conormalComplex A B :=
  HomologicalComplex.extendMap (kernel.ι (conormalToCotangentMoore A B))
    (ComplexShape.embeddingUpIntLE (0 : ℤ))

/-- The projection `𝒥/𝒥² ⟶ Im(d)` in cohomological degrees. -/
abbrev conormalToImage : conormalComplex A B ⟶ conormalImageComplex A B :=
  HomologicalComplex.extendMap (conormalToImageMoore A B)
    (ComplexShape.embeddingUpIntLE (0 : ℤ))

/-- The inclusion `Im(d) ⟶ Ω` in cohomological degrees. -/
abbrev conormalImageIota : conormalImageComplex A B ⟶ cotangentComplex A B :=
  HomologicalComplex.extendMap (Abelian.image.ι (conormalToCotangentMoore A B))
    (ComplexShape.embeddingUpIntLE (0 : ℤ))

/-- The projection `Ω ⟶ Coker(d)` in cohomological degrees. -/
abbrev conormalToCokernel : cotangentComplex A B ⟶ conormalCokernelComplex A B :=
  HomologicalComplex.extendMap (cokernel.π (conormalToCotangentMoore A B))
    (ComplexShape.embeddingUpIntLE (0 : ℤ))

/-- The factorisation of `d` through its image, in cohomological degrees. -/
theorem conormalToImage_comp :
    conormalToImage A B ≫ conormalImageIota A B = conormalToCotangentComplex A B := by
  rw [show conormalToImage A B ≫ conormalImageIota A B =
      HomologicalComplex.extendMap (conormalToImageMoore A B ≫
          Abelian.image.ι (conormalToCotangentMoore A B))
        (ComplexShape.embeddingUpIntLE (0 : ℤ)) from
    (HomologicalComplex.extendMap_comp _ _ _).symm, conormalToImageMoore_comp]
  rfl

/-- `Ker(d)` is killed by the projection onto the image, in cohomological degrees. -/
theorem conormalKernelIota_comp_conormalToImage :
    conormalKernelIota A B ≫ conormalToImage A B = 0 := by
  rw [show conormalKernelIota A B ≫ conormalToImage A B =
      HomologicalComplex.extendMap (kernel.ι (conormalToCotangentMoore A B) ≫
          conormalToImageMoore A B) (ComplexShape.embeddingUpIntLE (0 : ℤ)) from
    (HomologicalComplex.extendMap_comp _ _ _).symm, kernelι_comp_conormalToImageMoore,
    HomologicalComplex.extendMap_zero]

/-- `Im(d)` is killed by the projection onto the cokernel, in cohomological degrees. -/
theorem conormalImageIota_comp_conormalToCokernel :
    conormalImageIota A B ≫ conormalToCokernel A B = 0 := by
  rw [show conormalImageIota A B ≫ conormalToCokernel A B =
      HomologicalComplex.extendMap (Abelian.image.ι (conormalToCotangentMoore A B) ≫
          cokernel.π (conormalToCotangentMoore A B))
        (ComplexShape.embeddingUpIntLE (0 : ℤ)) from
    (HomologicalComplex.extendMap_comp _ _ _).symm,
    show Abelian.image.ι (conormalToCotangentMoore A B) ≫
      cokernel.π (conormalToCotangentMoore A B) = 0 from kernel.condition _,
    HomologicalComplex.extendMap_zero]

/-- **The short exact sequence `0 → Ker(d) → 𝒥/𝒥² → Im(d) → 0`** of cochain complexes. -/
theorem shortExact_conormalKernelImage :
    (ShortComplex.mk (conormalKernelIota A B) (conormalToImage A B)
      (conormalKernelIota_comp_conormalToImage A B)).ShortExact :=
  HomologicalComplex.shortExact_extend _ _ (shortExact_kernelImageMoore A B)

/-- **The short exact sequence `0 → Im(d) → Ω → Coker(d) → 0`** of cochain complexes. -/
theorem shortExact_conormalImageCokernel :
    (ShortComplex.mk (conormalImageIota A B) (conormalToCokernel A B)
      (conormalImageIota_comp_conormalToCokernel A B)).ShortExact :=
  HomologicalComplex.shortExact_extend _ _ (shortExact_imageConormalToCotangentMoore A B)

/-- `Coker(d)` has no homology in negative cohomological degrees: it is the constant complex on
`Ω[B⁄A]`, by Remark 09D5. -/
theorem isZero_conormalCokernelComplex_homology (n : ℕ) (hn : 0 < n) :
    IsZero ((conormalCokernelComplex A B).homology (-(n : ℤ))) :=
  (isZero_homology_cokernel_conormalToCotangentMoore A B n hn).of_iso
    (HomologicalComplex.extendHomologyIso (cokernel (conormalToCotangentMoore A B))
      (ComplexShape.embeddingUpIntLE (0 : ℤ)) (j := n) (j' := -(n : ℤ)) (by simp))

/-- The differential of `Ker(d)` into degree `0` vanishes: `Ker(d)` is the Moore complex of a
*constant* simplicial module (`Stacks.Cotangent.kernelConormalToCotangentMooreIso`), whose
differential out of degree `1` is `δ₀ - δ₁ = 0`. -/
theorem kernel_conormalToCotangentMoore_d :
    (kernel (conormalToCotangentMoore A B)).d 1 0 = 0 := by
  have h : (h1ConstMooreComplex A B).d 1 0 = 0 := by
    have e := AlgebraicTopology.alternatingFaceMapComplexConst.app
      (ModuleCat.of B (Algebra.H1Cotangent A B))
    have hd : (ChainComplex.alternatingConst.obj
        (ModuleCat.of B (Algebra.H1Cotangent A B))).d 1 0 = 0 := by
      simp [ChainComplex.alternatingConst, HomologicalComplex.alternatingConst]
      rfl
    have hcomm := e.hom.comm 1 0
    rw [hd, Limits.comp_zero] at hcomm
    have : Mono (e.hom.f 0) :=
      inferInstanceAs (Mono ((HomologicalComplex.eval _ (ComplexShape.down ℕ) 0).map e.hom))
    exact zero_of_comp_mono _ hcomm.symm
  have hcomm := (kernelConormalToCotangentMooreIso A B).hom.comm 1 0
  rw [h, Limits.comp_zero] at hcomm
  have : Mono ((kernelConormalToCotangentMooreIso A B).hom.f 0) :=
    inferInstanceAs (Mono ((HomologicalComplex.eval _ (ComplexShape.down ℕ) 0).map
      (kernelConormalToCotangentMooreIso A B).hom))
  exact zero_of_comp_mono _ hcomm.symm

/-- The differential of `Ker(d)` out of cohomological degree `-1` vanishes. -/
theorem conormalKernelComplex_d :
    (conormalKernelComplex A B).d (-1) 0 = 0 := by
  rw [HomologicalComplex.extend_d_eq (kernel (conormalToCotangentMoore A B))
    (ComplexShape.embeddingUpIntLE (0 : ℤ)) (i := 1) (j := 0) (by simp) (by simp),
    kernel_conormalToCotangentMoore_d]
  simp

/-- `Ker(d)` is killed by `d`, in cohomological degrees. -/
theorem conormalKernelIota_comp_conormalToCotangentComplex :
    conormalKernelIota A B ≫ conormalToCotangentComplex A B = 0 := by
  rw [← conormalToImage_comp, ← Category.assoc, conormalKernelIota_comp_conormalToImage,
    zero_comp]

/-! ### The cone of `d` in cohomological degree `-1` -/

/-- The mapping cone of `Ker(d) ⟶ 0`, a shift of `Ker(d)`. -/
abbrev kernelCone : CochainComplex (ModuleCat.{max u v} B) ℤ :=
  CochainComplex.mappingCone
    (0 : conormalKernelComplex A B ⟶ (0 : CochainComplex (ModuleCat.{max u v} B) ℤ))

/-- **The comparison `cone (Ker(d) ⟶ 0) ⟶ cone(d)`**, the inclusion of the kernel of `d` into
the `𝒥₀/𝒥₀²` summand of the cone. -/
def kernelConeToCotangentCone : kernelCone A B ⟶ cotangentCone A B :=
  CochainComplex.mappingCone.mapFromZero (conormalKernelIota A B)
    (conormalToCotangentComplex A B)
    (conormalKernelIota_comp_conormalToCotangentComplex A B)

/-- **The cone of `d` has, in cohomological degree `-1`, the homology of the cone of
`Ker(d) ⟶ 0`.** This is
`CochainComplex.mappingCone.isIso_homologyMap_mapFromZero` applied to the factorisation of `d`
through its image; its two inputs are the vanishing of `H₁(Coker d)` and `H₂(Coker d)` of
Remark 09D5. -/
theorem isIso_homologyMap_kernelConeToCotangentCone :
    IsIso (HomologicalComplex.homologyMap (kernelConeToCotangentCone A B) (-1)) :=
  CochainComplex.mappingCone.isIso_homologyMap_mapFromZero
    (conormalKernelIota A B) (conormalToImage A B) (conormalImageIota A B)
    (conormalToImage_comp A B) (conormalKernelIota_comp_conormalToImage A B)
    (conormalImageIota_comp_conormalToCokernel A B)
    (shortExact_conormalKernelImage A B) (shortExact_conormalImageCokernel A B)
    (-1) (-2) (by norm_num)
    (isZero_conormalCokernelComplex_homology A B 1 one_pos)
    (isZero_conormalCokernelComplex_homology A B 2 (by norm_num))

end Stacks.Cotangent

end
