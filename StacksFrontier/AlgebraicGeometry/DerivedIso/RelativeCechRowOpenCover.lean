module

public import StacksFrontier.AlgebraicGeometry.DerivedIso.RelativeCechZeroKernel
public import StacksFrontier.AlgebraicGeometry.DerivedIso.RelativeCechZeroOpenCover

/-!
# The relative Čech row of an arbitrary finite open cover is left exact

Let `f : X ⟶ S` be a morphism of schemes, let `𝒰` be a finite open cover of `X` — not assumed
affine — and let `ℱ` be a quasi-coherent `𝒪_X`-module.  The relative Čech complex
`Č ⁼(𝒰, f, ℱ)` of [Stacks, Tag 01XL] is concentrated in non-negative degrees and its degree zero
cohomology is `f_* ℱ`, so

`0 ⟶ f_* ℱ ⟶ Č ⁰(𝒰, f, ℱ) ⟶ Č ¹(𝒰, f, ℱ)`

is exact: the augmentation is a kernel of the first differential.

This is the bottom row of the comparison diagram of [Stacks, Tag 0GPA] for the second projection
`X ×_R Y ⟶ Y` and the open cover of `X ×_R Y` induced by an affine open cover of `X`, whose
members are affine only when `Y` is — which is why the cover is not assumed affine here.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeCechOpenCover.relativeCechComplexZ`: the relative Čech
  complex of a finite open cover as a family of `ℤ`-indexed complexes, the bound forgotten.
* `Stacks.AlgebraicGeometry.RelativeCechOpenCover.relativeCechAugZero`: the augmentation
  `f_* ℱ ⟶ Č ⁰(𝒰, f, ℱ)`, naturally in `ℱ`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeCechOpenCover.isLimitKernelFork_relativeCechAugZero`: **the
  relative Čech row of a finite open cover is left exact**, that is the augmentation
  `f_* ℱ ⟶ Č ⁰(𝒰, f, ℱ)` is a kernel of the first differential `Č ⁰(𝒰, f, ℱ) ⟶ Č ¹(𝒰, f, ℱ)`.
* `Stacks.AlgebraicGeometry.RelativeCechOpenCover.relativeCechAugZero_comp_dNatTrans`: that row
  is a complex, naturally in the quasi-coherent module.
* `Stacks.AlgebraicGeometry.RelativeCechOpenCover.mono_relativeCechAugZero_app`: the
  augmentation is a monomorphism.

## References

* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 0GPA](https://stacks.math.columbia.edu/tag/0GPA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.RelativeCechOpenCover

open Stacks.AlgebraicGeometry.RelativeCech
open Stacks.AlgebraicGeometry.CechPushforwardComplex

variable {X S : Scheme.{u}} (f : X ⟶ S) (𝒰 : X.OpenCover.{u}) [Fintype 𝒰.I₀]

/-- The relative Čech complex of a finite open cover as a family of `ℤ`-indexed complexes of
`𝒪_S`-modules, the bound being forgotten. -/
def relativeCechComplexZ :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      CochainComplex S.Modules ℤ :=
  relativeCechComplex f 𝒰 ⋙ CochainComplex.Plus.ι S.Modules

/-- No differential of the relative Čech complex enters degree zero:  the complex is the
extension of an `ℕ`-indexed complex, so its term in the preceding degree is zero. -/
theorem relativeCechComplexZ_d_prev_zero
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    ((relativeCechComplexZ f 𝒰).obj F).d ((ComplexShape.up ℤ).prev 0) 0 = 0 := by
  change (((CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (𝒰.f i))).obj
      ((relativeCechPresheaf f).obj F)).extend ComplexShape.embeddingUpNat).d
      ((ComplexShape.up ℤ).prev 0) 0 = 0
  refine (_root_.HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat
    ((ComplexShape.up ℤ).prev 0) (fun i ↦ ?_)).eq_zero_of_src _
  have h : (ComplexShape.up ℤ).prev 0 = -1 := by simp
  simp only [ComplexShape.embeddingUpNat_f, h]
  omega

/-- `H⁰(Č ⁼(𝒰, f, ℱ)) ≅ f_* ℱ`, read on the `ℤ`-indexed relative Čech complex. -/
def relativeCechHomologyZeroIsoZ :
    ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        Scheme.Modules.pushforward f ≅
      relativeCechComplexZ f 𝒰 ⋙
        _root_.HomologicalComplex.homologyFunctor S.Modules (ComplexShape.up ℤ) 0 :=
  (relativeCechHomologyZeroIso f 𝒰).symm

/-- **The augmentation `f_* ℱ ⟶ Č ⁰(𝒰, f, ℱ)` of the relative Čech complex of
[Stacks, Tag 01XL]** for a finite open cover, as a natural transformation in the quasi-coherent
`𝒪_X`-module `ℱ`:  the degree zero cohomology of that complex is `f_* ℱ`, and no differential
enters degree zero. -/
def relativeCechAugZero :
    ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        Scheme.Modules.pushforward f ⟶
      relativeCechComplexZ f 𝒰 ⋙
        _root_.HomologicalComplex.eval S.Modules (ComplexShape.up ℤ) 0 :=
  Stacks.HomologicalComplex.homologyAug (relativeCechHomologyZeroIsoZ f 𝒰)
    (relativeCechComplexZ_d_prev_zero f 𝒰)

/-- The augmentation followed by the first differential of the relative Čech complex is zero, at
a fixed quasi-coherent `𝒪_X`-module. -/
theorem relativeCechAugZero_app_comp_d
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (relativeCechAugZero f 𝒰).app F ≫ ((relativeCechComplexZ f 𝒰).obj F).d 0 1 = 0 :=
  Stacks.HomologicalComplex.homologyAug_app_comp_d _ _ 1 F

/-- **`f_* ℱ ⟶ Č ⁰(𝒰, f, ℱ) ⟶ Č ¹(𝒰, f, ℱ)` is a complex**, naturally in the quasi-coherent
`𝒪_X`-module `ℱ`. -/
theorem relativeCechAugZero_comp_dNatTrans :
    relativeCechAugZero f 𝒰 ≫ Functor.whiskerLeft (relativeCechComplexZ f 𝒰)
        (_root_.HomologicalComplex.dNatTrans S.Modules (ComplexShape.up ℤ) 0 1) = 0 :=
  Stacks.HomologicalComplex.homologyAug_comp_dNatTrans _ _ 1

/-- **The relative Čech row of a finite open cover is left exact**:  the augmentation
`f_* ℱ ⟶ Č ⁰(𝒰, f, ℱ)` is a kernel of the first differential `Č ⁰(𝒰, f, ℱ) ⟶ Č ¹(𝒰, f, ℱ)`.
This is the left exactness of the bottom row of the comparison diagram of [Stacks, Tag 0GPA],
whose cover is not affine. -/
def isLimitKernelFork_relativeCechAugZero
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    IsLimit (KernelFork.ofι ((relativeCechAugZero f 𝒰).app F)
      (relativeCechAugZero_app_comp_d f 𝒰 F)) :=
  Stacks.HomologicalComplex.isLimitKernelFork_homologyAug _ _ (by simp) F

/-- **The augmentation `f_* ℱ ⟶ Č ⁰(𝒰, f, ℱ)` is a monomorphism.** -/
theorem mono_relativeCechAugZero_app
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    Mono ((relativeCechAugZero f 𝒰).app F) :=
  mono_of_isLimit_fork (isLimitKernelFork_relativeCechAugZero f 𝒰 F)

end Stacks.AlgebraicGeometry.RelativeCechOpenCover

end
