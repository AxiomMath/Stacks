module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.ConvolutionPerfect
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.KernelCategory
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardPerfect

/-!
# Perfectness of the convolution of perfect kernels over an arbitrary base

Let `S` be a scheme, let `f : X ⟶ S` and `h : Z ⟶ S` be morphisms and let `g : Y ⟶ S` be flat,
proper and of finite presentation. For perfect `K` on `X ×_S Y` and `M` on `Y ×_S Z`, the
convolution `R pr_{13,*}(L pr_{12}^*K ⊗^𝐋 L pr_{23}^*M)` is perfect on `X ×_S Z`. This is the input
`hconv` of `AlgebraicGeometry.FourierMukaiKernelObj.categoryOf`, i.e. the perfectness claim of
clause (3) of [Stacks, Tag 0G0F], which the source draws from [Stacks, Tag 0B91].

The two pullbacks are perfect by [Stacks, Tag 09UA], their derived tensor product by
[Stacks, Tag 09J5], and `pr_{13}` is a base change of `g`, hence flat, proper and of finite
presentation, so the perfectness half of [Stacks, Tag 0B91] (1) applies
(`AlgebraicGeometry.isPerfect_derivedPushforward_of_flat_of_isProper`).

## Main results

* `AlgebraicGeometry.isPerfect_fourierMukaiConvolution_triple` — the convolution of perfect
  kernels on `X ×_S Y` and `Y ×_S Z` is perfect, over any base, for a flat proper middle factor of
  finite presentation. (`AlgebraicGeometry.isPerfect_fourierMukaiConvolution` is the case
  `Z = X`.)
* `AlgebraicGeometry.FourierMukaiKernelObj.isPerfect_convolution` — the same in the shape of the
  input `hconv` of `AlgebraicGeometry.FourierMukaiKernelObj.categoryOf`.

## References

* [Stacks Project, Tag 0G0F](https://stacks.math.columbia.edu/tag/0G0F)
* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.PerfectComplexes (IsPerfect)

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

section Perfect

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)

/-- **The convolution of two perfect kernels is perfect over an arbitrary base**: for `g : Y ⟶ S`
flat, proper and of finite presentation and perfect `K` on `X ×_S Y` and `M` on `Y ×_S Z`, the
convolution `R pr_{13,*}(L pr_{12}^*K ⊗^𝐋 L pr_{23}^*M)` of [Stacks, Tag 0FYS] is perfect on
`X ×_S Z`. -/
theorem isPerfect_fourierMukaiConvolution_triple
    [Flat g] [IsProper g] [LocallyOfFinitePresentation g]
    {K : DerivedCategory (pullback f g).Modules}
    (hK : IsPerfect (X := (pullback f g).toRingedSpace) K)
    {M : DerivedCategory (pullback g h).Modules}
    (hM : IsPerfect (X := (pullback g h).toRingedSpace) M) :
    IsPerfect (X := (pullback f h).toRingedSpace) (fourierMukaiConvolution f g h K M) := by
  have i1 : Flat (fourierMukaiPr13 f g h) :=
    fourierMukaiPr13_of_isPullback f g h @Flat inferInstance
  have i2 : IsProper (fourierMukaiPr13 f g h) :=
    fourierMukaiPr13_of_isPullback f g h @IsProper inferInstance
  have i3 : LocallyOfFinitePresentation (fourierMukaiPr13 f g h) :=
    fourierMukaiPr13_of_isPullback f g h @LocallyOfFinitePresentation inferInstance
  have h12 : IsPerfect (X := (fourierMukaiTripleProduct f g h).toRingedSpace)
      ((dpull (fourierMukaiPr12 f g h)).obj K) :=
    RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ K hK
  have h23 : IsPerfect (X := (fourierMukaiTripleProduct f g h).toRingedSpace)
      ((dpull (fourierMukaiPr23 f g h)).obj M) :=
    RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ M hM
  have hT : IsPerfect (X := (fourierMukaiTripleProduct f g h).toRingedSpace)
      ((dtenR (fourierMukaiTripleProduct f g h) ((dpull (fourierMukaiPr23 f g h)).obj M)).obj
        ((dpull (fourierMukaiPr12 f g h)).obj K)) :=
    isPerfect_dtenR _ _ h12 h23
  exact isPerfect_derivedPushforward_of_flat_of_isProper (fourierMukaiPr13 f g h) _ hT

end Perfect

namespace FourierMukaiKernelObj

/-- **The input `hconv` of `AlgebraicGeometry.FourierMukaiKernelObj.categoryOf`**: the
convolution of two perfect kernels between proper smooth schemes over any base `S` is perfect,
which is the perfectness claim of clause (3) of [Stacks, Tag 0G0F]. -/
theorem isPerfect_convolution
    {S : Scheme.{u}} {X Y Z : FourierMukaiKernelObj S} (K : PerfectKernel X Y)
    (K' : PerfectKernel Y Z) :
    IsPerfect (X := (pullback X.f Z.f).toRingedSpace)
      (fourierMukaiConvolution X.f Y.f Z.f K.obj K'.obj) :=
  isPerfect_fourierMukaiConvolution_triple X.f Y.f Z.f K.property K'.property

end FourierMukaiKernelObj

end AlgebraicGeometry

end
