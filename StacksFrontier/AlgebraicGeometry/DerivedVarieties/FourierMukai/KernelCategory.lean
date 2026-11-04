module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.ConvolutionAssociativity
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.DiagonalKernelPerfect
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.DiagonalKernelUnit
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.PerfectPreservation
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
import StacksCore.Tactic.StacksAttribute

/-!
# The category of Fourier-Mukai kernels

Let `S` be a scheme. Section 0G0F of the source builds a category with

1. objects the proper smooth schemes over `S`;
2. morphisms from `X` to `Y` the isomorphism classes of objects of `D_perf(𝒪_{X ×_S Y})`;
3. composition of the class of `K` on `X ×_S Y` and the class of `K'` on `Y ×_S Z` the class of
   the convolution `R pr_{13,*}(L pr_{12}^*K ⊗^𝐋 L pr_{23}^*K')`, which is perfect;
4. identity of `X` the class of `Δ_{X/S,*}𝒪_X`, which is perfect.

This file assembles that category out of its four clauses.

## Main definitions

* `AlgebraicGeometry.FourierMukaiKernelObj` — clause (1), a proper smooth scheme over `S`.
* `AlgebraicGeometry.FourierMukaiKernelObj.PerfectKernel` — `D_perf(𝒪_{X ×_S Y})`.
* `AlgebraicGeometry.FourierMukaiKernelObj.Hom` — clause (2), the isomorphism classes of objects
  of `D_perf(𝒪_{X ×_S Y})`.
* `AlgebraicGeometry.FourierMukaiKernelObj.categoryOf` — the category, built from any proof that
  the convolution of two perfect kernels is perfect.

## Main results

* `AlgebraicGeometry.fourierMukaiConvolutionCongr` — convolution respects isomorphisms of
  kernels, so it descends to isomorphism classes.

## Implementation notes

*What is proved here.* Clauses (1), (2) and (4), the unit laws (which the source omits) and
associativity (the source's five-step chain, `AlgebraicGeometry.fourierMukaiConvolutionAssocIso`)
are all proved with no hypothesis beyond the source's. The perfectness claim of clause (3), that
`R pr_{13,*}(L pr_{12}^*K ⊗^𝐋 L pr_{23}^*K')` is perfect, is the binder `hconv` of
`AlgebraicGeometry.FourierMukaiKernelObj.categoryOf`; it is proved over an arbitrary base, from
[Stacks, Tag 0B91], as `AlgebraicGeometry.FourierMukaiKernelObj.isPerfect_convolution`
(`FourierMukai/ConvolutionPerfectGeneral.lean`), and the category of [Stacks, Tag 0G0F] is
`AlgebraicGeometry.FourierMukaiKernelObj.category` (`FourierMukai/KernelCategoryInstance.lean`),
where the tag is registered.

## References

* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 09RF](https://stacks.math.columbia.edu/tag/09RF)
* [Stacks Project, Tag 0G0F](https://stacks.math.columbia.edu/tag/0G0F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.PerfectComplexes (IsPerfect)

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

/-! ### Convolution on isomorphism classes -/

section Congr

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)

/-- **Convolution respects isomorphisms of kernels**: isomorphisms `K ≅ L` on `X ×_S Y` and
`K' ≅ L'` on `Y ×_S Z` induce an isomorphism `K' ∘ K ≅ L' ∘ L` of convolutions, each of the
three derived functors the convolution is built from being a functor. -/
def fourierMukaiConvolutionCongr {K L : DerivedCategory (pullback f g).Modules} (e : K ≅ L)
    {K' L' : DerivedCategory (pullback g h).Modules} (e' : K' ≅ L') :
    fourierMukaiConvolution f g h K K' ≅ fourierMukaiConvolution f g h L L' :=
  (dpush (fourierMukaiPr13 f g h)).mapIso
    (((derivedTensorProductFunctor _).mapIso
        ((dpull (fourierMukaiPr12 f g h)).mapIso e)).app
          ((dpull (fourierMukaiPr23 f g h)).obj K') ≪≫
      ((derivedTensorProductFunctor _).obj
        ((dpull (fourierMukaiPr12 f g h)).obj L)).mapIso
          ((dpull (fourierMukaiPr23 f g h)).mapIso e'))

/-- A perfect object has quasi-coherent cohomology sheaves. -/
theorem isQCohAll_of_isPerfect {W : Scheme.{u}} {K : DerivedCategory W.Modules}
    (hK : IsPerfect (X := W.toRingedSpace) K) : IsQCohAll K :=
  PerfectApproximation.isQuasicoherent_homology_of_isPerfect W K hK

end Congr

/-! ### The objects and the morphisms -/

/-- **Clause (1) of Section 0G0F**: an object of the category of Fourier-Mukai kernels over `S`
is a scheme `X` with a proper smooth morphism `X ⟶ S`. -/
structure FourierMukaiKernelObj (S : Scheme.{u}) where
  /-- The underlying scheme. -/
  X : Scheme.{u}
  /-- The structure morphism. -/
  f : X ⟶ S
  [smooth : Smooth f]
  [proper : IsProper f]

attribute [instance] FourierMukaiKernelObj.smooth FourierMukaiKernelObj.proper

namespace FourierMukaiKernelObj

variable {S : Scheme.{u}}

/-- `D_perf(𝒪_{X ×_S Y})`, the full subcategory of perfect objects of `D(𝒪_{X ×_S Y})`. -/
abbrev PerfectKernel (X Y : FourierMukaiKernelObj S) :=
  ObjectProperty.FullSubcategory
    (fun K : DerivedCategory (pullback X.f Y.f).Modules =>
      IsPerfect (X := (pullback X.f Y.f).toRingedSpace) K)

/-- **Clause (2) of Section 0G0F**: a morphism from `X` to `Y` is an isomorphism class of
objects of `D_perf(𝒪_{X ×_S Y})`. -/
abbrev Hom (X Y : FourierMukaiKernelObj S) :=
  Quotient (isIsomorphicSetoid (PerfectKernel X Y))

/-- The convolution of two perfect kernels, granted that it is perfect. -/
def convolve
    (hconv : ∀ {X Y Z : FourierMukaiKernelObj S} (K : PerfectKernel X Y) (K' : PerfectKernel Y Z),
      IsPerfect (X := (pullback X.f Z.f).toRingedSpace)
        (fourierMukaiConvolution X.f Y.f Z.f K.obj K'.obj))
    {X Y Z : FourierMukaiKernelObj S} (K : PerfectKernel X Y) (K' : PerfectKernel Y Z) :
    PerfectKernel X Z :=
  ⟨fourierMukaiConvolution X.f Y.f Z.f K.obj K'.obj, hconv K K'⟩

/-- **Clause (4) of Section 0G0F**: the identity of `X` is `Δ_{X/S,*}𝒪_X`, which is perfect
(`AlgebraicGeometry.isPerfect_diagonalKernel_ringedSpace`). -/
def diagonal (X : FourierMukaiKernelObj S) : PerfectKernel X X :=
  ⟨diagonalKernel X.f, isPerfect_diagonalKernel_ringedSpace X.f⟩

/-- An isomorphism of underlying kernels is an isomorphism in `D_perf`. -/
lemma isIsomorphic_mk {X Y : FourierMukaiKernelObj S} {K L : PerfectKernel X Y}
    (e : K.obj ≅ L.obj) : (isIsomorphicSetoid (PerfectKernel X Y)) K L :=
  ⟨ObjectProperty.isoMk _ e⟩

variable (hconv : ∀ {X Y Z : FourierMukaiKernelObj S} (K : PerfectKernel X Y)
  (K' : PerfectKernel Y Z), IsPerfect (X := (pullback X.f Z.f).toRingedSpace)
    (fourierMukaiConvolution X.f Y.f Z.f K.obj K'.obj))

/-- **Clause (3) of Section 0G0F**: composition is convolution, on isomorphism classes. -/
def comp {X Y Z : FourierMukaiKernelObj S} : Hom X Y → Hom Y Z → Hom X Z :=
  Quotient.lift₂ (fun K K' => ⟦convolve hconv K K'⟧) (fun _ _ _ _ ⟨e⟩ ⟨e'⟩ =>
    Quotient.sound (isIsomorphic_mk (fourierMukaiConvolutionCongr _ _ _
      ((ObjectProperty.ι _).mapIso e) ((ObjectProperty.ι _).mapIso e'))))

/-- **The category of Fourier-Mukai kernels**, granted that the convolution of two perfect
kernels is perfect: clauses (1)-(4) of Section 0G0F, with the unit laws of
`AlgebraicGeometry.diagonalKernelConvolutionIso` and
`AlgebraicGeometry.convolutionDiagonalKernelIso` and the associativity of
`AlgebraicGeometry.fourierMukaiConvolutionAssocIso`. -/
@[instance_reducible]
def categoryOf : Category (FourierMukaiKernelObj S) where
  Hom := Hom
  id X := ⟦diagonal X⟧
  comp := comp hconv
  id_comp {X Y} := by
    rintro ⟨K⟩
    exact Quotient.sound (isIsomorphic_mk (diagonalKernelConvolutionIso X.f Y.f K.obj))
  comp_id {X Y} := by
    rintro ⟨K⟩
    exact Quotient.sound (isIsomorphic_mk (convolutionDiagonalKernelIso X.f Y.f K.obj))
  assoc {X Y Z W} := by
    rintro ⟨K⟩ ⟨K'⟩ ⟨K''⟩
    exact Quotient.sound (isIsomorphic_mk (fourierMukaiConvolutionAssocIso
      (isQCohAll_of_isPerfect K.property) (isQCohAll_of_isPerfect K'.property)
      (isQCohAll_of_isPerfect K''.property)))

end FourierMukaiKernelObj

end AlgebraicGeometry

end
