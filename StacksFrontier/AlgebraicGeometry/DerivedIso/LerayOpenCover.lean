module

public import StacksFrontier.AlgebraicGeometry.DerivedIso.Leray
public import StacksFrontier.AlgebraicGeometry.DerivedIso.LerayAffineOverBase
public import StacksFrontier.AlgebraicGeometry.DerivedIso.RelativeCechZeroOpenCover

/-!
# The relative Čech complex of an open cover with affine intersections computes `Rf_*ℱ`

Let `f : X ⟶ S` be a morphism of schemes, let `𝒰` be a finite open cover of `X` and let `ℱ` be a
quasi-coherent `𝒪_X`-module.  Suppose that for every finite intersection
`U_{i₀ … i_p} = U_{i₀} ∩ … ∩ U_{i_p}` both the inclusion `U_{i₀ … i_p} ⟶ X` and the composite
`U_{i₀ … i_p} ⟶ S` are affine morphisms.  Then the relative Čech complex of [Stacks, Tag 01XL]
computes the derived direct image:

`Č ⁼(𝒰, f, ℱ) ≅ Rf_*ℱ` in `D⁺(S)`,

naturally in `ℱ`.  The proof is the proof of [Stacks, Tag 01XL]: the terms of the absolute Čech
resolution `𝔠 ⁼(𝒰, ℱ)` of [Stacks, Tag 02FU] are right acyclic for `f_*` (each factor is
`j_* j^*ℱ` for an affine `j` with `j ≫ f` affine), so Leray's acyclicity lemma
([Stacks, Tag 015E]) identifies `f_* 𝔠 ⁼(𝒰, ℱ) = Č ⁼(𝒰, f, ℱ)` with `Rf_*ℱ`.

When `X` and `S` have affine diagonal and `𝒰` is affine the intersection hypothesis holds; it
also holds for the inverse image of such a cover along any base change `X' = S' ×_S X ⟶ X`,
whose members need not be affine.

## Main results

* `rightAcyclic_absoluteCechComplex_X`: the terms of the absolute Čech resolution are right
  acyclic for `f_*`.
* `relativeCechIsoDerivedPushforward`: **`Č ⁼(𝒰, f, ℱ) ≅ Rf_*ℱ` in `D⁺(S)`**.

## References

* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 02FU](https://stacks.math.columbia.edu/tag/02FU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.AlgebraicGeometry.RelativeCechOpenCover

open Stacks.AlgebraicGeometry.RelativeCech
open Stacks.AlgebraicGeometry.CechPushforwardComplex
open Stacks.AlgebraicGeometry.Tag01XLDerivedIso

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X S : Scheme.{u}}

/-- **The terms of the absolute Čech resolution of an open cover with affine intersections are
right acyclic for `f_*`.**  The degree `n` term is the product over the `(n + 1)`-tuples `i` of
`j_* j^*ℱ`, where `j` is the inclusion of the intersection `U_{i₀ … i_n}`; by hypothesis `j` and
`j ≫ f` are affine, so each factor is right acyclic. -/
theorem rightAcyclic_absoluteCechComplex_X (f : X ⟶ S) (𝒰 : X.OpenCover.{u}) [Finite 𝒰.I₀]
    (h𝒰 : ∀ (n : ℕ) (i : Fin (n + 1) → 𝒰.I₀),
      IsAffineHom (∏ᶜ fun a ↦ Over.mk (𝒰.f (i a))).hom ∧
        IsAffineHom ((∏ᶜ fun a ↦ Over.mk (𝒰.f (i a))).hom ≫ f))
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) (n : ℕ) :
    (Scheme.Modules.pushforward f).rightAcyclic
      (((CategoryTheory.cechComplexFunctor (fun i ↦ (Over.mk (𝒰.f i) : Over X))).obj
        ((relativeMonad X).flip.obj F.obj)).X n) := by
  have key : (Scheme.Modules.pushforward f).rightAcyclic
      (∏ᶜ (fun (i : Fin (n + 1) → 𝒰.I₀) ↦
        ((relativeMonad X).flip.obj F.obj).obj
          (op (∏ᶜ (fun a ↦ (Over.mk (𝒰.f (i a)) : Over X)))))) := by
    refine Stacks.RightAcyclicProduct.rightAcyclic_pi _ _ (fun i ↦ ?_)
    obtain ⟨h₁, h₂⟩ := h𝒰 n i
    have hpb : ((Scheme.Modules.pullback (∏ᶜ fun a ↦ Over.mk (𝒰.f (i a))).hom).obj
        F.obj).IsQuasicoherent :=
      Stacks.Modules.isQuasicoherent_pullback _ F.obj F.property
    exact Stacks.AlgebraicGeometry.RelativeCechAcyclic.rightAcyclic_pushforward_comp _ f _
  exact key

/-- Every term of the bounded below absolute Čech resolution, in every integral degree, is right
acyclic for `f_*`. -/
theorem rightAcyclic_absoluteCechComplexPlus_X (f : X ⟶ S) (𝒰 : X.OpenCover.{u})
    [Fintype 𝒰.I₀]
    (h𝒰 : ∀ (n : ℕ) (i : Fin (n + 1) → 𝒰.I₀),
      IsAffineHom (∏ᶜ fun a ↦ Over.mk (𝒰.f (i a))).hom ∧
        IsAffineHom ((∏ᶜ fun a ↦ Over.mk (𝒰.f (i a))).hom ≫ f))
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) (n : ℤ) :
    (Scheme.Modules.pushforward f).rightAcyclic
      (((absoluteCechComplexPlus 𝒰).obj F).obj.X n) := by
  rcases Int.lt_or_le n 0 with hn | hn
  · refine Stacks.RightAcyclicProduct.rightAcyclic_of_isZero _ ?_
    refine HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat n (fun m hm ↦ ?_)
    have h : (m : ℤ) = n := hm
    omega
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact Stacks.RightAcyclicProduct.rightAcyclic_of_iso _
      (HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat (i := m) rfl).symm
      (rightAcyclic_absoluteCechComplex_X f 𝒰 h𝒰 F m)

/-- **Leray's acyclicity lemma at the absolute Čech resolution** ([Stacks, Tag 015E]). -/
theorem isIso_rightDerivedFunctorPlusUnit_absoluteCechComplexPlus (f : X ⟶ S)
    (𝒰 : X.OpenCover.{u}) [Fintype 𝒰.I₀]
    (h𝒰 : ∀ (n : ℕ) (i : Fin (n + 1) → 𝒰.I₀),
      IsAffineHom (∏ᶜ fun a ↦ Over.mk (𝒰.f (i a))).hom ∧
        IsAffineHom ((∏ᶜ fun a ↦ Over.mk (𝒰.f (i a))).hom ≫ f))
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    IsIso ((Scheme.Modules.pushforward f).rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient X.Modules).obj ((absoluteCechComplexPlus 𝒰).obj F))) := by
  have h := CategoryTheory.Functor.isIso_totalRightDerivedUnit_app_of_rightAcyclic
    (Scheme.Modules.pushforward f) _ ((absoluteCechComplexPlus 𝒰).obj F).property
    (rightAcyclic_absoluteCechComplexPlus_X f 𝒰 h𝒰 F)
  have hd := (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc
    (Scheme.Modules.pushforward f).rightDerivedFunctorPlus
    (Scheme.Modules.pushforward f).rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso X.Modules) _
    (((Scheme.Modules.pushforward f).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh).totalRightDerivedUnit DerivedCategory.Plus.Qh
        (HomotopyCategory.Plus.quasiIso X.Modules))).1 inferInstance
  rw [← Functor.rightDerived_fac_app (Scheme.Modules.pushforward f).rightDerivedFunctorPlus
    (Scheme.Modules.pushforward f).rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso X.Modules)] at h
  have := hd
  rwa [isIso_comp_right_iff] at h

/-- The isomorphism of [Stacks, Tag 015E] at the absolute Čech resolution, as an isomorphism of
functors of the quasi-coherent module. -/
noncomputable def absoluteCechUnitIso (f : X ⟶ S) (𝒰 : X.OpenCover.{u}) [Fintype 𝒰.I₀]
    (h𝒰 : ∀ (n : ℕ) (i : Fin (n + 1) → 𝒰.I₀),
      IsAffineHom (∏ᶜ fun a ↦ Over.mk (𝒰.f (i a))).hom ∧
        IsAffineHom ((∏ᶜ fun a ↦ Over.mk (𝒰.f (i a))).hom ≫ f)) :
    absoluteCechComplexPlus 𝒰 ⋙ HomotopyCategory.Plus.quotient X.Modules ⋙
        (Scheme.Modules.pushforward f).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
      absoluteCechComplexPlus 𝒰 ⋙ HomotopyCategory.Plus.quotient X.Modules ⋙
        DerivedCategory.Plus.Qh ⋙ (Scheme.Modules.pushforward f).rightDerivedFunctorPlus :=
  NatIso.ofComponents
    (fun F ↦
      haveI := isIso_rightDerivedFunctorPlusUnit_absoluteCechComplexPlus f 𝒰 h𝒰 F
      asIso ((Scheme.Modules.pushforward f).rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.quotient X.Modules).obj ((absoluteCechComplexPlus 𝒰).obj F))))
    (fun {_ _} φ ↦ (Scheme.Modules.pushforward f).rightDerivedFunctorPlusUnith.naturality
      ((HomotopyCategory.Plus.quotient X.Modules).map ((absoluteCechComplexPlus 𝒰).map φ)))

/-- **`Č ⁼(𝒰, f, ℱ) ≅ Rf_*(𝔠 ⁼(𝒰, ℱ))` in `D⁺(S)`**, functorially in `ℱ`. -/
noncomputable def relativeCechComputesDerivedPushforward (f : X ⟶ S) (𝒰 : X.OpenCover.{u})
    [Fintype 𝒰.I₀]
    (h𝒰 : ∀ (n : ℕ) (i : Fin (n + 1) → 𝒰.I₀),
      IsAffineHom (∏ᶜ fun a ↦ Over.mk (𝒰.f (i a))).hom ∧
        IsAffineHom ((∏ᶜ fun a ↦ Over.mk (𝒰.f (i a))).hom ≫ f)) :
    relativeCechComplex f 𝒰 ⋙ HomotopyCategory.Plus.quotient S.Modules ⋙
        DerivedCategory.Plus.Qh ≅
      absoluteCechComplexPlus 𝒰 ⋙ HomotopyCategory.Plus.quotient X.Modules ⋙
        DerivedCategory.Plus.Qh ⋙ (Scheme.Modules.pushforward f).rightDerivedFunctorPlus :=
  (Functor.isoWhiskerRight (pushforwardAbsoluteCechComplexPlusIso f 𝒰)
      (HomotopyCategory.Plus.quotient S.Modules ⋙ DerivedCategory.Plus.Qh)).symm ≪≫
    (Functor.isoWhiskerLeft (absoluteCechComplexPlus 𝒰)
      (Functor.isoWhiskerRight
        (mapHomotopyCategoryPlusFactors (Scheme.Modules.pushforward f))
        DerivedCategory.Plus.Qh)).symm ≪≫
    absoluteCechUnitIso f 𝒰 h𝒰

/-- **The relative Čech complex of an open cover with affine intersections computes `Rf_*ℱ`.**
In `D⁺(S)`,

`Č ⁼(𝒰, f, ℱ) ≅ Rf_*ℱ`,

functorially in the quasi-coherent `𝒪_X`-module `ℱ`, for a finite open cover `𝒰` of `X` all of
whose finite intersections `U_{i₀ … i_p}` are affine over `X` and over `S`. -/
noncomputable def relativeCechIsoDerivedPushforward (f : X ⟶ S) (𝒰 : X.OpenCover.{u})
    [Fintype 𝒰.I₀]
    (h𝒰 : ∀ (n : ℕ) (i : Fin (n + 1) → 𝒰.I₀),
      IsAffineHom (∏ᶜ fun a ↦ Over.mk (𝒰.f (i a))).hom ∧
        IsAffineHom ((∏ᶜ fun a ↦ Over.mk (𝒰.f (i a))).hom ≫ f)) :
    relativeCechComplex f 𝒰 ⋙ HomotopyCategory.Plus.quotient S.Modules ⋙
        DerivedCategory.Plus.Qh ≅
      ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        DerivedCategory.Plus.singleFunctor X.Modules 0 ⋙
          (Scheme.Modules.pushforward f).rightDerivedFunctorPlus :=
  relativeCechComputesDerivedPushforward f 𝒰 h𝒰 ≪≫
    (Functor.isoWhiskerRight (LerayAffineOverBase.absoluteCechResolutionIso 𝒰)
      ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus)).symm

end Stacks.AlgebraicGeometry.RelativeCechOpenCover

end
