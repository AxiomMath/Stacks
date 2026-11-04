module

public import StacksFrontier.AlgebraicGeometry.CechSiteChange.Resolution
public import StacksFrontier.AlgebraicGeometry.DerivedIso.Transport

/-!
# The degree zero cohomology of the relative Čech complex is the direct image

Let `f : X ⟶ S` be a morphism of schemes, let `T` be a finite affine open cover of `X`, and let
`ℱ` be a quasi-coherent `𝒪_X`-module.  The relative Čech complex `Č ⁼(𝒰, f, ℱ)` is concentrated
in non-negative degrees, so its degree zero cohomology is the kernel of

`⊕_{i₀} f_{i₀ *} ℱ|_{U_{i₀}} ⟶ ⊕_{i₀ i₁} f_{i₀ i₁ *} ℱ|_{U_{i₀ i₁}}`,

and that kernel is `f_* ℱ`.  The proof given here deduces this from the *absolute* Čech
resolution: `f_*` applied termwise to `𝔠 ⁼(𝒰, ℱ)` is `Č ⁼(𝒰, f, ℱ)`, the augmentation
`ℱ[0] ⟶ 𝔠 ⁼(𝒰, ℱ)` is a quasi-isomorphism, and `f_*` — being a right adjoint, hence left exact —
commutes with the degree zero cohomology of a complex concentrated in non-negative degrees.

## Main definitions

* `Stacks.HomologicalComplex.mapHomologyNatIso`: a functor preserving finite limits commutes with
  the homology in a degree into which the differential vanishes.
* `Stacks.AlgebraicGeometry.Tag01XLDerivedIso.absoluteCechHomologyZeroIso`:
  **`H⁰(𝔠 ⁼(𝒰, ℱ)) ≅ ℱ`**, naturally in `ℱ`.
* `Stacks.AlgebraicGeometry.Tag01XLDerivedIso.relativeCechHomologyZeroIso`:
  **`H⁰(Č ⁼(𝒰, f, ℱ)) ≅ f_* ℱ`**, as an isomorphism of functors of the quasi-coherent module.
* `Stacks.AlgebraicGeometry.Tag01XLDerivedIso.relativeCechHomologyZero`: the same isomorphism at
  a fixed quasi-coherent module.

## Main results

* `Stacks.ShortComplex.preservesLeftHomologyOf_of_f_eq_zero`: a functor preserving finite limits
  preserves the left homology of a short complex whose first map is zero.

## Implementation notes

The homology of a complex in a fixed degree is by definition the homology of the associated short
complex, and applying a functor termwise to a complex produces, in each degree, the image of that
short complex; both identifications hold by `rfl`, so Mathlib's `ShortComplex.mapHomologyIso` and
its naturality transfer directly to complexes.

No hypothesis is placed on `f`, on `T` or on the schemes: unlike the derived statement, the degree
zero assertion needs neither affine diagonals nor acyclicity.

## References

* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 02FU](https://stacks.math.columbia.edu/tag/02FU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

/-! ### A left exact functor commutes with homology where the differential vanishes -/

namespace Stacks

section LeftExact

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  (G : A ⥤ B) [G.Additive] [PreservesFiniteLimits G]

/-- **A functor preserving finite limits preserves the left homology of a short complex whose
first map is zero.** -/
theorem ShortComplex.preservesLeftHomologyOf_of_f_eq_zero (S : CategoryTheory.ShortComplex A)
    (hf : S.f = 0) : G.PreservesLeftHomologyOf S := by
  have inst : (CategoryTheory.ShortComplex.LeftHomologyData.ofIsLimitKernelFork S hf _
      (kernelIsKernel S.g)).IsPreservedBy G :=
    { g := inferInstance
      f' := Limits.preservesCokernel_zero' G _
        (CategoryTheory.ShortComplex.LeftHomologyData.ofIsLimitKernelFork_f' S hf _
          (kernelIsKernel S.g)) }
  exact Functor.PreservesLeftHomologyOf.mk' G
    (CategoryTheory.ShortComplex.LeftHomologyData.ofIsLimitKernelFork S hf _ (kernelIsKernel S.g))

/-- **A functor preserving finite limits commutes with the homology in a degree into which the
differential vanishes.**  For a family `Φ` of complexes whose short complex in degree `i` has
vanishing first map, `H^i(G ∘ Φ) ≅ G(H^i(Φ))`, naturally in the parameter. -/
noncomputable def HomologicalComplex.mapHomologyNatIso {𝒞 : Type*} [Category* 𝒞] {ι : Type*}
    {c : ComplexShape ι} (Φ : 𝒞 ⥤ _root_.HomologicalComplex A c) (i : ι)
    (hΦ : ∀ Z, ((Φ.obj Z).sc i).f = 0) :
    Φ ⋙ G.mapHomologicalComplex c ⋙
        _root_.HomologicalComplex.homologyFunctor B c i ≅
      Φ ⋙ _root_.HomologicalComplex.homologyFunctor A c i ⋙ G :=
  haveI : ∀ Z, G.PreservesLeftHomologyOf ((Φ.obj Z).sc i) :=
    fun Z ↦ ShortComplex.preservesLeftHomologyOf_of_f_eq_zero G _ (hΦ Z)
  NatIso.ofComponents (fun Z ↦ ((Φ.obj Z).sc i).mapHomologyIso G)
    (fun ψ ↦ CategoryTheory.ShortComplex.mapHomologyIso_hom_naturality
      ((_root_.HomologicalComplex.shortComplexFunctor A c i).map (Φ.map ψ)) G)

end LeftExact

end Stacks

namespace Stacks.AlgebraicGeometry.Tag01XLDerivedIso

open Stacks.AlgebraicGeometry.RelativeCech
open Stacks.AlgebraicGeometry.RelativeCechComplex
open Stacks.AlgebraicGeometry.CechPushforwardComplex
open Stacks.CechSiteChange

variable {X S : Scheme.{u}}

/-! ### The degree zero cohomology of the absolute Čech resolution -/

/-- The absolute Čech resolution vanishes in the degree from which the differential into degree
zero comes, because that degree is negative and the resolution is the extension of an
`ℕ`-indexed complex. -/
theorem sc_zero_f_eq_zero_absoluteCechComplex (T : X.AffineOpenCover.{u, u})
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    ((((absoluteCechPresheaf X ⋙
          CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (T.f i))) ⋙
        ComplexShape.embeddingUpNat.extendFunctor X.Modules).obj F).sc 0).f = 0 := by
  refine (HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat
    ((ComplexShape.up ℤ).prev 0) (fun i ↦ ?_)).eq_zero_of_src _
  have h : (ComplexShape.up ℤ).prev 0 = -1 := by simp
  simp only [ComplexShape.embeddingUpNat_f, h]
  omega

/-- **The augmentation of the absolute Čech resolution is an isomorphism on degree zero
cohomology**, naturally in the quasi-coherent module:  it is a quasi-isomorphism
([Stacks, Tag 02FU]). -/
noncomputable def absoluteCechAugHomologyIso (T : X.AffineOpenCover.{u, u}) :
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0) ⋙
        HomologicalComplex.homologyFunctor X.Modules (ComplexShape.up ℤ) 0 ≅
      ((absoluteCechPresheaf X ⋙
            CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (T.f i))) ⋙
          ComplexShape.embeddingUpNat.extendFunctor X.Modules) ⋙
        HomologicalComplex.homologyFunctor X.Modules (ComplexShape.up ℤ) 0 :=
  haveI h : ∀ F, IsIso ((Functor.whiskerRight (absoluteCechAugZ X T)
      (HomologicalComplex.homologyFunctor X.Modules (ComplexShape.up ℤ) 0)).app F) := by
    intro F
    have hq := quasiIso_absoluteCechAugZ_app X T F
    have : QuasiIsoAt ((absoluteCechAugZ X T).app F) 0 := inferInstance
    rw [quasiIsoAt_iff_isIso_homologyMap] at this
    exact this
  haveI : IsIso (Functor.whiskerRight (absoluteCechAugZ X T)
      (HomologicalComplex.homologyFunctor X.Modules (ComplexShape.up ℤ) 0)) :=
    NatIso.isIso_of_isIso_app _
  asIso (Functor.whiskerRight (absoluteCechAugZ X T)
    (HomologicalComplex.homologyFunctor X.Modules (ComplexShape.up ℤ) 0))

/-- **`H⁰(𝔠 ⁼(𝒰, ℱ)) ≅ ℱ`**, naturally in the quasi-coherent `𝒪_X`-module `ℱ`:  the degree zero
cohomology of the absolute Čech resolution is the module itself ([Stacks, Tag 02FU]). -/
noncomputable def absoluteCechHomologyZeroIso (T : X.AffineOpenCover.{u, u}) [Fintype T.I₀] :
    (absoluteCechComplexPlus T ⋙ CochainComplex.Plus.ι X.Modules) ⋙
        HomologicalComplex.homologyFunctor X.Modules (ComplexShape.up ℤ) 0 ≅
      ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) :=
  (absoluteCechAugHomologyIso T).symm ≪≫
    Functor.isoWhiskerLeft (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf))
      (HomologicalComplex.homologyFunctorSingleIso X.Modules (ComplexShape.up ℤ) 0) ≪≫
    Functor.rightUnitor _

/-! ### The degree zero cohomology of the relative Čech complex -/

/-- **`H⁰(Č ⁼(𝒰, f, ℱ)) ≅ f_* ℱ`**, as an isomorphism of functors of the quasi-coherent
`𝒪_X`-module `ℱ`:  the degree zero cohomology of the relative Čech complex of [Stacks, Tag 01XL]
is the (underived) direct image. -/
noncomputable def relativeCechHomologyZeroIso (f : X ⟶ S) (T : X.AffineOpenCover.{u, u})
    [Fintype T.I₀] :
    relativeCechComplex f T ⋙ CochainComplex.Plus.ι S.Modules ⋙
        HomologicalComplex.homologyFunctor S.Modules (ComplexShape.up ℤ) 0 ≅
      ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        Scheme.Modules.pushforward f :=
  (Functor.isoWhiskerRight (pushforwardAbsoluteCechComplexPlusIso f T)
      (CochainComplex.Plus.ι S.Modules ⋙
        HomologicalComplex.homologyFunctor S.Modules (ComplexShape.up ℤ) 0)).symm ≪≫
    Stacks.HomologicalComplex.mapHomologyNatIso (Scheme.Modules.pushforward f)
      (absoluteCechComplexPlus T ⋙ CochainComplex.Plus.ι X.Modules) 0
      (sc_zero_f_eq_zero_absoluteCechComplex T) ≪≫
    Functor.isoWhiskerRight (absoluteCechHomologyZeroIso T) (Scheme.Modules.pushforward f)

/-- **`H⁰(Č ⁼(𝒰, f, ℱ)) ≅ f_* ℱ`** at a fixed quasi-coherent `𝒪_X`-module. -/
noncomputable def relativeCechHomologyZero (f : X ⟶ S) (T : X.AffineOpenCover.{u, u})
    [Fintype T.I₀] (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    ((relativeCechComplex f T).obj F).obj.homology 0 ≅
      (Scheme.Modules.pushforward f).obj F.obj :=
  (relativeCechHomologyZeroIso f T).app F

end Stacks.AlgebraicGeometry.Tag01XLDerivedIso

end
