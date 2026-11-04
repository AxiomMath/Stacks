module

public import StacksFrontier.AlgebraicGeometry.DerivedIso.RelativeCechZero

/-!
# The relative Čech complex of an arbitrary finite open cover

`Stacks.AlgebraicGeometry.RelativeCechComplex.relativeCechComplex` and
`Stacks.AlgebraicGeometry.Tag01XLDerivedIso.relativeCechHomologyZeroIso` are stated for a finite
*affine* open cover.  Affineness of the members of the cover plays no role in either: the Čech
complex of [Stacks, Tag 01XL] is formed from the family `Over.mk (𝒰.f i)` in `Over X`, and
[Stacks, Tag 02FU] — that the resulting complex is a resolution — needs only that the open ranges
of the `𝒰.f i` cover `X`.

This file carries the construction and the degree zero computation out for an arbitrary finite
open cover `𝒰` of `X`:

`H⁰(Č ⁼(𝒰, f, ℱ)) ≅ f_* ℱ`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeCechOpenCover.relativeCechComplex`: the bounded below
  relative Čech complex of a finite open cover.
* `Stacks.AlgebraicGeometry.RelativeCechOpenCover.absoluteCechComplexPlus`: the bounded below
  absolute Čech resolution of a finite open cover.
* `Stacks.AlgebraicGeometry.RelativeCechOpenCover.absoluteCechAugZ`: the augmentation
  `ℱ[0] ⟶ 𝔠 ⁼(𝒰, ℱ)` of `ℤ`-indexed complexes.

## Main results

* `Stacks.AlgebraicGeometry.RelativeCechOpenCover.quasiIso_absoluteCechAugZ_app`:
  **[Stacks, Tag 02FU] for an arbitrary open cover**: the augmentation of the absolute Čech
  resolution is a quasi-isomorphism.
* `Stacks.AlgebraicGeometry.RelativeCechOpenCover.pushforwardAbsoluteCechComplexPlusIso`:
  **`f_* 𝔠 ⁼(𝒰, ℱ) ≅ Č ⁼(𝒰, f, ℱ)`** for an arbitrary finite open cover.
* `Stacks.AlgebraicGeometry.RelativeCechOpenCover.relativeCechHomologyZeroIso`:
  **`H⁰(Č ⁼(𝒰, f, ℱ)) ≅ f_* ℱ`** for an arbitrary finite open cover, naturally in the
  quasi-coherent `𝒪_X`-module `ℱ`.

## References

* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
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
open Stacks.CechSiteChange

variable {X S : Scheme.{u}}

/-! ### The Čech complex of an open cover over the site of open sets -/

/-- **The Čech complex of [Stacks, Tag 01XL] for an open cover lives over the site of open
sets.**  For an open cover `𝒰` of `X`, the Čech complex over `Over X` of the family
`Over.mk (𝒰.f i)` is the Čech complex over `X.Opens` of the family of the open ranges of the
`𝒰.f i`, with coefficients restricted along `opensOver X`, naturally in the coefficient
presheaf. -/
noncomputable def cechComplexFunctorOpenCoverIso {A : Type*} [Category* A] [HasProducts.{u} A]
    [Preadditive A] (X : Scheme.{u}) (𝒰 : X.OpenCover.{u}) :
    cechComplexFunctor (A := A) (fun i ↦ Over.mk (𝒰.f i)) ≅
      (Functor.whiskeringLeft (X.Opens)ᵒᵖ (Over X)ᵒᵖ A).obj (opensOver X).op ⋙
        cechComplexFunctor (A := A) (fun i ↦ (𝒰.f i).opensRange) :=
  cechComplexFunctorIsoOfFamilyIso (A := A) (fun i ↦ overMkIsoOpensOver X (𝒰.f i)) ≪≫
    cechComplexFunctorSiteIso (A := A) (opensOver X) (fun i ↦ (𝒰.f i).opensRange)

/-- **The absolute Čech complex of [Stacks, Tag 01XL] for an open cover is a Čech complex over
the site of open sets.**  The family is the family of open ranges of the cover and the
coefficients are `Stacks.CechSiteChange.absoluteCechOpensPresheaf X`. -/
noncomputable def absoluteCechComplexOpensIso (X : Scheme.{u}) (𝒰 : X.OpenCover.{u}) :
    absoluteCechPresheaf X ⋙
        CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (𝒰.f i)) ≅
      absoluteCechOpensPresheaf X ⋙
        CategoryTheory.cechComplexFunctor (fun i ↦ (𝒰.f i).opensRange) :=
  Functor.isoWhiskerLeft (absoluteCechPresheaf X)
    (cechComplexFunctorOpenCoverIso (A := X.Modules) X 𝒰)

/-- **The absolute Čech complex of [Stacks, Tag 01XL] for an open cover is the Čech complex of
[Stacks, Tag 02FU]** for the family of open ranges of the cover, naturally in the quasi-coherent
module. -/
noncomputable def absoluteCechComplexCoveringIso (X : Scheme.{u}) (𝒰 : X.OpenCover.{u}) :
    absoluteCechPresheaf X ⋙
        CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (𝒰.f i)) ≅
      ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        coveringComplexOpens X (fun i ↦ (𝒰.f i).opensRange) :=
  absoluteCechComplexOpensIso X 𝒰 ≪≫
    Functor.isoWhiskerRight (absoluteCechOpensPresheafIso X)
      (CategoryTheory.cechComplexFunctor (fun i ↦ (𝒰.f i).opensRange))

/-! ### The augmentation of the absolute Čech resolution -/

/-- **The augmentation `ℱ ⟶ 𝔠 ⁼(𝒰, ℱ)` of the absolute Čech resolution of [Stacks, Tag 01XL]**
for an open cover, as an `ℕ`-indexed natural transformation. -/
noncomputable def absoluteCechAug (X : Scheme.{u}) (𝒰 : X.OpenCover.{u}) :
    ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        HomologicalComplex.single X.Modules (ComplexShape.up ℕ) 0 ⟶
      absoluteCechPresheaf X ⋙
        CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (𝒰.f i)) :=
  Functor.whiskerLeft (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf))
      (augOpens X (fun i ↦ (𝒰.f i).opensRange)) ≫
    (absoluteCechComplexCoveringIso X 𝒰).inv

/-- The components of `absoluteCechAug`. -/
theorem absoluteCechAug_app (X : Scheme.{u}) (𝒰 : X.OpenCover.{u})
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (absoluteCechAug X 𝒰).app F =
      (augOpens X (fun i ↦ (𝒰.f i).opensRange)).app F.obj ≫
        (absoluteCechComplexCoveringIso X 𝒰).inv.app F :=
  rfl

/-- **[Stacks, Tag 02FU] in the site of [Stacks, Tag 01XL], for an arbitrary open cover**: the
augmentation of the absolute Čech resolution is a quasi-isomorphism. -/
theorem quasiIso_absoluteCechAug_app (X : Scheme.{u}) (𝒰 : X.OpenCover.{u})
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    QuasiIso ((absoluteCechAug X 𝒰).app F) := by
  have hq := quasiIso_augOpens_app X (fun i ↦ (𝒰.f i).opensRange) 𝒰.iSup_opensRange F.obj
  rw [absoluteCechAug_app X 𝒰 F]
  infer_instance

/-- The augmentation extended along `ComplexShape.embeddingUpNat`. -/
noncomputable def absoluteCechAugExtend (X : Scheme.{u}) (𝒰 : X.OpenCover.{u}) :
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        HomologicalComplex.single X.Modules (ComplexShape.up ℕ) 0) ⋙
        ComplexShape.embeddingUpNat.extendFunctor X.Modules ⟶
      (absoluteCechPresheaf X ⋙
          CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (𝒰.f i))) ⋙
        ComplexShape.embeddingUpNat.extendFunctor X.Modules :=
  Functor.whiskerRight (absoluteCechAug X 𝒰) (ComplexShape.embeddingUpNat.extendFunctor X.Modules)

/-- The augmentation extended along `ComplexShape.embeddingUpNat` is a quasi-isomorphism. -/
theorem quasiIso_absoluteCechAugExtend_app (X : Scheme.{u}) (𝒰 : X.OpenCover.{u})
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    QuasiIso ((absoluteCechAugExtend X 𝒰).app F) := by
  have hq := quasiIso_absoluteCechAug_app X 𝒰 F
  exact inferInstanceAs (QuasiIso (HomologicalComplex.extendMap ((absoluteCechAug X 𝒰).app F)
    ComplexShape.embeddingUpNat))

/-- **The augmentation `ℱ[0] ⟶ 𝔠 ⁼(𝒰, ℱ)` of [Stacks, Tag 01XL] for an open cover, as a natural
transformation of `ℤ`-indexed complexes of `𝒪_X`-modules.** -/
noncomputable def absoluteCechAugZ (X : Scheme.{u}) (𝒰 : X.OpenCover.{u}) :
    ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0 ⟶
      (absoluteCechPresheaf X ⋙
          CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (𝒰.f i))) ⋙
        ComplexShape.embeddingUpNat.extendFunctor X.Modules :=
  (Functor.isoWhiskerLeft (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf))
      (singleExtendIso X)).inv ≫ absoluteCechAugExtend X 𝒰

/-- The components of `absoluteCechAugZ`. -/
theorem absoluteCechAugZ_app (X : Scheme.{u}) (𝒰 : X.OpenCover.{u})
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (absoluteCechAugZ X 𝒰).app F =
      ((singleExtendIso X).app F.obj).inv ≫ (absoluteCechAugExtend X 𝒰).app F :=
  rfl

/-- **[Stacks, Tag 02FU] for the absolute Čech resolution of an arbitrary open cover**: the
augmentation `ℱ[0] ⟶ 𝔠 ⁼(𝒰, ℱ)` of `ℤ`-indexed complexes is a quasi-isomorphism. -/
theorem quasiIso_absoluteCechAugZ_app (X : Scheme.{u}) (𝒰 : X.OpenCover.{u})
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    QuasiIso ((absoluteCechAugZ X 𝒰).app F) := by
  have hq := quasiIso_absoluteCechAugExtend_app X 𝒰 F
  rw [absoluteCechAugZ_app X 𝒰 F]
  infer_instance

/-! ### The bounded below complexes -/

/-- **The absolute Čech resolution of a finite open cover, as a bounded below complex of
`𝒪_X`-modules**:  the `ℕ`-indexed Čech complex extended along `ComplexShape.embeddingUpNat` and
bounded below at `0`. -/
noncomputable def absoluteCechComplexPlus (𝒰 : X.OpenCover.{u}) [Fintype 𝒰.I₀] :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      CochainComplex.Plus X.Modules :=
  ObjectProperty.lift _
    (absoluteCechPresheaf X ⋙
      CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (𝒰.f i)) ⋙
      ComplexShape.embeddingUpNat.extendFunctor X.Modules)
    (fun F ↦ ⟨0, by
      change CochainComplex.IsStrictlyGE
        (((CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (𝒰.f i))).obj
          ((absoluteCechPresheaf X).obj F)).extend ComplexShape.embeddingUpNat) 0
      infer_instance⟩)

/-- **The bounded below relative Čech complex of [Stacks, Tag 01XL] of a finite open cover.**  The
alternating Čech complex, for the family `Over.mk (𝒰.f i)` in `Over X`, of the coefficient
presheaf of `f`, extended from `ℕ`-indexing to `ℤ`-indexing and regarded as a bounded below
complex. -/
noncomputable def relativeCechComplex (f : X ⟶ S) (𝒰 : X.OpenCover.{u}) [Fintype 𝒰.I₀] :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      CochainComplex.Plus S.Modules :=
  ObjectProperty.lift _
    (relativeCechPresheaf f ⋙
      CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (𝒰.f i)) ⋙
      ComplexShape.embeddingUpNat.extendFunctor S.Modules)
    (fun F ↦ ⟨0, by
      change CochainComplex.IsStrictlyGE
        (((CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (𝒰.f i))).obj
          ((relativeCechPresheaf f).obj F)).extend ComplexShape.embeddingUpNat) 0
      infer_instance⟩)

/-- The underlying `ℤ`-indexed complex of the relative Čech complex is the extension of
Mathlib's `ℕ`-indexed Čech complex along `ComplexShape.embeddingUpNat`. -/
theorem relativeCechComplex_obj_obj (f : X ⟶ S) (𝒰 : X.OpenCover.{u}) [Fintype 𝒰.I₀]
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    ((relativeCechComplex f 𝒰).obj F).obj =
      ((CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (𝒰.f i))).obj
        ((relativeCechPresheaf f).obj F)).extend ComplexShape.embeddingUpNat :=
  rfl

/-- The index set of the open cover underlying an affine open cover is the index set of that
affine open cover. -/
instance fintype_openCover_I₀ (T : X.AffineOpenCover.{u, u}) [Fintype T.I₀] :
    Fintype T.openCover.I₀ :=
  inferInstanceAs (Fintype T.I₀)

/-- **The relative Čech complex of a finite open cover is a generalisation of the one of a finite
affine open cover**:  at the open cover underlying an affine open cover the two agree. -/
theorem relativeCechComplex_openCover (f : X ⟶ S) (T : X.AffineOpenCover.{u, u})
    [Fintype T.I₀] :
    relativeCechComplex f T.openCover =
      Stacks.AlgebraicGeometry.RelativeCechComplex.relativeCechComplex f T :=
  rfl

/-- **The absolute Čech resolution of a finite open cover is a generalisation of the one of a
finite affine open cover**:  at the open cover underlying an affine open cover the two agree. -/
theorem absoluteCechComplexPlus_openCover (T : X.AffineOpenCover.{u, u}) [Fintype T.I₀] :
    absoluteCechComplexPlus T.openCover = Tag01XLDerivedIso.absoluteCechComplexPlus T :=
  rfl

/-! ### The direct image of the absolute Čech resolution -/

/-- **`f_* 𝔠 ⁼(𝒰, ℱ) ≅ Č ⁼(𝒰, f, ℱ)`** for an open cover:  applying `f_*` termwise to the
absolute Čech complex of the family `Over.mk (𝒰.f i)` is the relative Čech complex of
[Stacks, Tag 01XL], naturally in the quasi-coherent module. -/
noncomputable def pushforwardAbsoluteCechComplexIso (f : X ⟶ S) (𝒰 : X.OpenCover.{u}) :
    absoluteCechPresheaf X ⋙ CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (𝒰.f i)) ⋙
        (Scheme.Modules.pushforward f).mapHomologicalComplex _ ≅
      relativeCechPresheaf f ⋙ CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (𝒰.f i)) :=
  Functor.isoWhiskerLeft (absoluteCechPresheaf X)
      (Stacks.CechPushforward.cechComplexFunctorCompMapHomologicalComplexIso
        (Scheme.Modules.pushforward f) (fun i ↦ Over.mk (𝒰.f i))) ≪≫
    eqToIso (flip_comp_whiskerings_comp (relativeMonad X) (Scheme.Modules.pushforward f)
      (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf))
      (CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (𝒰.f i))))

/-- The `ℤ`-indexed form of `pushforwardAbsoluteCechComplexIso`. -/
noncomputable def pushforwardAbsoluteCechComplexExtendIso (f : X ⟶ S) (𝒰 : X.OpenCover.{u}) :
    ((absoluteCechPresheaf X ⋙ CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (𝒰.f i))) ⋙
        ComplexShape.embeddingUpNat.extendFunctor X.Modules) ⋙
          (Scheme.Modules.pushforward f).mapHomologicalComplex _ ≅
      (relativeCechPresheaf f ⋙ CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (𝒰.f i))) ⋙
        ComplexShape.embeddingUpNat.extendFunctor S.Modules :=
  compExtendFunctorIso ComplexShape.embeddingUpNat _ _ (Scheme.Modules.pushforward f)
    (pushforwardAbsoluteCechComplexIso f 𝒰)

/-- **`f_*` of the bounded below absolute Čech resolution of a finite open cover is the relative
Čech complex of [Stacks, Tag 01XL]**, naturally in the quasi-coherent `𝒪_X`-module. -/
noncomputable def pushforwardAbsoluteCechComplexPlusIso (f : X ⟶ S) (𝒰 : X.OpenCover.{u})
    [Fintype 𝒰.I₀] :
    absoluteCechComplexPlus 𝒰 ⋙ (Scheme.Modules.pushforward f).mapCochainComplexPlus ≅
      relativeCechComplex f 𝒰 :=
  Functor.fullyFaithfulCancelRight (CochainComplex.Plus.ι S.Modules)
    (pushforwardAbsoluteCechComplexExtendIso f 𝒰)

/-! ### The degree zero cohomology -/

/-- The absolute Čech resolution vanishes in the degree from which the differential into degree
zero comes, that degree being negative. -/
theorem sc_zero_f_eq_zero_absoluteCechComplex (𝒰 : X.OpenCover.{u})
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    ((((absoluteCechPresheaf X ⋙
          CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (𝒰.f i))) ⋙
        ComplexShape.embeddingUpNat.extendFunctor X.Modules).obj F).sc 0).f = 0 := by
  refine (HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat
    ((ComplexShape.up ℤ).prev 0) (fun i ↦ ?_)).eq_zero_of_src _
  have h : (ComplexShape.up ℤ).prev 0 = -1 := by simp
  simp only [ComplexShape.embeddingUpNat_f, h]
  omega

/-- **The augmentation of the absolute Čech resolution is an isomorphism on degree zero
cohomology** ([Stacks, Tag 02FU]), naturally in the quasi-coherent module. -/
noncomputable def absoluteCechAugHomologyIso (𝒰 : X.OpenCover.{u}) :
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0) ⋙
        HomologicalComplex.homologyFunctor X.Modules (ComplexShape.up ℤ) 0 ≅
      ((absoluteCechPresheaf X ⋙
            CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (𝒰.f i))) ⋙
          ComplexShape.embeddingUpNat.extendFunctor X.Modules) ⋙
        HomologicalComplex.homologyFunctor X.Modules (ComplexShape.up ℤ) 0 :=
  haveI h : ∀ F, IsIso ((Functor.whiskerRight (absoluteCechAugZ X 𝒰)
      (HomologicalComplex.homologyFunctor X.Modules (ComplexShape.up ℤ) 0)).app F) := by
    intro F
    have hq := quasiIso_absoluteCechAugZ_app X 𝒰 F
    have : QuasiIsoAt ((absoluteCechAugZ X 𝒰).app F) 0 := inferInstance
    rw [quasiIsoAt_iff_isIso_homologyMap] at this
    exact this
  haveI : IsIso (Functor.whiskerRight (absoluteCechAugZ X 𝒰)
      (HomologicalComplex.homologyFunctor X.Modules (ComplexShape.up ℤ) 0)) :=
    NatIso.isIso_of_isIso_app _
  asIso (Functor.whiskerRight (absoluteCechAugZ X 𝒰)
    (HomologicalComplex.homologyFunctor X.Modules (ComplexShape.up ℤ) 0))

/-- **`H⁰(𝔠 ⁼(𝒰, ℱ)) ≅ ℱ`** for a finite open cover, naturally in the quasi-coherent
`𝒪_X`-module `ℱ` ([Stacks, Tag 02FU]). -/
noncomputable def absoluteCechHomologyZeroIso (𝒰 : X.OpenCover.{u}) [Fintype 𝒰.I₀] :
    (absoluteCechComplexPlus 𝒰 ⋙ CochainComplex.Plus.ι X.Modules) ⋙
        HomologicalComplex.homologyFunctor X.Modules (ComplexShape.up ℤ) 0 ≅
      ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) :=
  (absoluteCechAugHomologyIso 𝒰).symm ≪≫
    Functor.isoWhiskerLeft (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf))
      (HomologicalComplex.homologyFunctorSingleIso X.Modules (ComplexShape.up ℤ) 0) ≪≫
    Functor.rightUnitor _

/-- **`H⁰(Č ⁼(𝒰, f, ℱ)) ≅ f_* ℱ`** for a finite open cover `𝒰` of `X`, as an isomorphism of
functors of the quasi-coherent `𝒪_X`-module `ℱ`:  the degree zero cohomology of the relative Čech
complex of [Stacks, Tag 01XL] is the (underived) direct image.  No hypothesis is placed on `f`,
on `𝒰` or on the schemes beyond finiteness of the index set. -/
noncomputable def relativeCechHomologyZeroIso (f : X ⟶ S) (𝒰 : X.OpenCover.{u}) [Fintype 𝒰.I₀] :
    relativeCechComplex f 𝒰 ⋙ CochainComplex.Plus.ι S.Modules ⋙
        HomologicalComplex.homologyFunctor S.Modules (ComplexShape.up ℤ) 0 ≅
      ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        Scheme.Modules.pushforward f :=
  (Functor.isoWhiskerRight (pushforwardAbsoluteCechComplexPlusIso f 𝒰)
      (CochainComplex.Plus.ι S.Modules ⋙
        HomologicalComplex.homologyFunctor S.Modules (ComplexShape.up ℤ) 0)).symm ≪≫
    Stacks.HomologicalComplex.mapHomologyNatIso (Scheme.Modules.pushforward f)
      (absoluteCechComplexPlus 𝒰 ⋙ CochainComplex.Plus.ι X.Modules) 0
      (sc_zero_f_eq_zero_absoluteCechComplex 𝒰) ≪≫
    Functor.isoWhiskerRight (absoluteCechHomologyZeroIso 𝒰) (Scheme.Modules.pushforward f)

end Stacks.AlgebraicGeometry.RelativeCechOpenCover

end
