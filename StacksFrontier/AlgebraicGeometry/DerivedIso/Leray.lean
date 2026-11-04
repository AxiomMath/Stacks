module

public import StacksFrontier.AlgebraicGeometry.CechSiteChange.Resolution
public import StacksFrontier.AlgebraicGeometry.RightAcyclicProduct.Scheme
public import StacksFrontier.AlgebraicGeometry.DerivedIso.Transport

/-!
# The relative Čech complex computes `Rf_*ℱ` ([Stacks, Tag 01XL])

Let `f : X ⟶ S` be a morphism of schemes with `X` and `S` of affine diagonal, let `T` be a finite
affine open cover of `X`, and let `ℱ` be a quasi-coherent `𝒪_X`-module.  Leray's acyclicity lemma
([Stacks, Tag 015E]) applies to the absolute Čech resolution `𝔠 ⁼(𝒰, ℱ)`, because all of its terms
are right acyclic for `f_*`
(`Stacks.RightAcyclicProduct.rightAcyclic_absoluteCechComplex_X`), and
`Stacks.AlgebraicGeometry.Tag01XLDerivedIso.pushforwardAbsoluteCechComplexPlusIso` identifies
`f_* 𝔠 ⁼(𝒰, ℱ)` with the relative Čech complex `Č ⁼(𝒰, f, ℱ)` of [Stacks, Tag 01XL].  Combining
the two gives an isomorphism

`Č ⁼(𝒰, f, ℱ) ≅ Rf_*(𝔠 ⁼(𝒰, ℱ))`

in `D⁺(S)`, functorial in `ℱ`.  The augmentation `ℱ[0] ⟶ 𝔠 ⁼(𝒰, ℱ)` is a quasi-isomorphism
([Stacks, Tag 02FU], supplied in this spelling by
`Stacks.CechSiteChange.quasiIso_absoluteCechAugZ_app`), so `𝔠 ⁼(𝒰, ℱ)` may be replaced by `ℱ`,
which gives

`Č ⁼(𝒰, f, ℱ) ≅ Rf_*ℱ`.

## Main results

* `rightAcyclic_absoluteCechComplexPlus_X`: every term of the bounded below absolute Čech
  resolution, in every *integral* degree, is right acyclic for `f_*`.
* `isIso_rightDerivedFunctorPlusUnit_absoluteCechComplexPlus`: [Stacks, Tag 015E] applied.
* `mapHomotopyCategoryPlusFactors`: the bounded below homotopy quotient commutes with applying an
  additive functor termwise, which pinned Mathlib states only in the unbounded case
  (`CategoryTheory.Functor.mapHomotopyCategoryFactors`).
* `relativeCechComputesDerivedPushforward`: **the first isomorphism above**, as an isomorphism of
  functors of the quasi-coherent module.
* `absoluteCechResolutionIso`: **`ℱ[0] ≅ 𝔠 ⁼(𝒰, ℱ)` in `D⁺(X)`** — [Stacks, Tag 02FU] in the
  bounded below derived category.
* `relativeCechIsoDerivedPushforward`: **`Č ⁼(𝒰, f, ℱ) ≅ Rf_*ℱ` in `D⁺(S)`**, functorially in
  `ℱ`.

## Implementation notes

The passage from `D(X)` to `D⁺(X)` is a `CategoryTheory.Functor.fullyFaithfulCancelRight` against
the inclusion of the bounded below derived category:  both sides of
`absoluteCechResolutionIso`, composed with that inclusion, are *equal on the nose* to the
corresponding functors into `D(X)` (`singleFunctorPlus_comp_ι` and
`absoluteCechComplexPlus_comp_ι`), the only intervening comparison being
`DerivedCategory.quotientCompQhIso`.

## References

* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 02FU](https://stacks.math.columbia.edu/tag/02FU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.AlgebraicGeometry.Tag01XLDerivedIso

open Stacks.AlgebraicGeometry.RelativeCechComplex

/-! ### The bounded below homotopy quotient commutes with a termwise functor -/

section Quotient

variable {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
  (G : A ⥤ B) [G.Additive]

/-- **`CategoryTheory.Functor.mapHomotopyCategoryFactors` for bounded below complexes.**  Taking
the homotopy class of a bounded below complex and then applying `G` termwise is the same as
applying `G` termwise and then taking the homotopy class.  Pinned Mathlib states this for
unbounded complexes only; both sides here are `ObjectProperty.lift`s of the unbounded ones, so
the inclusion of the bounded below homotopy category cancels. -/
noncomputable def mapHomotopyCategoryPlusFactors :
    HomotopyCategory.Plus.quotient A ⋙ G.mapHomotopyCategoryPlus ≅
      G.mapCochainComplexPlus ⋙ HomotopyCategory.Plus.quotient B :=
  Functor.fullyFaithfulCancelRight (HomotopyCategory.Plus.ι B)
    (Functor.isoWhiskerLeft (CochainComplex.Plus.ι A)
      (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)))

end Quotient

/-! ### Leray's acyclicity lemma at the absolute Čech resolution -/

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X S : Scheme.{u}}

/-- **Every term of the bounded below absolute Čech resolution is right acyclic for `f_*`.**  In
a non-negative degree the term is a term of the `ℕ`-indexed Čech complex, handled by
`Stacks.RightAcyclicProduct.rightAcyclic_absoluteCechComplex_X`; in a negative degree it is a
zero object.  This is the hypothesis `∀ n, F.rightAcyclic (K.X n)` of Leray's acyclicity lemma,
for the `ℤ`-indexed complex that lemma consumes. -/
theorem rightAcyclic_absoluteCechComplexPlus_X (f : X ⟶ S) (T : X.AffineOpenCover) [Fintype T.I₀]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from S))]
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) (n : ℤ) :
    (Scheme.Modules.pushforward f).rightAcyclic
      (((absoluteCechComplexPlus T).obj F).obj.X n) := by
  rcases Int.lt_or_le n 0 with hn | hn
  · refine Stacks.RightAcyclicProduct.rightAcyclic_of_isZero _ ?_
    refine HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat n (fun m hm ↦ ?_)
    have h : (m : ℤ) = n := hm
    omega
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact Stacks.RightAcyclicProduct.rightAcyclic_of_iso _
      (HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat (i := m) rfl).symm
      (Stacks.RightAcyclicProduct.rightAcyclic_absoluteCechComplex_X f T F m)

/-- **Leray's acyclicity lemma at the absolute Čech resolution** ([Stacks, Tag 015E]): the
canonical map `f_* 𝔠 ⁼(𝒰, ℱ) ⟶ Rf_*(𝔠 ⁼(𝒰, ℱ))` is an isomorphism in `D⁺(S)`.  The map is the
component of `CategoryTheory.Functor.rightDerivedFunctorPlusUnit`, which is *by definition* the
unit [Stacks, Tag 015E] concludes the invertibility of. -/
theorem isIso_rightDerivedFunctorPlusUnit_absoluteCechComplexPlus (f : X ⟶ S)
    (T : X.AffineOpenCover) [Fintype T.I₀]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from S))]
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    IsIso ((Scheme.Modules.pushforward f).rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.quotient X.Modules).obj ((absoluteCechComplexPlus T).obj F))) :=
  CategoryTheory.Functor.isIso_totalRightDerivedUnit_app_of_rightAcyclic
    (Scheme.Modules.pushforward f) _ ((absoluteCechComplexPlus T).obj F).property
    (rightAcyclic_absoluteCechComplexPlus_X f T F)

/-- The isomorphism of [Stacks, Tag 015E] at the absolute Čech resolution, as an isomorphism of
functors of the quasi-coherent module. -/
noncomputable def absoluteCechUnitIso (f : X ⟶ S) (T : X.AffineOpenCover) [Fintype T.I₀]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from S))] :
    absoluteCechComplexPlus T ⋙ HomotopyCategory.Plus.quotient X.Modules ⋙
        (Scheme.Modules.pushforward f).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
      absoluteCechComplexPlus T ⋙ HomotopyCategory.Plus.quotient X.Modules ⋙
        DerivedCategory.Plus.Qh ⋙ (Scheme.Modules.pushforward f).rightDerivedFunctorPlus :=
  NatIso.ofComponents
    (fun F ↦
      haveI := isIso_rightDerivedFunctorPlusUnit_absoluteCechComplexPlus f T F
      asIso ((Scheme.Modules.pushforward f).rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.quotient X.Modules).obj ((absoluteCechComplexPlus T).obj F))))
    (fun {_ _} φ ↦ (Scheme.Modules.pushforward f).rightDerivedFunctorPlusUnit.naturality
      ((HomotopyCategory.Plus.quotient X.Modules).map ((absoluteCechComplexPlus T).map φ)))

/-- **The relative Čech complex of [Stacks, Tag 01XL] computes `Rf_*` of the absolute Čech
resolution.**  In `D⁺(S)`,

`Č ⁼(𝒰, f, ℱ) ≅ Rf_*(𝔠 ⁼(𝒰, ℱ))`,

functorially in the quasi-coherent `𝒪_X`-module `ℱ`.  The hypotheses are those of
[Stacks, Tag 01XL]: `T` a finite affine open cover of `X` (so `X` is quasi-compact and covered by
finitely many affine opens) and `X`, `S` of affine diagonal.  Nothing is assumed about `f`.

This is `relativeCechIsoDerivedPushforward` with `𝔠 ⁼(𝒰, ℱ)` in place of `ℱ`; the two are
identified by the resolution `absoluteCechResolutionIso`. -/
noncomputable def relativeCechComputesDerivedPushforward (f : X ⟶ S) (T : X.AffineOpenCover)
    [Fintype T.I₀]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from S))] :
    relativeCechComplex f T ⋙ HomotopyCategory.Plus.quotient S.Modules ⋙
        DerivedCategory.Plus.Qh ≅
      absoluteCechComplexPlus T ⋙ HomotopyCategory.Plus.quotient X.Modules ⋙
        DerivedCategory.Plus.Qh ⋙ (Scheme.Modules.pushforward f).rightDerivedFunctorPlus :=
  (Functor.isoWhiskerRight (pushforwardAbsoluteCechComplexPlusIso f T)
      (HomotopyCategory.Plus.quotient S.Modules ⋙ DerivedCategory.Plus.Qh)).symm ≪≫
    (Functor.isoWhiskerLeft (absoluteCechComplexPlus T)
      (Functor.isoWhiskerRight
        (mapHomotopyCategoryPlusFactors (Scheme.Modules.pushforward f))
        DerivedCategory.Plus.Qh)).symm ≪≫
    absoluteCechUnitIso f T

/-! ### The absolute Čech resolution computes `ℱ` in `D⁺(X)` -/

open Stacks.CechSiteChange

/-- The augmentation `ℱ[0] ⟶ 𝔠 ⁼(𝒰, ℱ)` becomes an isomorphism in the derived category, because
it is a quasi-isomorphism ([Stacks, Tag 02FU]). -/
theorem isIso_Q_map_absoluteCechAugZ (T : X.AffineOpenCover.{u, u})
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    IsIso (DerivedCategory.Q.map ((absoluteCechAugZ X T).app F)) := by
  have hq := quasiIso_absoluteCechAugZ_app X T F
  rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
  infer_instance

/-- The augmentation of the absolute Čech resolution, read in the derived category. -/
noncomputable def absoluteCechAugQ (T : X.AffineOpenCover.{u, u}) :
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0) ⋙ DerivedCategory.Q ⟶
      ((Stacks.AlgebraicGeometry.CechPushforwardComplex.absoluteCechPresheaf X ⋙
          CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (T.f i))) ⋙
          ComplexShape.embeddingUpNat.extendFunctor X.Modules) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (absoluteCechAugZ X T) DerivedCategory.Q

/-- **`ℱ[0] ≅ 𝔠 ⁼(𝒰, ℱ)` in `D(X)`** ([Stacks, Tag 02FU]), naturally in the quasi-coherent
module. -/
noncomputable def absoluteCechAugQIso (T : X.AffineOpenCover.{u, u}) :
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0) ⋙ DerivedCategory.Q ≅
      ((Stacks.AlgebraicGeometry.CechPushforwardComplex.absoluteCechPresheaf X ⋙
          CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (T.f i))) ⋙
          ComplexShape.embeddingUpNat.extendFunctor X.Modules) ⋙ DerivedCategory.Q :=
  haveI : ∀ F, IsIso ((absoluteCechAugQ T).app F) := fun F => isIso_Q_map_absoluteCechAugZ T F
  haveI : IsIso (absoluteCechAugQ T) := NatIso.isIso_of_isIso_app (absoluteCechAugQ T)
  asIso (absoluteCechAugQ T)

/-- The single functor into `D⁺(X)`, followed by the inclusion of `D⁺(X)` in `D(X)`, is the
localisation of the single cochain complex. -/
theorem singleFunctorPlus_comp_ι (X : Scheme.{u}) :
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        DerivedCategory.Plus.singleFunctor X.Modules 0) ⋙ DerivedCategory.Plus.ι =
      (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0) ⋙ DerivedCategory.Q :=
  rfl

/-- The bounded below absolute Čech resolution in `D⁺(X)`, followed by the inclusion of `D⁺(X)`
in `D(X)`, is the `ℤ`-indexed absolute Čech resolution localised. -/
theorem absoluteCechComplexPlus_comp_ι (T : X.AffineOpenCover.{u, u}) [Fintype T.I₀] :
    (absoluteCechComplexPlus T ⋙ HomotopyCategory.Plus.quotient X.Modules ⋙
        DerivedCategory.Plus.Qh) ⋙ DerivedCategory.Plus.ι =
      ((Stacks.AlgebraicGeometry.CechPushforwardComplex.absoluteCechPresheaf X ⋙
          CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (T.f i))) ⋙
          ComplexShape.embeddingUpNat.extendFunctor X.Modules) ⋙
        HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  rfl

/-- `ℱ[0] ≅ 𝔠 ⁼(𝒰, ℱ)`, after the inclusion of `D⁺(X)` in `D(X)`. -/
noncomputable def absoluteCechResolutionIsoι (T : X.AffineOpenCover.{u, u}) [Fintype T.I₀] :
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        DerivedCategory.Plus.singleFunctor X.Modules 0) ⋙ DerivedCategory.Plus.ι ≅
      (absoluteCechComplexPlus T ⋙ HomotopyCategory.Plus.quotient X.Modules ⋙
        DerivedCategory.Plus.Qh) ⋙ DerivedCategory.Plus.ι :=
  eqToIso (singleFunctorPlus_comp_ι X) ≪≫ absoluteCechAugQIso T ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso X.Modules).symm ≪≫
    eqToIso (absoluteCechComplexPlus_comp_ι T).symm

/-- **`ℱ[0] ≅ 𝔠 ⁼(𝒰, ℱ)` in `D⁺(X)`** ([Stacks, Tag 02FU]), naturally in the quasi-coherent
`𝒪_X`-module `ℱ`.  The inclusion of `D⁺(X)` in `D(X)` is fully faithful, so the isomorphism
descends from `absoluteCechResolutionIsoι`. -/
noncomputable def absoluteCechResolutionIso (T : X.AffineOpenCover.{u, u}) [Fintype T.I₀] :
    ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        DerivedCategory.Plus.singleFunctor X.Modules 0 ≅
      absoluteCechComplexPlus T ⋙ HomotopyCategory.Plus.quotient X.Modules ⋙
        DerivedCategory.Plus.Qh :=
  Functor.fullyFaithfulCancelRight DerivedCategory.Plus.ι (absoluteCechResolutionIsoι T)

/-- **The relative Čech complex of [Stacks, Tag 01XL] computes `Rf_*ℱ`.**  In `D⁺(S)`,

`Č ⁼(𝒰, f, ℱ) ≅ Rf_*ℱ`,

functorially in the quasi-coherent `𝒪_X`-module `ℱ`.  The hypotheses are those of
[Stacks, Tag 01XL]: `T` a finite affine open cover of `X` — so `X` is quasi-compact and covered
by finitely many affine opens — and `X`, `S` of affine diagonal.  Nothing is assumed about `f`.

This is `relativeCechComputesDerivedPushforward` composed with the resolution
`ℱ[0] ≅ 𝔠 ⁼(𝒰, ℱ)` of [Stacks, Tag 02FU]. -/
@[stacks 01XL "the derived isomorphism"]
noncomputable def relativeCechIsoDerivedPushforward (f : X ⟶ S) (T : X.AffineOpenCover.{u, u})
    [Fintype T.I₀]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from S))] :
    relativeCechComplex f T ⋙ HomotopyCategory.Plus.quotient S.Modules ⋙
        DerivedCategory.Plus.Qh ≅
      ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        DerivedCategory.Plus.singleFunctor X.Modules 0 ⋙
          (Scheme.Modules.pushforward f).rightDerivedFunctorPlus :=
  relativeCechComputesDerivedPushforward f T ≪≫
    (Functor.isoWhiskerRight (absoluteCechResolutionIso T)
      ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus)).symm

/-- **The hypothesis audit, committed rather than asserted.**  The binder list is [Stacks, Tag
01XL]'s — the morphism `f`, the quasi-coherent module `ℱ`, the finite affine
open covering `𝒰`, and affine diagonal for `X` and for `S` — and nothing else: no affineness, no
Noetherian hypothesis, no separatedness, no condition on `f`, and no smallness beyond the one the
source itself carries (the index type of the covering lies in `Type u`, forced by
`CategoryTheory.cechComplexFunctor` demanding `HasProducts.{u} S.Modules`).  `Fintype T.I₀` on an
`AffineOpenCover` is exactly "`X` is quasi-compact and `𝒰` is a finite affine open covering". -/
example {X S : Scheme.{u}} (f : X ⟶ S)
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    (T : X.AffineOpenCover) [Fintype T.I₀]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from S))] :
    Nonempty (DerivedCategory.Plus.Qh.obj
        ((HomotopyCategory.Plus.quotient S.Modules).obj ((relativeCechComplex f T).obj F)) ≅
      (Scheme.Modules.pushforward f).rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Qh.obj
          ((HomotopyCategory.Plus.quotient X.Modules).obj
            ((absoluteCechComplexPlus T).obj F)))) :=
  ⟨(relativeCechComputesDerivedPushforward f T).app F⟩

end Stacks.AlgebraicGeometry.Tag01XLDerivedIso

end
