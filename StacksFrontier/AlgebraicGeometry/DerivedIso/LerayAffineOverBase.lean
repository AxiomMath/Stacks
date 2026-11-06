module

public import StacksFrontier.AlgebraicGeometry.DerivedIso.Leray
public import StacksFrontier.AlgebraicGeometry.DerivedIso.RelativeCechZeroOpenCover

/-!
# The relative Čech complex computes `Rf_*ℱ` for a cover that is affine over the base

Let `f : X ⟶ S` be a morphism of schemes, let `𝒰` be a finite open cover of `X`, and let `ℱ` be
a quasi-coherent `𝒪_X`-module.  [Stacks, Tag 01XL] is proved in
`Stacks.AlgebraicGeometry.Tag01XLDerivedIso.relativeCechIsoDerivedPushforward` for a finite
*affine* open cover of a scheme of affine diagonal over a base of affine diagonal.  This file
proves the same conclusion under an incomparable hypothesis: each intersection
`U_{i_0 … i_p} = U_{i_0} ∩ ⋯ ∩ U_{i_p}` of members of the cover is **affine over the base**,
meaning that its inclusion `j : U_{i_0 … i_p} ⟶ X` is an affine morphism and so is `j ≫ f`.
Neither the members of `𝒰` nor the schemes `X` and `S` are assumed affine, and no diagonal is
assumed affine.

The mathematics is Leray's acyclicity lemma ([Stacks, Tag 015E]) exactly as in the affine case:
the terms of the absolute Čech resolution `𝔠 ⁼(𝒰, ℱ)` are finite products of modules
`j_* j ^* ℱ`, and `Stacks.AlgebraicGeometry.RelativeCechAcyclic.rightAcyclic_pushforward_comp`
makes such a module right acyclic for `f_*` precisely under the hypothesis above.  In the affine
case the two affineness assertions are consequences of affineness of `U_{i_0 … i_p}` together
with affineness of the diagonals; here they are assumed outright, which is weaker on one side
and stronger on the other.

## Main results

* `rightAcyclic_absoluteCechComplex_X`: every term of the `ℕ`-indexed absolute Čech resolution
  of a cover that is affine over the base is right acyclic for `f_*`.
* `rightAcyclic_absoluteCechComplexPlus_X`: the same for the bounded below resolution, in every
  integral degree — the hypothesis of [Stacks, Tag 015E].
* `relativeCechComputesDerivedPushforward`: **`Č ⁼(𝒰, f, ℱ) ≅ Rf_*(𝔠 ⁼(𝒰, ℱ))` in `D⁺(S)`**,
  functorially in `ℱ`.
* `absoluteCechResolutionIso`: **`ℱ[0] ≅ 𝔠 ⁼(𝒰, ℱ)` in `D⁺(X)`** for an arbitrary finite open
  cover — [Stacks, Tag 02FU], with no affineness hypothesis whatsoever.
* `relativeCechIsoDerivedPushforward`: **`Č ⁼(𝒰, f, ℱ) ≅ Rf_*ℱ` in `D⁺(S)`**, functorially
  in `ℱ`.
* `relativeCechIsoDerivedPushforwardOfMembers`: the same, with the two affineness hypotheses
  taken at the members `U_i` of the cover instead of at their intersections.
* `isAffineHom_iInf_ι`: a finite nonempty intersection of opens whose inclusions are affine
  morphisms has affine inclusion, so the hypotheses at the intersections follow from the
  hypotheses at the members (`isAffineHom_pi_hom_of_members`,
  `isAffineHom_pi_hom_comp_of_members`).

## Implementation notes

The affineness hypotheses of the main results are stated at the intersections, as two explicit
hypotheses about the products `∏ᶜ (fun a ↦ Over.mk (𝒰.f (i a)))` in `Over X`: the degree `n`
term of the Čech resolution is the product over the `(n + 1)`-tuples `i : Fin (n + 1) → 𝒰.I₀` of
the value of the coefficient presheaf at that product. The hypotheses at the members imply them,
through the identification of a finite product in `Over X` of open subschemes with the
intersection of their ranges
(`Stacks.AlgebraicGeometry.RelativeCechComplex.isLimitOpenImmersionFan`).

## References

* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 02FU](https://stacks.math.columbia.edu/tag/02FU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.AlgebraicGeometry.LerayAffineOverBase

open Stacks.AlgebraicGeometry.RelativeCech
open Stacks.AlgebraicGeometry.CechPushforwardComplex
open Stacks.AlgebraicGeometry.RelativeCechOpenCover
open Stacks.RightAcyclicProduct

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X S : Scheme.{u}}

/-! ### The hypotheses at the intersections, from affineness of the members -/

section Members

open Stacks.AlgebraicGeometry.RelativeCechComplex (commonOpen isLimitOpenImmersionFan)

/-- **An open subscheme whose inclusion is an affine morphism is affine over an open subscheme
containing it**: for opens `U ≤ V` of `X` with `U.ι` affine, the inclusion `U ⟶ V` is an affine
morphism. -/
theorem isAffineHom_homOfLE {U V : X.Opens} (h : U ≤ V) (hU : IsAffineHom U.ι) :
    IsAffineHom (X.homOfLE h) := by
  have hri : MorphismProperty.RespectsIso (@IsAffineHom) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hdg : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.diagonal @IsAffineHom) :=
    MorphismProperty.IsStableUnderBaseChange.diagonal
  have hpost : MorphismProperty.HasOfPostcompProperty (@IsAffineHom)
      (MorphismProperty.diagonal @IsAffineHom) :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr le_rfl
  refine MorphismProperty.of_postcomp (W := @IsAffineHom)
    (W' := MorphismProperty.diagonal @IsAffineHom) (X.homOfLE h) V.ι ?_ ?_
  · have hiso : IsIso (pullback.diagonal V.ι) :=
      (pullback.isIso_diagonal_iff V.ι).mpr inferInstance
    exact MorphismProperty.diagonal_iff.mpr inferInstance
  · rw [X.homOfLE_ι]
    exact hU

/-- **The intersection of two opens with affine inclusion has affine inclusion.** -/
theorem isAffineHom_inf_ι {U V : X.Opens} (hU : IsAffineHom U.ι) (hV : IsAffineHom V.ι) :
    IsAffineHom (U ⊓ V).ι := by
  have hbc : IsAffineHom (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) :=
    MorphismProperty.of_isPullback (AlgebraicGeometry.isPullback_opens_inf U V) hU
  rw [← X.homOfLE_ι (inf_le_right : U ⊓ V ≤ V)]
  infer_instance

/-- **A finite nonempty intersection of opens with affine inclusion has affine inclusion.** -/
theorem isAffineHom_iInf_ι {α : Sort*} [Finite α] [Nonempty α] {U : α → X.Opens}
    (hU : ∀ a, IsAffineHom (U a).ι) : IsAffineHom (⨅ a, U a).ι :=
  InfClosed.iInf_mem_of_nonempty (s := Set.ofPred fun V : X.Opens ↦ IsAffineHom V.ι)
    (fun _ h _ h' ↦ isAffineHom_inf_ι h h') hU

/-- The inclusion of the range of an affine open immersion is an affine morphism. -/
theorem isAffineHom_opensRange_ι {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g]
    (hg : IsAffineHom g) : IsAffineHom g.opensRange.ι := by
  rw [← Scheme.Hom.isoOpensRange_inv_comp g]
  infer_instance

/-- If the composite of an open immersion with `f` is affine, so is the composite of the
inclusion of its range with `f`. -/
theorem isAffineHom_opensRange_ι_comp {Y : Scheme.{u}} (g : Y ⟶ X) (f : X ⟶ S)
    [IsOpenImmersion g] (hg : IsAffineHom (g ≫ f)) : IsAffineHom (g.opensRange.ι ≫ f) := by
  rw [← Scheme.Hom.isoOpensRange_inv_comp g, Category.assoc]
  infer_instance

variable {α : Type} [Finite α] (V : α → Over X) [∀ a, IsOpenImmersion (V a).hom] [HasProduct V]

/-- **A finite product in `Over X` of open subschemes is their intersection**, as an isomorphism
of objects of `Over X`. -/
noncomputable def piIsoCommonOpen : (∏ᶜ V : Over X) ≅ Over.mk (commonOpen V).ι :=
  (limit.isLimit _).conePointUniqueUpToIso (isLimitOpenImmersionFan V)

/-- The structure morphism of a finite product in `Over X` of open subschemes is the inclusion
of their intersection, up to the isomorphism `piIsoCommonOpen`. -/
theorem pi_hom_eq :
    (∏ᶜ V : Over X).hom = (piIsoCommonOpen V).hom.left ≫ (commonOpen V).ι :=
  (Over.w (piIsoCommonOpen V).hom).symm

/-- The underlying scheme morphism of `piIsoCommonOpen` is an isomorphism. -/
theorem isIso_piIsoCommonOpen_hom_left : IsIso (piIsoCommonOpen V).hom.left :=
  inferInstanceAs (IsIso (((Over.forget X).mapIso (piIsoCommonOpen V)).hom))

/-- The structure morphism of a finite product in `Over X` of open subschemes is affine as soon
as the inclusion of their intersection is. -/
theorem isAffineHom_pi_hom (h : IsAffineHom (commonOpen V).ι) :
    IsAffineHom (∏ᶜ V : Over X).hom := by
  have hiso := isIso_piIsoCommonOpen_hom_left V
  rw [pi_hom_eq V]
  infer_instance

/-- The composite with `f` of the structure morphism of a finite product in `Over X` of open
subschemes is affine as soon as the composite with `f` of the inclusion of their intersection
is. -/
theorem isAffineHom_pi_hom_comp (f : X ⟶ S) (h : IsAffineHom ((commonOpen V).ι ≫ f)) :
    IsAffineHom ((∏ᶜ V : Over X).hom ≫ f) := by
  have hiso := isIso_piIsoCommonOpen_hom_left V
  rw [pi_hom_eq V, Category.assoc]
  infer_instance

private instance isOpenImmersion_over_mk_hom {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] :
    IsOpenImmersion (Over.mk g).hom :=
  inferInstanceAs (IsOpenImmersion g)

/-- If every member of the open cover `𝒰` has affine inclusion into `X`, then so does the
intersection of the members `𝒰.f (i a)`. -/
private theorem commonOpen_ι_isAffineHom_of_members (𝒰 : X.OpenCover.{u}) {k : ℕ}
    (i : Fin (k + 1) → 𝒰.I₀) (hm : ∀ j, IsAffineHom (𝒰.f j)) :
    IsAffineHom (commonOpen (fun a ↦ (Over.mk (𝒰.f (i a)) : Over X))).ι :=
  isAffineHom_iInf_ι (fun a ↦ isAffineHom_opensRange_ι (𝒰.f (i a)) (hm (i a)))

/-- If every member of the open cover `𝒰` has affine inclusion into `X`, then the structure
morphism of the product in `Over X` of the members `𝒰.f (i a)` is affine. -/
theorem isAffineHom_pi_hom_of_members (𝒰 : X.OpenCover.{u}) {k : ℕ} (i : Fin (k + 1) → 𝒰.I₀)
    (hm : ∀ j, IsAffineHom (𝒰.f j)) :
    IsAffineHom (∏ᶜ (fun a ↦ (Over.mk (𝒰.f (i a)) : Over X))).hom := by
  have hc := commonOpen_ι_isAffineHom_of_members 𝒰 i hm
  exact isAffineHom_pi_hom _ hc

/-- If every member of the open cover `𝒰` has affine inclusion into `X` and affine composite with
`f`, then the composite with `f` of the structure morphism of the product in `Over X` of the
members `𝒰.f (i a)` is affine. -/
theorem isAffineHom_pi_hom_comp_of_members (f : X ⟶ S) (𝒰 : X.OpenCover.{u}) {k : ℕ}
    (i : Fin (k + 1) → 𝒰.I₀) (hm : ∀ j, IsAffineHom (𝒰.f j))
    (hmf : ∀ j, IsAffineHom (𝒰.f j ≫ f)) :
    IsAffineHom ((∏ᶜ (fun a ↦ (Over.mk (𝒰.f (i a)) : Over X))).hom ≫ f) := by
  have hc := commonOpen_ι_isAffineHom_of_members 𝒰 i hm
  have hle : commonOpen (fun a ↦ (Over.mk (𝒰.f (i a)) : Over X)) ≤
      (𝒰.f (i 0)).opensRange := iInf_le _ 0
  have h₁ : IsAffineHom (X.homOfLE hle) := isAffineHom_homOfLE hle hc
  have h₂ : IsAffineHom ((𝒰.f (i 0)).opensRange.ι ≫ f) :=
    isAffineHom_opensRange_ι_comp (𝒰.f (i 0)) f (hmf (i 0))
  have hcf : IsAffineHom
      ((commonOpen (fun a ↦ (Over.mk (𝒰.f (i a)) : Over X))).ι ≫ f) := by
    rw [← X.homOfLE_ι hle, Category.assoc]
    infer_instance
  exact isAffineHom_pi_hom_comp _ f hcf

end Members

/-! ### Acyclicity of the terms of the absolute Čech resolution -/

/-- **The value of the absolute coefficient presheaf at an object affine over the base is right
acyclic for `f_*`**: for `A` in `Over X` with `A.hom` and `A.hom ≫ f` affine morphisms, the
module `A.hom_* A.hom ^* ℱ` is right acyclic for `f_*`. -/
theorem rightAcyclic_cechMonadPresheaf_obj (f : X ⟶ S) (A : Over X) [IsAffineHom A.hom]
    [IsAffineHom (A.hom ≫ f)]
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (Scheme.Modules.pushforward f).rightAcyclic
      (((relativeMonad X).flip.obj F.obj).obj (op A)) := by
  have hpb : ((Scheme.Modules.pullback A.hom).obj F.obj).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback A.hom F.obj F.property
  exact Stacks.AlgebraicGeometry.RelativeCechAcyclic.rightAcyclic_pushforward_comp A.hom f
    ((Scheme.Modules.pullback A.hom).obj F.obj)

/-- **Every term of the absolute Čech resolution of a finite open cover that is affine over the
base is right acyclic for `f_*`.** -/
theorem rightAcyclic_absoluteCechComplex_X (f : X ⟶ S) (𝒰 : X.OpenCover.{u}) [Finite 𝒰.I₀]
    (hj : ∀ {k : ℕ} (i : Fin (k + 1) → 𝒰.I₀),
      IsAffineHom (∏ᶜ (fun a ↦ (Over.mk (𝒰.f (i a)) : Over X))).hom)
    (hjf : ∀ {k : ℕ} (i : Fin (k + 1) → 𝒰.I₀),
      IsAffineHom ((∏ᶜ (fun a ↦ (Over.mk (𝒰.f (i a)) : Over X))).hom ≫ f))
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) (n : ℕ) :
    (Scheme.Modules.pushforward f).rightAcyclic
      (((CategoryTheory.cechComplexFunctor (fun i ↦ (Over.mk (𝒰.f i) : Over X))).obj
        ((relativeMonad X).flip.obj F.obj)).X n) := by
  have key : (Scheme.Modules.pushforward f).rightAcyclic
      (∏ᶜ (fun (i : Fin (n + 1) → 𝒰.I₀) ↦
        ((relativeMonad X).flip.obj F.obj).obj
          (op (∏ᶜ (fun a ↦ (Over.mk (𝒰.f (i a)) : Over X)))))) := by
    refine rightAcyclic_pi _ _ (fun i ↦ ?_)
    have h₁ := hj i
    have h₂ := hjf i
    exact rightAcyclic_cechMonadPresheaf_obj f _ F
  exact key

/-- **Every term of the bounded below absolute Čech resolution of a finite open cover that is
affine over the base is right acyclic for `f_*`**, in every integral degree. -/
theorem rightAcyclic_absoluteCechComplexPlus_X (f : X ⟶ S) (𝒰 : X.OpenCover.{u}) [Fintype 𝒰.I₀]
    (hj : ∀ {k : ℕ} (i : Fin (k + 1) → 𝒰.I₀),
      IsAffineHom (∏ᶜ (fun a ↦ (Over.mk (𝒰.f (i a)) : Over X))).hom)
    (hjf : ∀ {k : ℕ} (i : Fin (k + 1) → 𝒰.I₀),
      IsAffineHom ((∏ᶜ (fun a ↦ (Over.mk (𝒰.f (i a)) : Over X))).hom ≫ f))
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) (n : ℤ) :
    (Scheme.Modules.pushforward f).rightAcyclic
      (((absoluteCechComplexPlus 𝒰).obj F).obj.X n) := by
  rcases Int.lt_or_le n 0 with hn | hn
  · refine rightAcyclic_of_isZero _ ?_
    refine HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat n (fun m hm ↦ ?_)
    have h : (m : ℤ) = n := hm
    omega
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact rightAcyclic_of_iso _
      (HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat (i := m) rfl).symm
      (rightAcyclic_absoluteCechComplex_X f 𝒰 hj hjf F m)

/-- **Leray's acyclicity lemma at the absolute Čech resolution** ([Stacks, Tag 015E]): the
canonical map `f_* 𝔠 ⁼(𝒰, ℱ) ⟶ Rf_*(𝔠 ⁼(𝒰, ℱ))`, the component of
`CategoryTheory.Functor.rightDerivedFunctorPlusUnith`, is an isomorphism in `D⁺(S)`. -/
theorem isIso_rightDerivedFunctorPlusUnit_absoluteCechComplexPlus (f : X ⟶ S)
    (𝒰 : X.OpenCover.{u}) [Fintype 𝒰.I₀]
    (hj : ∀ {k : ℕ} (i : Fin (k + 1) → 𝒰.I₀),
      IsAffineHom (∏ᶜ (fun a ↦ (Over.mk (𝒰.f (i a)) : Over X))).hom)
    (hjf : ∀ {k : ℕ} (i : Fin (k + 1) → 𝒰.I₀),
      IsAffineHom ((∏ᶜ (fun a ↦ (Over.mk (𝒰.f (i a)) : Over X))).hom ≫ f))
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    IsIso ((Scheme.Modules.pushforward f).rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient X.Modules).obj ((absoluteCechComplexPlus 𝒰).obj F))) := by
  have hβ := CategoryTheory.Functor.isIso_totalRightDerivedUnit_app_of_rightAcyclic
    (Scheme.Modules.pushforward f) _ ((absoluteCechComplexPlus 𝒰).obj F).property
    (rightAcyclic_absoluteCechComplexPlus_X f 𝒰 hj hjf F)
  have hd := (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc
    (Scheme.Modules.pushforward f).rightDerivedFunctorPlus
    (Scheme.Modules.pushforward f).rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso X.Modules) _
    (((Scheme.Modules.pushforward f).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh).totalRightDerivedUnit
      DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso X.Modules))).1 inferInstance
  rw [← Functor.rightDerived_fac_app (Scheme.Modules.pushforward f).rightDerivedFunctorPlus
    (Scheme.Modules.pushforward f).rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso X.Modules)] at hβ
  rwa [isIso_comp_right_iff] at hβ

/-- The isomorphism of [Stacks, Tag 015E] at the absolute Čech resolution, as an isomorphism of
functors of the quasi-coherent module. -/
noncomputable def absoluteCechUnitIso (f : X ⟶ S) (𝒰 : X.OpenCover.{u}) [Fintype 𝒰.I₀]
    (hj : ∀ {k : ℕ} (i : Fin (k + 1) → 𝒰.I₀),
      IsAffineHom (∏ᶜ (fun a ↦ (Over.mk (𝒰.f (i a)) : Over X))).hom)
    (hjf : ∀ {k : ℕ} (i : Fin (k + 1) → 𝒰.I₀),
      IsAffineHom ((∏ᶜ (fun a ↦ (Over.mk (𝒰.f (i a)) : Over X))).hom ≫ f)) :
    absoluteCechComplexPlus 𝒰 ⋙ HomotopyCategory.Plus.quotient X.Modules ⋙
        (Scheme.Modules.pushforward f).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
      absoluteCechComplexPlus 𝒰 ⋙ HomotopyCategory.Plus.quotient X.Modules ⋙
        DerivedCategory.Plus.Qh ⋙ (Scheme.Modules.pushforward f).rightDerivedFunctorPlus :=
  NatIso.ofComponents
    (fun F ↦
      haveI := isIso_rightDerivedFunctorPlusUnit_absoluteCechComplexPlus f 𝒰 hj hjf F
      asIso ((Scheme.Modules.pushforward f).rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.quotient X.Modules).obj ((absoluteCechComplexPlus 𝒰).obj F))))
    (fun {_ _} φ ↦ (Scheme.Modules.pushforward f).rightDerivedFunctorPlusUnith.naturality
      ((HomotopyCategory.Plus.quotient X.Modules).map ((absoluteCechComplexPlus 𝒰).map φ)))

/-- **The relative Čech complex of [Stacks, Tag 01XL] computes `Rf_*` of the absolute Čech
resolution**, for a finite open cover affine over the base.  In `D⁺(S)`,

`Č ⁼(𝒰, f, ℱ) ≅ Rf_*(𝔠 ⁼(𝒰, ℱ))`,

functorially in the quasi-coherent `𝒪_X`-module `ℱ`. -/
noncomputable def relativeCechComputesDerivedPushforward (f : X ⟶ S) (𝒰 : X.OpenCover.{u})
    [Fintype 𝒰.I₀]
    (hj : ∀ {k : ℕ} (i : Fin (k + 1) → 𝒰.I₀),
      IsAffineHom (∏ᶜ (fun a ↦ (Over.mk (𝒰.f (i a)) : Over X))).hom)
    (hjf : ∀ {k : ℕ} (i : Fin (k + 1) → 𝒰.I₀),
      IsAffineHom ((∏ᶜ (fun a ↦ (Over.mk (𝒰.f (i a)) : Over X))).hom ≫ f)) :
    relativeCechComplex f 𝒰 ⋙ HomotopyCategory.Plus.quotient S.Modules ⋙
        DerivedCategory.Plus.Qh ≅
      absoluteCechComplexPlus 𝒰 ⋙ HomotopyCategory.Plus.quotient X.Modules ⋙
        DerivedCategory.Plus.Qh ⋙ (Scheme.Modules.pushforward f).rightDerivedFunctorPlus :=
  (Functor.isoWhiskerRight (pushforwardAbsoluteCechComplexPlusIso f 𝒰)
      (HomotopyCategory.Plus.quotient S.Modules ⋙ DerivedCategory.Plus.Qh)).symm ≪≫
    (Functor.isoWhiskerLeft (absoluteCechComplexPlus 𝒰)
      (Functor.isoWhiskerRight
        (Tag01XLDerivedIso.mapHomotopyCategoryPlusFactors (Scheme.Modules.pushforward f))
        DerivedCategory.Plus.Qh)).symm ≪≫
    absoluteCechUnitIso f 𝒰 hj hjf

/-! ### The absolute Čech resolution computes `ℱ` in `D⁺(X)` -/

/-- The augmentation `ℱ[0] ⟶ 𝔠 ⁼(𝒰, ℱ)` becomes an isomorphism in the derived category
([Stacks, Tag 02FU]). -/
theorem isIso_Q_map_absoluteCechAugZ (𝒰 : X.OpenCover.{u})
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    IsIso (DerivedCategory.Q.map ((absoluteCechAugZ X 𝒰).app F)) := by
  have hq := quasiIso_absoluteCechAugZ_app X 𝒰 F
  rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
  infer_instance

/-- The augmentation of the absolute Čech resolution, read in the derived category. -/
noncomputable def absoluteCechAugQ (𝒰 : X.OpenCover.{u}) :
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0) ⋙ DerivedCategory.Q ⟶
      ((absoluteCechPresheaf X ⋙
          CategoryTheory.cechComplexFunctor (fun i ↦ (Over.mk (𝒰.f i) : Over X))) ⋙
          ComplexShape.embeddingUpNat.extendFunctor X.Modules) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (absoluteCechAugZ X 𝒰) DerivedCategory.Q

/-- **`ℱ[0] ≅ 𝔠 ⁼(𝒰, ℱ)` in `D(X)`** ([Stacks, Tag 02FU]), naturally in the quasi-coherent
module. -/
noncomputable def absoluteCechAugQIso (𝒰 : X.OpenCover.{u}) :
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0) ⋙ DerivedCategory.Q ≅
      ((absoluteCechPresheaf X ⋙
          CategoryTheory.cechComplexFunctor (fun i ↦ (Over.mk (𝒰.f i) : Over X))) ⋙
          ComplexShape.embeddingUpNat.extendFunctor X.Modules) ⋙ DerivedCategory.Q :=
  haveI : ∀ F, IsIso ((absoluteCechAugQ 𝒰).app F) := fun F ↦ isIso_Q_map_absoluteCechAugZ 𝒰 F
  haveI : IsIso (absoluteCechAugQ 𝒰) := NatIso.isIso_of_isIso_app (absoluteCechAugQ 𝒰)
  asIso (absoluteCechAugQ 𝒰)

/-- The bounded below absolute Čech resolution in `D⁺(X)`, followed by the inclusion of `D⁺(X)`
in `D(X)`, is the `ℤ`-indexed absolute Čech resolution localised. -/
theorem absoluteCechComplexPlus_comp_ι (𝒰 : X.OpenCover.{u}) [Fintype 𝒰.I₀] :
    (absoluteCechComplexPlus 𝒰 ⋙ HomotopyCategory.Plus.quotient X.Modules ⋙
        DerivedCategory.Plus.Qh) ⋙ DerivedCategory.Plus.ι =
      ((absoluteCechPresheaf X ⋙
          CategoryTheory.cechComplexFunctor (fun i ↦ (Over.mk (𝒰.f i) : Over X))) ⋙
          ComplexShape.embeddingUpNat.extendFunctor X.Modules) ⋙
        HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  rfl

/-- `ℱ[0] ≅ 𝔠 ⁼(𝒰, ℱ)`, after the inclusion of `D⁺(X)` in `D(X)`. -/
noncomputable def absoluteCechResolutionIsoι (𝒰 : X.OpenCover.{u}) [Fintype 𝒰.I₀] :
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        DerivedCategory.Plus.singleFunctor X.Modules 0) ⋙ DerivedCategory.Plus.ι ≅
      (absoluteCechComplexPlus 𝒰 ⋙ HomotopyCategory.Plus.quotient X.Modules ⋙
        DerivedCategory.Plus.Qh) ⋙ DerivedCategory.Plus.ι :=
  eqToIso (Tag01XLDerivedIso.singleFunctorPlus_comp_ι X) ≪≫ absoluteCechAugQIso 𝒰 ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso X.Modules).symm ≪≫
    eqToIso (absoluteCechComplexPlus_comp_ι 𝒰).symm

/-- **`ℱ[0] ≅ 𝔠 ⁼(𝒰, ℱ)` in `D⁺(X)`** ([Stacks, Tag 02FU]) for an arbitrary finite open cover,
naturally in the quasi-coherent `𝒪_X`-module `ℱ`. -/
noncomputable def absoluteCechResolutionIso (𝒰 : X.OpenCover.{u}) [Fintype 𝒰.I₀] :
    ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        DerivedCategory.Plus.singleFunctor X.Modules 0 ≅
      absoluteCechComplexPlus 𝒰 ⋙ HomotopyCategory.Plus.quotient X.Modules ⋙
        DerivedCategory.Plus.Qh :=
  Functor.fullyFaithfulCancelRight DerivedCategory.Plus.ι (absoluteCechResolutionIsoι 𝒰)

/-- **The relative Čech complex of [Stacks, Tag 01XL] computes `Rf_*ℱ` for a finite open cover
affine over the base.**  In `D⁺(S)`,

`Č ⁼(𝒰, f, ℱ) ≅ Rf_*ℱ`,

functorially in the quasi-coherent `𝒪_X`-module `ℱ`.  The hypotheses are: `𝒰` a finite open
cover of `X`, and each intersection of members of `𝒰` affine over the base, in the sense that its
inclusion `j` into `X` and the composite `j ≫ f` are affine morphisms.  The members of `𝒰` need
not be affine schemes and neither `X` nor `S` need have affine diagonal. -/
noncomputable def relativeCechIsoDerivedPushforward (f : X ⟶ S) (𝒰 : X.OpenCover.{u})
    [Fintype 𝒰.I₀]
    (hj : ∀ {k : ℕ} (i : Fin (k + 1) → 𝒰.I₀),
      IsAffineHom (∏ᶜ (fun a ↦ (Over.mk (𝒰.f (i a)) : Over X))).hom)
    (hjf : ∀ {k : ℕ} (i : Fin (k + 1) → 𝒰.I₀),
      IsAffineHom ((∏ᶜ (fun a ↦ (Over.mk (𝒰.f (i a)) : Over X))).hom ≫ f)) :
    relativeCechComplex f 𝒰 ⋙ HomotopyCategory.Plus.quotient S.Modules ⋙
        DerivedCategory.Plus.Qh ≅
      ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        DerivedCategory.Plus.singleFunctor X.Modules 0 ⋙
          (Scheme.Modules.pushforward f).rightDerivedFunctorPlus :=
  relativeCechComputesDerivedPushforward f 𝒰 hj hjf ≪≫
    (Functor.isoWhiskerRight (absoluteCechResolutionIso 𝒰)
      ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus)).symm

/-- **`Č ⁼(𝒰, f, ℱ) ≅ Rf_*ℱ` for a finite open cover whose members are affine over the base.**
Here the inclusion `𝒰.f i : U_i ⟶ X` and the composite `𝒰.f i ≫ f : U_i ⟶ S` are affine for
every `i`. -/
noncomputable def relativeCechIsoDerivedPushforwardOfMembers (f : X ⟶ S) (𝒰 : X.OpenCover.{u})
    [Fintype 𝒰.I₀] (hm : ∀ i, IsAffineHom (𝒰.f i)) (hmf : ∀ i, IsAffineHom (𝒰.f i ≫ f)) :
    relativeCechComplex f 𝒰 ⋙ HomotopyCategory.Plus.quotient S.Modules ⋙
        DerivedCategory.Plus.Qh ≅
      ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        DerivedCategory.Plus.singleFunctor X.Modules 0 ⋙
          (Scheme.Modules.pushforward f).rightDerivedFunctorPlus :=
  relativeCechIsoDerivedPushforward f 𝒰
    (fun i ↦ isAffineHom_pi_hom_of_members 𝒰 i hm)
    (fun i ↦ isAffineHom_pi_hom_comp_of_members f 𝒰 i hm hmf)

end Stacks.AlgebraicGeometry.LerayAffineOverBase

end
