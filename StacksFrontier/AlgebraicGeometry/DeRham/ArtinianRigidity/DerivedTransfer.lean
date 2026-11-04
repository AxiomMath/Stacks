module

public import StacksFrontier.AlgebraicGeometry.DeRham.PushforwardModuleRefinement
public import StacksFrontier.Topology.Sheaves.Sheaf.AbelianComplexLocality
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativeBaseProjection
public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.AbelianAcyclic
public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.HigherDirectImages
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.LerayDegreewise
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.RightAcyclicProduct.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.RecoveryA.DerivedDirectImageComposition

/-!
# Transfer of `Rf_*Ω^•` along an affine morphism inducing a quasi-isomorphism of de Rham complexes

Let `q : W ⟶ X` be an affine morphism of schemes over `f : X ⟶ S`. If the canonical map of de
Rham complexes `Ω^•_{X/S} ⟶ q_*Ω^•_{W/S}` (`Stacks.DeRhamPullback.deRhamPushforwardChain`, of
`f^{-1}𝒪_S`-modules) is a quasi-isomorphism, then `Rf_*Ω^•_{X/S} ≅ R(q ≫ f)_*Ω^•_{W/S}` in
`D⁺(𝒪_S)` (`Stacks.DeRhamRigidity.derivedDeRhamDirectImageIsoOfQuasiIso`).

The proof combines three facts. The terms of `Ω^•_{W/S}` are quasi-coherent, so they are acyclic
for the direct image along `(W, (q ≫ f)^{-1}𝒪_S) ⟶ (X, f^{-1}𝒪_S)`
(`rightAcyclic_pushforward_relativeBase`, from Tag 01XC read on abelian sheaves and Tag 01F1). So
`q_* = Rq_*` on the de Rham complex, by Leray's acyclicity lemma. Finally, Leray's composition
isomorphism for derived direct images applies (Tag 01F5).
`quasiIso_deRhamPushforwardChain_of_sections` reduces the quasi-isomorphism hypothesis to the
sections over a basis of opens.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.DeRhamDirectImage Stacks.DeRhamSmooth Stacks.DeRhamPullback RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.HigherDirectImage Stacks.Cohomology.ModulePushforwardComparison
open Stacks.Cohomology.LerayLowDegree

universe u

namespace Stacks.DeRhamRigidity

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- The direct image of sheaves of modules along a morphism of ringed spaces is additive. -/
local instance pushforward_additive' {A B : RingedSpace.{u}} (φ : A ⟶ B) :
    (_root_.pushforward φ).Additive :=
  Stacks.Cohomology.DerivedDirectImageComposition.pushforward_additive φ

/-- The direct image of sheaves of modules is left exact. -/
local instance pushforward_preservesFiniteLimits' {A B : RingedSpace.{u}} (φ : A ⟶ B) :
    PreservesFiniteLimits (_root_.pushforward φ) :=
  Stacks.Cohomology.ModulePushforwardComparison.modulePushforward_preservesFiniteLimits φ

/-- A faithful functor preserving zero morphisms reflects zero objects. -/
theorem isZero_of_faithful {C D : Type*} [Category* C] [Category* D] [Preadditive C]
    [Preadditive D] (F : C ⥤ D) [F.Faithful] [F.PreservesZeroMorphisms] {Y : C}
    (h : IsZero (F.obj Y)) : IsZero Y :=
  (IsZero.iff_id_eq_zero _).2 (F.map_injective (by
    rw [F.map_id, F.map_zero]; exact (IsZero.iff_id_eq_zero _).1 h))

variable {W X S : Scheme.{u}} (q : W ⟶ X) (f : X ⟶ S)

/-- **The terms of the de Rham complex of `W` are acyclic for the direct image along
`(W, (q ≫ f)^{-1}𝒪_S) ⟶ (X, f^{-1}𝒪_S)`** when `q` is affine. -/
theorem rightAcyclic_pushforward_relativeBase [IsAffineHom q] (n : ℕ) :
    (_root_.pushforward (relativeBase q f)).rightAcyclic
      ((Scheme.Hom.deRhamComplex (q ≫ f)).X n) := by
  refine (Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived _ _).2
    fun p hp => ?_
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms (q ≫ f) n
  have hab := (Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived _ _).1
    (rightAcyclic_abelianPushforward_toSheaf_of_isAffineHom
      q (Scheme.Hom.relativeDifferentialForms (q ≫ f) (n : ℤ))) p hp
  have hiso := (rightDerived_modulePushforward_forget_iso
    (relativeBase q f) p).app ((Scheme.Hom.deRhamComplex (q ≫ f)).X n)
  have hz := IsZero.of_iso hab hiso
  exact isZero_of_faithful (SheafOfModules.toSheaf (structureSheafRing (inverseImageBase f))) hz

/-- The direct image of the extended de Rham complex is the extension of the direct image. -/
def pushforwardExtendIso :
    (HomologicalComplex.extend (((_root_.pushforward (relativeBase q f)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (Scheme.Hom.deRhamComplex (q ≫ f))) ComplexShape.embeddingUpNat) ≅
      ((_root_.pushforward (relativeBase q f)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (deRhamCochainComplex (q ≫ f)) :=
  HomologicalComplex.mapHomologicalComplexExtendIso (_root_.pushforward (relativeBase q f))
    (show CochainComplex (Modules (inverseImageBase (q ≫ f))) ℕ from
      Scheme.Hom.deRhamComplex (q ≫ f)) ComplexShape.embeddingUpNat

/-- The de Rham complex of `X` over `S` mapped to the direct image of the de Rham complex of `W`,
as `ℤ`-indexed complexes of `f^{-1}𝒪_S`-modules. -/
def deRhamPushforwardInt :
    deRhamCochainComplex f ⟶
      ((_root_.pushforward (relativeBase q f)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (deRhamCochainComplex (q ≫ f)) :=
  HomologicalComplex.extendMap (deRhamPushforwardChain q f) ComplexShape.embeddingUpNat ≫
    (pushforwardExtendIso q f).hom

/-- If the comparison map `Ω^•_{X/S} ⟶ q_*Ω^•_{W/S}` of `ℕ`-indexed complexes is a
quasi-isomorphism, then so is its `ℤ`-indexed extension `deRhamPushforwardInt q f`. -/
theorem quasiIso_deRhamPushforwardInt (h : QuasiIso (deRhamPushforwardChain q f)) :
    QuasiIso (deRhamPushforwardInt q f) := by
  have : QuasiIso (HomologicalComplex.extendMap (deRhamPushforwardChain q f)
      ComplexShape.embeddingUpNat) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ _).2 h
  exact quasiIso_comp (hφ := this) (hφ' := quasiIso_of_isIso (pushforwardExtendIso q f).hom)

/-- Every term of the direct image complex is acyclic: the terms of the `ℤ`-indexed de Rham
complex of `W` are acyclic for the direct image along `relativeBase q f`. -/
theorem rightAcyclic_pushforward_relativeBase_int [IsAffineHom q] (n : ℤ) :
    (_root_.pushforward (relativeBase q f)).rightAcyclic ((deRhamCochainComplex (q ≫ f)).X n) := by
  rcases Int.lt_or_le n 0 with hn | hn
  · exact Stacks.RightAcyclicProduct.rightAcyclic_of_isZero _
      (HomologicalComplex.isZero_extend_X _ _ n (fun i hi => by
        have hi' : (i : ℤ) = n := hi
        omega))
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact Stacks.RightAcyclicProduct.rightAcyclic_of_iso _
      (HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat (i := p) rfl).symm
      (rightAcyclic_pushforward_relativeBase q f p)

open Stacks.Cohomology.DerivedDirectImageComposition in
/-- Leray's composition isomorphism for `(W, (q ≫ f)^{-1}𝒪_S) ⟶ (X, f^{-1}𝒪_S) ⟶ S`, read along
any spelling `g` of the composite. -/
def relativePushforwardCompIso (g : inverseImageBase (q ≫ f) ⟶ S.toRingedSpace)
    (hg : relativeBase q f ≫ inverseImageBaseProjection f = g)
    (Y : DerivedCategory.Plus (Modules (inverseImageBase (q ≫ f)))) :
    (relativePushforward f).rightDerivedFunctorPlus.obj
        ((_root_.pushforward (relativeBase q f)).rightDerivedFunctorPlus.obj Y) ≅
      (_root_.pushforward g).rightDerivedFunctorPlus.obj Y := by
  subst hg
  exact (higherDirectImagesCompIso (relativeBase q f) (inverseImageBaseProjection f)).app Y

/-- The de Rham complex of `W` as a bounded below complex. -/
abbrev deRhamPlus : CochainComplex.Plus (Modules (inverseImageBase (q ≫ f))) :=
  ⟨deRhamCochainComplex (q ≫ f), 0, inferInstance⟩

/-- The direct image of the de Rham complex of `W`, as a bounded below complex. -/
abbrev deRhamPushforwardPlus : CochainComplex.Plus (Modules (inverseImageBase f)) :=
  ⟨((_root_.pushforward (relativeBase q f)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (deRhamCochainComplex (q ≫ f)), 0, inferInstance⟩

/-- The de Rham complex of `X` as a bounded below complex. -/
abbrev deRhamPlusBase : CochainComplex.Plus (Modules (inverseImageBase f)) :=
  ⟨deRhamCochainComplex f, 0, inferInstance⟩

/-- If the comparison map `Ω^•_{X/S} ⟶ q_*Ω^•_{W/S}` is a quasi-isomorphism, then its image
in the bounded below derived category `D⁺(f^{-1}𝒪_S)` is an isomorphism. -/
theorem isIso_Q_map_deRhamPushforwardInt (h : QuasiIso (deRhamPushforwardChain q f)) :
    IsIso (DerivedCategory.Plus.Q.map (X := deRhamPlusBase f) (Y := deRhamPushforwardPlus q f)
      (ObjectProperty.homMk (deRhamPushforwardInt q f))) := by
  have := quasiIso_deRhamPushforwardInt q f h
  have : IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map
      (X := deRhamPlusBase f) (Y := deRhamPushforwardPlus q f)
      (ObjectProperty.homMk (deRhamPushforwardInt q f)))) := by
    show IsIso (DerivedCategory.Q.map (deRhamPushforwardInt q f))
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  exact isIso_of_fully_faithful DerivedCategory.Plus.ι _

/-- The localization of the direct image complex is the direct image functor on the homotopy
category, localized. -/
def qPushforwardIso :
    DerivedCategory.Plus.Q.obj (deRhamPushforwardPlus q f) ≅
      ((_root_.pushforward (relativeBase q f)).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh).obj
        ((HomotopyCategory.Plus.quotient _).obj (deRhamPlus q f)) :=
  DerivedCategory.Plus.ι.preimageIso
    ((DerivedCategory.quotientCompQhIso _).app
      (((_root_.pushforward (relativeBase q f)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (deRhamCochainComplex (q ≫ f)))).symm

/-- The localization of a bounded below complex through the homotopy category. -/
def qhQuotientIso {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (K : CochainComplex.Plus C) :
    DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj K) ≅
      DerivedCategory.Plus.Q.obj K :=
  DerivedCategory.Plus.ι.preimageIso ((DerivedCategory.quotientCompQhIso C).app K.obj)

/-- **The module-level comparison is a quasi-isomorphism as soon as it is one on sections over a
basis of opens**, read on the underlying abelian sheaves. -/
theorem quasiIso_deRhamPushforwardChain_of_sections {𝔅 : Set X.Opens}
    (h𝔅 : TopologicalSpace.Opens.IsBasis 𝔅)
    (hcomm : q ≫ f = (q ≫ f) ≫ 𝟙 S)
    (h : ∀ U ∈ 𝔅, QuasiIso (((abelianSections.{u, u} X.carrier U).mapHomologicalComplex
      (ComplexShape.up ℕ)).map (Scheme.Hom.deRhamAbelianPushforwardMap q f (q ≫ f) (𝟙 S) hcomm))) :
    QuasiIso (deRhamPushforwardChain q f) := by
  have hab := Stacks.AbelianSheaves.quasiIso_of_forall_sections_quasiIso_nat _ h𝔅 h
  rw [deRhamAbelianPushforwardMap_eq_toSheaf_map] at hab
  exact (Stacks.SheafOfModules.quasiIso_toSheaf_map_iff (deRhamPushforwardChain q f)).1 hab

variable [IsAffineHom q]

/-- For `q` affine, the unit of the right derived functor of the direct image along
`relativeBase q f` is an isomorphism at the de Rham complex of `W`, i.e. `q_*Ω^•_{W/S}` computes
`Rq_*Ω^•_{W/S}`. -/
theorem isIso_unit_deRhamPlus :
    IsIso ((_root_.pushforward (relativeBase q f)).rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.quotient _).obj (deRhamPlus q f))) :=
  CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic _ _
    (rightAcyclic_pushforward_relativeBase_int q f)

/-- **Transfer of `Rf_*Ω^•` along an affine morphism.** Let `q : W ⟶ X` be an affine morphism of
schemes over `S` such that the canonical map of de Rham complexes `Ω^•_{X/S} ⟶ q_*Ω^•_{W/S}` is a
quasi-isomorphism. Then `Rf_*Ω^•_{X/S} ≅ R(q ≫ f)_*Ω^•_{W/S}` in `D⁺(𝒪_S)`. -/
def derivedDeRhamDirectImageIsoOfQuasiIso (h : QuasiIso (deRhamPushforwardChain q f)) :
    derivedDeRhamDirectImage f ≅ derivedDeRhamDirectImage (q ≫ f) :=
  haveI := isIso_Q_map_deRhamPushforwardInt q f h
  haveI := isIso_unit_deRhamPlus q f
  (relativePushforward f).rightDerivedFunctorPlus.mapIso
      (asIso (DerivedCategory.Plus.Q.map (X := deRhamPlusBase f) (Y := deRhamPushforwardPlus q f)
          (ObjectProperty.homMk (deRhamPushforwardInt q f))) ≪≫
        qPushforwardIso q f ≪≫
        asIso ((_root_.pushforward (relativeBase q f)).rightDerivedFunctorPlusUnit.app
          ((HomotopyCategory.Plus.quotient _).obj (deRhamPlus q f))) ≪≫
        (_root_.pushforward (relativeBase q f)).rightDerivedFunctorPlus.mapIso
          (qhQuotientIso (deRhamPlus q f))) ≪≫
    relativePushforwardCompIso q f _ (relativeBase_comp_inverseImageBaseProjection q f)
      (DerivedCategory.Plus.Q.obj (deRhamPlus q f))

end Stacks.DeRhamRigidity
