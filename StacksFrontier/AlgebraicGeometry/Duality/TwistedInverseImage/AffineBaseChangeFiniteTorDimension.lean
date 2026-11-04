module

public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.DirectImageInDerivedCategory
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.AffineBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.AffineLocal
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.AffineSchemeTorDimension
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.AffineSchemeTorDimensionAmplitude
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.BoundedBelowTensor
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.BoundedBelowOnARingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.BoundedFlatRepresentative

/-!
# Base change of the twisted inverse image over an affine base: finite Tor dimension

For a cartesian square of quasi-compact and quasi-separated schemes with `g : Y' ⟶ Y` a morphism
of affine schemes of finite Tor dimension, `f` proper, `Y` Noetherian and `f`, `g` Tor
independent, the base change map `L(g')^* a(K) ⟶ a'(Lg^*K)` of [Stacks, Tag 0AA6] is invertible
for every `K ∈ D^+_QCoh(𝒪_Y)`: part (3) of [Stacks, Tag 0AA8].

By `Stacks.Duality.isIso_twistedInverseImageBaseChangeMap_app_of_isIso_compareWithPullbackTensor`
this is the invertibility of the comparison map `Lf^*J ⊗ᴸ a(K) ⟶ a(J ⊗ᴸ K)` at `J = Rg_*𝒪_{Y'}`,
which is `Stacks.Duality.isIso_comparisonMap_of_isGE` once `J` is known to have Tor amplitude
bounded below. For `g` affine `J` is `g_*𝒪_{Y'}` in degree zero, whose Tor amplitude is that of
`Γ(Y', 𝒪)` over `Γ(Y, 𝒪)` ([Stacks, Tag 08E9]).

## Main results

* `Stacks.Duality.exists_hasTorAmplitude_derivedPushforward_structureSheaf` — `Rg_*𝒪_{Y'}` has
  bounded Tor amplitude.
* `Stacks.Duality.isIso_twistedInverseImageBaseChangeMap_app_of_finiteTorDimension` —
  [Stacks, Tag 0AA8] part (3).
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative (structureSheafModule
  hasTorAmplitude_iff_exists_flat_representative isFlat_kernel_id_structureSheafModule
  isFlat_structureSheafModule)

universe u

namespace Stacks.Duality

/-! ### Tor amplitude at the two models -/

section Model

variable {X : Scheme.{u}}

/-- **Tor amplitude does not depend on the model.** An object of `D(𝒪_X)` of Tor amplitude in
`[a, b]` at the standard model has Tor amplitude in `[a, b]` at the locally small model: both
are the existence of a representing complex of flat modules vanishing outside `[a, b]`
([Stacks, Tag 08CI]). -/
theorem hasTorAmplitude_of_hasTorAmplitude_standard (E : DerivedCategory X.Modules) (a b : ℤ)
    (hab : a ≤ b)
    (h : @Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
      (PerfectApproximation.standardModel X) E a b) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace E a b := by
  obtain ⟨K, hK, hz, ⟨e⟩⟩ :=
    (@hasTorAmplitude_iff_exists_flat_representative X.toRingedSpace
      (PerfectApproximation.standardModel X) E a b hab).1 h
  exact (hasTorAmplitude_iff_exists_flat_representative E a b hab).2
    ⟨K, hK, hz, ⟨(StacksDraft.DerivedModel.schemeModulesComparison X).functor.mapIso e⟩⟩

/-- **Tensoring with an object of Tor amplitude in `[a, b]` raises lower bounds by `a`** on
`D_QCoh(𝒪_X)`. -/
theorem qcGE_tensor_of_hasTorAmplitude (J : quasiCoherentDerivedCategory X) (a b : ℤ)
    (hJ : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace J.obj a b)
    (m : ℤ) (E : quasiCoherentDerivedCategory X) (hE : QcGE m E) : QcGE (m + a) (J ⊗ E) := by
  have h := Stacks.SheafOfModules.DerivedTensorProduct.isGE_tensor_of_hasTorAmplitudeGE
    (Stacks.Cohomology.TorAmplitude.derTensorSite X.toRingedSpace) J.obj E.obj a m
    (Stacks.Cohomology.TorAmplitude.hasTorAmplitudeGE_of_hasTorAmplitude X.toRingedSpace J.obj a b
      hJ) hE
  show (((@curriedTensor (DerivedCategory X.Modules) _
    (Scheme.Modules.canonicalDerivedMonoidal X)).obj J.obj).obj E.obj).IsGE (m + a)
  rw [curriedTensor_canonicalDerivedMonoidal_eq, add_comm]
  exact h

end Model

/-! ### The Tor amplitude of `Rg_*𝒪_{Y'}` -/

section PushforwardStructureSheaf

variable {Y' Y : Scheme.{u}} [IsAffine Y'] [IsAffine Y] (g : Y' ⟶ Y)

section Standard

attribute [local instance 10000] HasDerivedCategory.standard

/-- At the standard model, `g_*𝒪_{Y'}` in degree zero has finite Tor dimension when the ring map
`Γ(Y, ⊤) ⟶ Γ(Y', ⊤)` does. -/
theorem hasFiniteTorDimension_single_pushforward_structureSheaf_standard
    (hg : HasFiniteTorDimensionRingHom g.appTop.hom) :
    Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension Y.toRingedSpace
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} Y.ringCatSheaf) 0).obj
        ((pushforwardSheafOfModules g).obj (SheafOfModules.unit Y'.ringCatSheaf))) := by
  have hle : (⊤ : Y'.Opens) ≤ g ⁻¹ᵁ ⊤ := by simp
  have happ : g.appLE ⊤ ⊤ hle = g.appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have hφ : let : Algebra Γ(Y, ⊤) Γ(Y', ⊤) := (g.appLE ⊤ ⊤ (by simp)).hom.toAlgebra
      ∃ c d : ℤ, StacksDraft.TorAmplitude.HasTorAmplitudeCanonical Γ(Y, ⊤)
        ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(Y, ⊤)) 0).obj
          ((ModuleCat.restrictScalars (algebraMap Γ(Y, ⊤) Γ(Y', ⊤))).obj
            (ModuleCat.of Γ(Y', ⊤) Γ(Y', ⊤)))) c d := by
    rw [happ]
    exact hg
  have hO : Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension Y'.toRingedSpace
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} Y'.ringCatSheaf) 0).obj
        (SheafOfModules.unit Y'.ringCatSheaf)) := by
    refine ⟨0, 0, (hasTorAmplitude_iff_exists_flat_representative
      _ 0 0 le_rfl).2 ⟨(CochainComplex.singleFunctor _ 0).obj
        (structureSheafModule
          Y'.toRingedSpace), fun i => ?_, fun i hi => ?_, ⟨?_⟩⟩⟩
    · by_cases h : i = 0
      · subst h
        exact Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative.isFlat_of_iso
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).symm
          (isFlat_structureSheafModule _)
      · exact Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative.isFlat_of_iso
          (IsZero.iso (isZero_kernel_of_mono (𝟙 _))
            (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ i h))
          (isFlat_kernel_id_structureSheafModule _)
    · exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ i
        (by rintro rfl; exact hi ⟨le_rfl, le_rfl⟩)
    · exact ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _).symm
  have hqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor Y'.Modules i).obj
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} Y'.ringCatSheaf) 0).obj
        (SheafOfModules.unit Y'.ringCatSheaf))).IsQuasicoherent := by
    intro i
    have hs : ∀ M : Y'.Modules, ((DerivedCategory.singleFunctor Y'.Modules 0).obj M).IsGE 0 ∧
        ((DerivedCategory.singleFunctor Y'.Modules 0).obj M).IsLE 0 :=
      fun M => ⟨inferInstance, inferInstance⟩
    have := (hs (SheafOfModules.unit Y'.ringCatSheaf)).1
    have := (hs (SheafOfModules.unit Y'.ringCatSheaf)).2
    rcases lt_trichotomy i 0 with h | rfl | h
    · exact AlgebraicGeometry.isQuasicoherent_of_isZero Y' _
        (DerivedCategory.isZero_of_isGE (C := Y'.Modules)
        ((DerivedCategory.singleFunctor Y'.Modules 0).obj (SheafOfModules.unit Y'.ringCatSheaf))
          0 i h)
    · exact (SheafOfModules.isQuasicoherent Y'.ringCatSheaf).prop_of_iso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso Y'.Modules 0).app _).symm
        (inferInstance : (SheafOfModules.unit Y'.ringCatSheaf : Y'.Modules).IsQuasicoherent)
    · exact AlgebraicGeometry.isQuasicoherent_of_isZero Y' _
        (DerivedCategory.isZero_of_isLE (C := Y'.Modules)
        ((DerivedCategory.singleFunctor Y'.Modules 0).obj (SheafOfModules.unit Y'.ringCatSheaf))
          0 i h)
  obtain ⟨a, b, hab⟩ :=
    hasFiniteTorDimension_schemeDerivedPushforward_of_isAffine_of_torAmplitude g hφ _ hqc hO
  exact ⟨a, b, Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_of_iso
    (X := Y.toRingedSpace) hab
    (Stacks.AlgebraicGeometry.DerivedAffinePushforward.derivedPushforwardStructureSheafIso g)⟩

end Standard

/-- **`Rg_*𝒪_{Y'}` has bounded Tor amplitude** for a morphism `g` of affine schemes such that
`Γ(Y', ⊤)` has finite Tor dimension over `Γ(Y, ⊤)`. -/
theorem exists_hasTorAmplitude_derivedPushforward_structureSheaf
    (hg : HasFiniteTorDimensionRingHom g.appTop.hom) :
    ∃ a b : ℤ, Stacks.Cohomology.TorAmplitude.HasTorAmplitude Y.toRingedSpace
      ((derivedPushforward g).obj (DerivedPushforward.derivedStructureSheaf Y').obj) a b := by
  obtain ⟨a, b, h⟩ := hasFiniteTorDimension_single_pushforward_structureSheaf_standard g hg
  refine ⟨a, max a b, ?_⟩
  have h' := hasTorAmplitude_of_hasTorAmplitude_standard _ a (max a b) (le_max_left a b)
    (fun F i hi => h F i (fun hi' => hi ⟨hi'.1, le_trans hi'.2 (le_max_right a b)⟩))
  exact Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_of_iso (X := Y.toRingedSpace)
    h' (Stacks.AlgebraicGeometry.DerivedAffinePushforward.derivedPushforwardStructureSheafIso.{u}
      g).symm

end PushforwardStructureSheaf

/-! ### [Stacks, Tag 0AA8] part (3) -/

section BaseChange

variable {X' X Y' Y : Scheme.{u}} [CompactSpace X'] [QuasiSeparatedSpace X'] [CompactSpace X]
  [QuasiSeparatedSpace X] [CompactSpace Y'] [QuasiSeparatedSpace Y'] [CompactSpace Y]
  [QuasiSeparatedSpace Y] {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- **[Stacks, Tag 0AA8] part (3).** In a cartesian square of quasi-compact and quasi-separated
schemes, let `g : Y' ⟶ Y` be a morphism of affine schemes, `f : X ⟶ Y` proper, and `f`, `g` Tor
independent. If `g` has finite Tor dimension and `Y` is Noetherian, the base change map
`L(g')^* a(K) ⟶ a'(Lg^*K)` of [Stacks, Tag 0AA6] is an isomorphism for every
`K ∈ D^+_QCoh(𝒪_Y)`.

For a morphism of affine schemes, having finite Tor dimension means that `Γ(Y', 𝒪)` has finite
Tor dimension as a `Γ(Y, 𝒪)`-module (`AlgebraicGeometry.HasFiniteTorDimensionRingHom` of the map
on global sections): the stalks `𝒪_{Y', y'}` then have Tor dimension bounded uniformly over
`𝒪_{Y, g(y')}`, which is the definition of a morphism of finite Tor dimension; finite Tor
dimension of each stalk separately, without a uniform bound, is weaker. -/
@[stacks 0AA8 "(3)"]
theorem isIso_twistedInverseImageBaseChangeMap_app_of_finiteTorDimension
    (sq : IsPullback g' f' f g) [IsAffine Y] [IsAffine Y'] [IsProper f] [IsNoetherian Y]
    (hTor : TorIndependent f g) (hg : HasFiniteTorDimensionRingHom g.appTop.hom)
    (K : quasiCoherentDerivedCategory Y) (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    haveI := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sq hTor
    IsIso ((twistedInverseImageBaseChangeMap g' f' f g
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
      sq).app K) := by
  refine isIso_twistedInverseImageBaseChangeMap_app_of_isIso_compareWithPullbackTensor sq
    hTor K ?_
  rw [compareWithPullbackTensor_eq_comparisonMap f _ _ (fun _ _ => rfl),
    tensorUnit_quasiCoherentDerivedCategory]
  obtain ⟨b, hb⟩ := hK
  obtain ⟨a, a', ha⟩ := exists_hasTorAmplitude_derivedPushforward_structureSheaf g hg
  have := isIso_comparisonMap_of_isGE f _ K a b
    (qcGE_tensor_of_hasTorAmplitude
      ((quasiCoherentDerivedPushforward g
        (isQuasicoherent_homology_derivedPushforward_of_qcqs g)).obj
        (DerivedPushforward.derivedStructureSheaf Y')) a a' ha)
    ((DerivedCategory.isGE_iff _ _).2 hb)
  infer_instance

end BaseChange

end Stacks.Duality

end
