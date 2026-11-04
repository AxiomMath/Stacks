module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.DegreeZeroTranspose
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethExtPureMapInvertibility

/-!
# The pure-tensor law of the degree-zero Künneth chain
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

open Stacks.Cohomology.GlobalKunneth (baseRing sectionsOverBase)
open Stacks.Cohomology.DerivedKunnethExt (boxSheafHomMap boxProd sheafHomObj tensorMap
  derivedPullbackFunctor sheafHomEvalEquiv)

variable (k : Type u) [Field k]

section Law

variable (X Y : Over (Spec (.of k)))

/-- The morphism `u ≫ (Lp^*t_K ⊗ Lq^*t_M) ≫ boxSheafHomMap : 𝒪_W ⟶ R𝓗om(K ⊠ M, K ⊠ M)`, with `u`
the unit of the degree-zero Künneth map on classes and `t_K`, `t_M` the transposes of the
identities. -/
abbrev pureTensorUnit (K : DerivedCategory X.left.Modules) (M : DerivedCategory Y.left.Modules) :
    structureSheafObj k (fibreProductOver k X Y) ⟶
      sheafHomObj (pullback X.hom Y.hom).toRingedSpace
        (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
          (pullback.snd X.hom Y.hom).toLRSHom.toShHom K M)
        (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
          (pullback.snd X.hom Y.hom).toLRSHom.toShHom K M) :=
  degreeZeroKunnethUnit k X Y ≫
    tensorMap (pullback X.hom Y.hom).toRingedSpace
        ((derivedPullbackFunctor (pullback.fst X.hom Y.hom).toLRSHom.toShHom).map
          (homTranspose k X K K (𝟙 K)))
        ((derivedPullbackFunctor (pullback.snd X.hom Y.hom).toLRSHom.toShHom).map
          (homTranspose k Y M M (𝟙 M))) ≫
      boxSheafHomMap (pullback.fst X.hom Y.hom).toLRSHom.toShHom
        (pullback.snd X.hom Y.hom).toLRSHom.toShHom K K M M

/-- Postcomposition with `pureTensorUnit` and `R𝓗om(K ⊠ M, -)`, additively. -/
def pureTensorPostcomp (K K' : DerivedCategory X.left.Modules)
    (M M' : DerivedCategory Y.left.Modules) :
    ((boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
        (pullback.snd X.hom Y.hom).toLRSHom.toShHom K M) ⟶
      (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
        (pullback.snd X.hom Y.hom).toLRSHom.toShHom K' M')) →+
      (structureSheafObj k (fibreProductOver k X Y) ⟶
        (derivedSheafHomObj k (fibreProductOver k X Y)
          (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
            (pullback.snd X.hom Y.hom).toLRSHom.toShHom K M)
          (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
            (pullback.snd X.hom Y.hom).toLRSHom.toShHom K' M'))) :=
  AddMonoidHom.mk' (fun χ => pureTensorUnit k X Y K M ≫
      ((Stacks.SheafOfModules.derivedSheafHom (pullback X.hom Y.hom).toRingedSpace.sheaf).obj
        (op (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
          (pullback.snd X.hom Y.hom).toLRSHom.toShHom K M))).map χ) (fun χ χ' =>
    Stacks.Cohomology.DerivedKunnethExt.comp_map_add _ (pureTensorUnit k X Y K M) χ χ')

/-- **The reading of `Hom(K ⊠ M, K' ⊠ M')` in `H⁰RΓ(W, R𝓗om(K ⊠ M, K' ⊠ M'))`**:
`χ ↦ cls(pureTensorUnit ≫ R𝓗om(K ⊠ M, χ))`. -/
def pureTensorReading (K K' : DerivedCategory X.left.Modules)
    (M M' : DerivedCategory Y.left.Modules) :
    ((boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
        (pullback.snd X.hom Y.hom).toLRSHom.toShHom K M) ⟶
      (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
        (pullback.snd X.hom Y.hom).toLRSHom.toShHom K' M')) →+
      degreeZeroSectionsField k (pullback.fst X.hom Y.hom ≫ X.hom)
        (sheafHomObj (pullback X.hom Y.hom).toRingedSpace
          (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
            (pullback.snd X.hom Y.hom).toLRSHom.toShHom K M)
          (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
            (pullback.snd X.hom Y.hom).toLRSHom.toShHom K' M')) :=
  (degreeZeroClassAddEquiv k (fibreProductOver k X Y)
    (derivedSheafHomObj k (fibreProductOver k X Y)
      (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
        (pullback.snd X.hom Y.hom).toLRSHom.toShHom K M)
      (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
        (pullback.snd X.hom Y.hom).toLRSHom.toShHom K' M'))).toAddMonoidHom.comp
    (pureTensorPostcomp k X Y K K' M M')

/-- `pureTensorReading` sends `χ` to the degree-zero class of
`pureTensorUnit ≫ R𝓗om(K ⊠ M, χ)`. -/
theorem pureTensorReading_apply (K K' : DerivedCategory X.left.Modules)
    (M M' : DerivedCategory Y.left.Modules)
    (χ : (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
        (pullback.snd X.hom Y.hom).toLRSHom.toShHom K M) ⟶
      (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
        (pullback.snd X.hom Y.hom).toLRSHom.toShHom K' M')) :
    pureTensorReading k X Y K K' M M' χ = (degreeZeroClassAddEquiv k (fibreProductOver k X Y)
      (derivedSheafHomObj k (fibreProductOver k X Y)
        (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
          (pullback.snd X.hom Y.hom).toLRSHom.toShHom K M)
        (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
          (pullback.snd X.hom Y.hom).toLRSHom.toShHom K' M')))
      (pureTensorUnit k X Y K M ≫
        ((Stacks.SheafOfModules.derivedSheafHom (pullback X.hom Y.hom).toRingedSpace.sheaf).obj
          (op (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
            (pullback.snd X.hom Y.hom).toLRSHom.toShHom K M))).map χ) :=
  rfl

/-- Composing the transpose of the identity with `R𝓗om(K, φ)` is the transpose, a bijection. -/
private theorem bijective_homTranspose_comp_map (K : DerivedCategory X.left.Modules)
    (T : DerivedCategory X.left.Modules) :
    Function.Bijective (fun φ : K ⟶ T => homTranspose k X K K (𝟙 K) ≫
      ((Stacks.SheafOfModules.derivedSheafHom X.left.toRingedSpace.sheaf).obj (op K)).map φ) := by
  rw [show (fun φ : K ⟶ T => homTranspose k X K K (𝟙 K) ≫
      ((Stacks.SheafOfModules.derivedSheafHom X.left.toRingedSpace.sheaf).obj (op K)).map φ) =
      homTranspose k X K T from funext fun φ => (homTranspose_eq_comp k X K T φ).symm]
  exact ⟨homTranspose_injective k X K T, homTranspose_surjective k X K T⟩

/-- Postcomposition with `pureTensorUnit` is injective, for `X` and `Y` quasi-compact and
quasi-separated: the unit `u` is then invertible (`AlgebraicGeometry.isIso_degreeZeroKunnethUnit`),
the transposes are bijections, and
`Stacks.Cohomology.DerivedKunnethExt.injective_comp_map_boxSheafHomMap` applies. -/
theorem injective_pureTensorUnit_comp_map
    [QuasiCompact X.hom] [QuasiSeparated X.hom] [QuasiCompact Y.hom] [QuasiSeparated Y.hom]
    (K K' : DerivedCategory X.left.Modules) (M M' : DerivedCategory Y.left.Modules) :
    Function.Injective (fun χ : (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
        (pullback.snd X.hom Y.hom).toLRSHom.toShHom K M) ⟶
      (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
        (pullback.snd X.hom Y.hom).toLRSHom.toShHom K' M') => pureTensorUnit k X Y K M ≫
      ((Stacks.SheafOfModules.derivedSheafHom (pullback X.hom Y.hom).toRingedSpace.sheaf).obj
        (op (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
          (pullback.snd X.hom Y.hom).toLRSHom.toShHom K M))).map χ) :=
  Stacks.Cohomology.DerivedKunnethExt.injective_comp_map_boxSheafHomMap
    (pullback.fst X.hom Y.hom).toLRSHom.toShHom (pullback.snd X.hom Y.hom).toLRSHom.toShHom
    (homTranspose k X K K (𝟙 K)) (homTranspose k Y M M (𝟙 M)) (degreeZeroKunnethUnit k X Y)
    (isIso_degreeZeroKunnethUnit k X Y)
    (bijective_homTranspose_comp_map k X K) (bijective_homTranspose_comp_map k Y M)
    (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
      (pullback.snd X.hom Y.hom).toLRSHom.toShHom K' M')

/-- `pureTensorPostcomp` is injective when `X` and `Y` are quasi-compact and
quasi-separated. -/
theorem pureTensorPostcomp_injective
    [QuasiCompact X.hom] [QuasiSeparated X.hom] [QuasiCompact Y.hom] [QuasiSeparated Y.hom]
    (K K' : DerivedCategory X.left.Modules) (M M' : DerivedCategory Y.left.Modules) :
    Function.Injective (pureTensorPostcomp k X Y K K' M M') :=
  injective_pureTensorUnit_comp_map k X Y K K' M M'

/-- **The reading `pureTensorReading` is injective** when `X` and `Y` are quasi-compact and
quasi-separated. -/
theorem pureTensorReading_injective
    [QuasiCompact X.hom] [QuasiSeparated X.hom] [QuasiCompact Y.hom] [QuasiSeparated Y.hom]
    (K K' : DerivedCategory X.left.Modules) (M M' : DerivedCategory Y.left.Modules) :
    Function.Injective (pureTensorReading k X Y K K' M M') := by
  intro χ χ' h
  rw [pureTensorReading_apply, pureTensorReading_apply] at h
  have h' := congrArg (degreeZeroClassAddEquiv k (fibreProductOver k X Y)
    (derivedSheafHomObj k (fibreProductOver k X Y)
      (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
        (pullback.snd X.hom Y.hom).toLRSHom.toShHom K M)
      (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
        (pullback.snd X.hom Y.hom).toLRSHom.toShHom K' M'))).symm h
  rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply] at h'
  exact injective_pureTensorUnit_comp_map k X Y K K' M M' h'

/-- `pureTensorUnit` followed by `R𝓗om(K ⊠ M, φ ⊠ ψ)` is
`u ≫ (Lp^*t_φ ⊗ Lq^*t_ψ) ≫ boxSheafHomMap`: the naturality of `boxSheafHomMap` and of the
transposes in their targets. -/
theorem pureTensorUnit_comp_map (K K' : DerivedCategory X.left.Modules)
    (M M' : DerivedCategory Y.left.Modules) (φ : K ⟶ K') (ψ : M ⟶ M') :
    pureTensorUnit k X Y K M ≫
        ((Stacks.SheafOfModules.derivedSheafHom (pullback X.hom Y.hom).toRingedSpace.sheaf).obj
          (op (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
            (pullback.snd X.hom Y.hom).toLRSHom.toShHom K M))).map
          (tensorMap (pullback X.hom Y.hom).toRingedSpace
            ((derivedPullbackFunctor (pullback.fst X.hom Y.hom).toLRSHom.toShHom).map φ)
            ((derivedPullbackFunctor (pullback.snd X.hom Y.hom).toLRSHom.toShHom).map ψ)) =
      (degreeZeroKunnethUnit k X Y ≫
        boxDerivedMap k X Y (homTranspose k X K K' φ) (homTranspose k Y M M' ψ)) ≫
          boxSheafHomMap (pullback.fst X.hom Y.hom).toLRSHom.toShHom
            (pullback.snd X.hom Y.hom).toLRSHom.toShHom K K' M M' :=
  (Stacks.Cohomology.DerivedKunnethExt.comp_boxSheafHomMap_map_of_eq
    (pullback.fst X.hom Y.hom).toLRSHom.toShHom (pullback.snd X.hom Y.hom).toLRSHom.toShHom
    (homTranspose k X K K (𝟙 K)) (homTranspose k Y M M (𝟙 M)) (degreeZeroKunnethUnit k X Y) φ ψ
    (homTranspose k X K K' φ) (homTranspose k Y M M' ψ)
    (homTranspose_eq_comp k X K K' φ).symm (homTranspose_eq_comp k Y M M' ψ).symm).trans
    (Category.assoc _ _ _).symm

/-- **The pure-tensor law for `pureTensorReading`**: `φ ⊠ ψ` is read as the image of
`[φ] ⊗ [ψ]` under the degree-zero Künneth map followed by `H⁰RΓ` of `boxSheafHomMap`. -/
theorem pureTensorReading_tensorMap (K K' : DerivedCategory X.left.Modules)
    (M M' : DerivedCategory Y.left.Modules) (φ : K ⟶ K') (ψ : M ⟶ M') :
    pureTensorReading k X Y K K' M M'
        (tensorMap (pullback X.hom Y.hom).toRingedSpace
          ((derivedPullbackFunctor (pullback.fst X.hom Y.hom).toLRSHom.toShHom).map φ)
          ((derivedPullbackFunctor (pullback.snd X.hom Y.hom).toLRSHom.toShHom).map ψ)) =
      (degreeZeroBoxSheafHomMap k X.hom Y.hom K K' M M').hom
        ((degreeZeroKunnethMap k X.hom Y.hom (sheafHomObj X.left.toRingedSpace K K')
            (sheafHomObj Y.left.toRingedSpace M M')).hom
          (homLinearEquivDegreeZeroSections k X K K' φ ⊗ₜ
            homLinearEquivDegreeZeroSections k Y M M' ψ)) := by
  have hU1 := degreeZeroClassAddEquiv_comp k (fibreProductOver k X Y)
    (degreeZeroKunnethUnit k X Y ≫
      boxDerivedMap k X Y (homTranspose k X K K' φ) (homTranspose k Y M M' ψ))
    (boxSheafHomMap (pullback.fst X.hom Y.hom).toLRSHom.toShHom
      (pullback.snd X.hom Y.hom).toLRSHom.toShHom K K' M M')
  have hU2 := degreeZeroKunnethMap_classes k X Y (homTranspose k X K K' φ)
    (homTranspose k Y M M' ψ)
  have h1 := homLinearEquivDegreeZeroSections_eq_class k X K K' φ
  have h2 := homLinearEquivDegreeZeroSections_eq_class k Y M M' ψ
  rw [pureTensorReading_apply, pureTensorUnit_comp_map]
  exact hU1.trans (congrArg (degreeZeroBoxSheafHomMap k X.hom Y.hom K K' M M').hom (hU2.symm.trans
    (congrArg₂ (fun a b => (degreeZeroKunnethMap k X.hom Y.hom
      (sheafHomObj X.left.toRingedSpace K K') (sheafHomObj Y.left.toRingedSpace M M')).hom
        (a ⊗ₜ b)) h1.symm h2.symm)))

/-- **The pure-tensor law of the degree-zero Künneth chain, in the injective form.**  For `X`, `Y`
quasi-compact and quasi-separated over a field `k`, `W = X ×_k Y`, and `K, K' ∈ D(𝒪_X)`,
`M, M' ∈ D(𝒪_Y)`, there is an injective additive map
`D : Hom(K ⊠ M, K' ⊠ M') ⟶ H⁰RΓ(W, R𝓗om(K ⊠ M, K' ⊠ M'))`
under which `φ ⊠ ψ` is the image of `[φ] ⊗ [ψ]` under the degree-zero Künneth map followed by
`H⁰RΓ` of `boxSheafHomMap`: `pureTensorReading`.  This is the conclusion of
`AlgebraicGeometry.exists_injective_degreeZeroPureTensor` without its hypothesis
`AlgebraicGeometry.DegreeZeroPureTensorTransposeLaw`, and it uses no coherence between the unit
constraints of the several tensor products involved. -/
theorem exists_injective_degreeZeroPureTensor_of_qcqs
    [QuasiCompact X.hom] [QuasiSeparated X.hom] [QuasiCompact Y.hom] [QuasiSeparated Y.hom]
    (K K' : DerivedCategory X.left.Modules) (M M' : DerivedCategory Y.left.Modules) :
    ∃ D : ((boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
        (pullback.snd X.hom Y.hom).toLRSHom.toShHom K M) ⟶
      (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
        (pullback.snd X.hom Y.hom).toLRSHom.toShHom K' M')) →+
        degreeZeroSectionsField k (pullback.fst X.hom Y.hom ≫ X.hom)
          (sheafHomObj (pullback X.hom Y.hom).toRingedSpace
            (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
              (pullback.snd X.hom Y.hom).toLRSHom.toShHom K M)
            (boxProd (pullback.fst X.hom Y.hom).toLRSHom.toShHom
              (pullback.snd X.hom Y.hom).toLRSHom.toShHom K' M')),
      Function.Injective D ∧ ∀ (φ : K ⟶ K') (ψ : M ⟶ M'),
        D (tensorMap (pullback X.hom Y.hom).toRingedSpace
            ((derivedPullbackFunctor (pullback.fst X.hom Y.hom).toLRSHom.toShHom).map φ)
            ((derivedPullbackFunctor (pullback.snd X.hom Y.hom).toLRSHom.toShHom).map ψ)) =
          (degreeZeroBoxSheafHomMap k X.hom Y.hom K K' M M').hom
            ((degreeZeroKunnethMap k X.hom Y.hom (sheafHomObj X.left.toRingedSpace K K')
                (sheafHomObj Y.left.toRingedSpace M M')).hom
              (homLinearEquivDegreeZeroSections k X K K' φ ⊗ₜ
                homLinearEquivDegreeZeroSections k Y M M' ψ)) :=
  ⟨pureTensorReading k X Y K K' M M', pureTensorReading_injective k X Y K K' M M',
    pureTensorReading_tensorMap k X Y K K' M M'⟩

attribute [local instance] CategoryTheory.Linear.fullSubcategory
attribute [local instance] isTriangulated_isPerfect_locallySmall

/-- **The Künneth input `himage` of [Stacks, Tag 0G0A] at the standard model**, for `X` and `Y`
quasi-compact and quasi-separated over `k`: the pairing `(a, c) ↦ a ⊠ c` exhibits
`Hom(ℰᵢ ⊠ F(𝒢ᵢ), ℰⱼ ⊠ F(𝒢ⱼ))` as `Hom(ℰᵢ, ℰⱼ) ⊗_k Hom(F(𝒢ᵢ), F(𝒢ⱼ))`.  This is
`AlgebraicGeometry.DiagonalResolution.isTensorPairing_transformedImagePairingStd_of_transposeLaw'`
with the injective reading supplied by
`AlgebraicGeometry.exists_injective_degreeZeroPureTensor_of_qcqs` instead of the transpose law. -/
theorem DiagonalResolution.isTensorPairing_transformedImagePairingStd_of_qcqs
    [QuasiCompact X.hom] [QuasiSeparated X.hom] [QuasiCompact Y.hom] [QuasiSeparated Y.hom]
    (R : DiagonalResolution X.hom)
    (F : perfectDerived X.left ⥤ perfectDerived Y.left) [F.CommShift ℤ] (hff : F.FullyFaithful)
    (i j : ℕ) :
    letI : Linear k X.left.Modules := modulesLinear k X
    letI : Linear k Y.left.Modules := modulesLinear k Y
    IsTensorPairing k (R.left i ⟶ R.left j)
      (R.secondFactorImageStd F i ⟶ R.secondFactorImageStd F j)
      (R.transformedImagePairingStd Y.hom F i j) := by
  let : Linear k X.left.Modules := modulesLinear k X
  let : Linear k Y.left.Modules := modulesLinear k Y
  obtain ⟨D, hD, hDlaw⟩ := exists_injective_degreeZeroPureTensor_of_qcqs k X Y
    ((DerivedCategory.singleFunctor X.left.Modules 0).obj (R.left i))
    ((DerivedCategory.singleFunctor X.left.Modules 0).obj (R.left j))
    (R.secondFactorImageStd F i) (R.secondFactorImageStd F j)
  refine isTensorPairing_of_degreeZeroKunneth k X.hom Y.hom
    (P := derivedExternalTensorStd X.hom Y.hom (R.firstFactorStd i) (R.secondFactorImageStd F i) ⟶
      derivedExternalTensorStd X.hom Y.hom (R.firstFactorStd j) (R.secondFactorImageStd F j))
    ((DerivedCategory.singleFunctor X.left.Modules 0).obj (R.left i))
    ((DerivedCategory.singleFunctor X.left.Modules 0).obj (R.left j))
    (R.secondFactorImageStd F i) (R.secondFactorImageStd F j)
    (isPerfect_singleFunctor_of_isFiniteLocallyFree_std _ _ (R.isFiniteLocallyFree_left i))
    (R.isPerfect_secondFactorImageStd F i)
    (R.isQCohAll_derivedSheafHom_left i j)
    (R.isQCohAll_derivedSheafHom_secondFactorImageStd F i j)
    (fun p hp => R.isZero_homology_sectionsOverBase_derivedSheafHom_left k i j p hp)
    (fun p hp => R.isZero_homology_sectionsOverBase_derivedSheafHom_secondFactorImageStd F hff
      Y.hom i j p hp)
    (singleFunctorHomLinearEquiv k _ _ ≪≫ₗ homLinearEquivDegreeZeroSections k X _ _)
    (homLinearEquivDegreeZeroSections k Y _ _)
    D hD
    _ fun a c => ?_
  rw [R.transformedImagePairingStd_of_eq_tensorMap]
  exact hDlaw _ _

end Law

section Situation

attribute [-instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Linear.fullSubcategory
attribute [local instance] isTriangulated_isPerfect_locallySmall

variable (X Y : Over (Spec (.of k)))

/-- **`himage` of [Stacks, Tag 0G0A] at the standard model, at the hypotheses of Situation
[Stacks, Tag 0G08]**: `k` a field, `X` and `Y` smooth and proper over `k`, and `F` a `k`-linear,
exact, fully faithful functor between the perfect derived categories.  (Smoothness and the
`k`-linearity of `F` are not used; properness is used only through quasi-compactness and
quasi-separatedness.) -/
theorem DiagonalResolution.isTensorPairing_transformedImagePairingStd
    [Smooth X.hom] [Smooth Y.hom] [IsProper X.hom] [IsProper Y.hom] :
    letI : Linear k X.left.Modules := modulesLinear k X
    letI : Linear k Y.left.Modules := modulesLinear k Y
    ∀ (F : perfectDerived X.left ⥤ perfectDerived Y.left) [F.CommShift ℤ] [F.IsTriangulated],
      F.Linear k → Nonempty F.FullyFaithful →
      ∀ (R : DiagonalResolution X.hom) (i j : ℕ),
        IsTensorPairing k (R.left i ⟶ R.left j)
          (R.secondFactorImageStd F i ⟶ R.secondFactorImageStd F j)
          (R.transformedImagePairingStd Y.hom F i j) := by
  intro F _ _ _ hff R i j
  exact R.isTensorPairing_transformedImagePairingStd_of_qcqs k X Y F hff.some i j

end Situation

end AlgebraicGeometry

end
