module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Module
public import StacksFrontier.AlgebraicGeometry.Discriminant.FactorizationRefinement

/-!
# Moving a relative dualizing module along the target

The relative dualizing module of a finite-open factorization is a tensor product over the
intermediate algebra, so a change of the target carries it along. This file records the three
changes of target that the localization theory of relative dualizing modules needs: transport
along an algebra isomorphism, scalar extension to an away localization, and the identification
of the scalar extension of the target to a localization of the base in which the localizing
element is already invertible.

## Main definitions

* `Stacks.Discriminant.dualizingModuleTensorEquiv` identifies the relative dualizing module with
  the tensor product defining it.
* `Stacks.Discriminant.dualizingModule_retargetEquiv` transports the relative dualizing module
  along an algebra isomorphism of the target.
* `Stacks.Discriminant.targetLocalizationMap` is the canonical map into the scalar extension of
  the relative dualizing module along an away localization of the target, which
  `Stacks.Discriminant.targetLocalizationMap_isLocalized` identifies with the localized module.
* `Stacks.Discriminant.dualizingTensorLocalizationEquiv` identifies that scalar extension with
  the relative dualizing module of the localized factorization.
* `Stacks.Discriminant.baseChangeTargetEquiv` identifies the scalar extension of the target to a
  localization of the base away from an element already invertible in the target.

## Main results

* `Stacks.Discriminant.dualizingModule_retargetEquiv_tmul` and
  `Stacks.Discriminant.dualizingTensorLocalizationEquiv_tmul` compute the transport along an
  isomorphism of the target and the identification of the scalar extension on pure tensors.

## Implementation notes

The module structures are transported across the symmetry of the tensor product, as in the
construction of the relative dualizing module itself, so the identifications are built from
additive equivalences together with the compatibility of the scalar action.

## References

* [Stacks Project, Tag 0BT2](https://stacks.math.columbia.edu/tag/0BT2)
-/

@[expose] public section

namespace Stacks.Discriminant

universe u v w x y

open Topology
open scoped TensorProduct

/-- The relative dualizing module is by definition a tensor product; this is the identification
of the two, as a linear equivalence over the target. -/
noncomputable def dualizingModuleTensorEquiv
    {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, x} A B) :
    letI : CommRing F.middle := F.commRingMiddle
    letI : Algebra A F.middle := F.algebraMiddle
    letI : Algebra F.middle B := F.algebraTarget
    letI : IsScalarTower A F.middle B := F.scalarTower
    letI : Module F.middle (Module.Dual A F.middle) :=
      algebraDualModule A F.middle
    letI : AddCommGroup (Module.Dual A F.middle ⊗[F.middle] B) := by
      change AddCommGroup (dualizingModule F)
      exact dualizingModule.instAddCommGroup F
    letI : Module B (Module.Dual A F.middle ⊗[F.middle] B) :=
      dualizingModule.instModule F
    dualizingModule F ≃ₗ[B] Module.Dual A F.middle ⊗[F.middle] B := by
  let C := F.middle
  letI : CommRing C := F.commRingMiddle
  letI : Algebra A C := F.algebraMiddle
  letI : Algebra C B := F.algebraTarget
  letI : IsScalarTower A C B := F.scalarTower
  let M := Module.Dual A C
  letI : Module C M := algebraDualModule A C
  letI : Module B (B ⊗[C] M) := TensorProduct.leftModule
  letI : AddCommGroup (M ⊗[C] B) := by
    change AddCommGroup (dualizingModule F)
    exact dualizingModule.instAddCommGroup F
  letI : Module B (M ⊗[C] B) := dualizingModule.instModule F
  let eAdd : dualizingModule F ≃+ (M ⊗[C] B) := {
    toFun := fun m => m
    invFun := fun m => m
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl }
  exact eAdd.toLinearEquiv fun _ _ => rfl

/-- The identification of the relative dualizing module with its underlying tensor product
sends a pure tensor to the corresponding pure tensor. -/
theorem dualizingModuleTensorEquiv_tmul
    {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, x} A B)
    (φ : Module.Dual A F.middle) (b : B) :
    letI : CommRing F.middle := F.commRingMiddle
    letI : Algebra A F.middle := F.algebraMiddle
    letI : Algebra F.middle B := F.algebraTarget
    letI : IsScalarTower A F.middle B := F.scalarTower
    letI : Module F.middle (Module.Dual A F.middle) :=
      algebraDualModule A F.middle
    letI : AddCommGroup (Module.Dual A F.middle ⊗[F.middle] B) := by
      change AddCommGroup (dualizingModule F)
      exact dualizingModule.instAddCommGroup F
    letI : Module B (Module.Dual A F.middle ⊗[F.middle] B) :=
      dualizingModule.instModule F
    (dualizingModuleTensorEquiv F).toFun (dualizingModule.tmul F φ b) =
      φ ⊗ₜ[F.middle] b := rfl

/-- Transporting a finite-open factorization along an algebra isomorphism of its target
transports its relative dualizing module along the same isomorphism. -/
noncomputable def dualizingModule_retargetEquiv
    {A : Type u} {D : Type v} {B : Type w}
    [CommRing A] [CommRing D] [CommRing B] [Algebra A D] [Algebra A B] [Algebra B D]
    (F : FiniteOpenFactorization.{u, v, x} A D) (e : D ≃ₐ[A] B)
    (he : ∀ b : B, e (algebraMap B D b) = b) :
    letI : Module B (dualizingModule F) :=
      Module.compHom _ (algebraMap B D)
    letI : AddCommGroup (dualizingModule (retargetFactorization F e)) :=
      dualizingModule.instAddCommGroup (retargetFactorization F e)
    letI : Module B (dualizingModule (retargetFactorization F e)) :=
      dualizingModule.instModule (retargetFactorization F e)
    dualizingModule F ≃ₗ[B] dualizingModule (retargetFactorization F e) := by
  let F' := retargetFactorization F e
  let C := F.middle
  letI : CommRing C := F.commRingMiddle
  letI : Algebra A C := F.algebraMiddle
  letI : Algebra C D := F.algebraTarget
  letI : IsScalarTower A C D := F.scalarTower
  letI : Algebra C B := F'.algebraTarget
  letI : IsScalarTower A C B := F'.scalarTower
  letI : IsScalarTower C B D := IsScalarTower.of_algebraMap_eq' (by
    ext c
    apply e.injective
    calc
      e (algebraMap C D c) = algebraMap C B c := rfl
      _ = e (algebraMap B D (algebraMap C B c)) := (he _).symm
      )
  letI : Module D (dualizingModule F) := dualizingModule.instModule F
  letI : Module B (dualizingModule F) := Module.compHom _ (algebraMap B D)
  let eC : D ≃ₐ[C] B := AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun _ => rfl)
  let M := Module.Dual A C
  letI : Module C M := algebraDualModule A C
  letI : AddCommGroup (M ⊗[C] D) := by
    change AddCommGroup (dualizingModule F)
    exact dualizingModule.instAddCommGroup F
  letI : AddCommGroup (M ⊗[C] B) := by
    change AddCommGroup (dualizingModule F')
    exact dualizingModule.instAddCommGroup F'
  letI : Module D (M ⊗[C] D) :=
    (TensorProduct.comm C M D).toAddEquiv.module D
  letI : Module B (M ⊗[C] B) :=
    (TensorProduct.comm C M B).toAddEquiv.module B
  let eTensor : (M ⊗[C] D) ≃ₗ[C] (M ⊗[C] B) :=
    LinearEquiv.lTensor M eC.toLinearEquiv
  let eAdd : dualizingModule F ≃+ dualizingModule F' := {
    toFun := fun z => eTensor z
    invFun := fun z => eTensor.symm z
    left_inv := eTensor.left_inv
    right_inv := eTensor.right_inv
    map_add' := eTensor.map_add }
  exact eAdd.toLinearEquiv (by
    intro b z
    change eTensor ((algebraMap B D b) • z) = b • eTensor z
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' =>
      calc
        eTensor ((algebraMap B D b) • (z + z')) =
            eTensor ((algebraMap B D b) • z + (algebraMap B D b) • z') := by
          rw [smul_add]
        _ = eTensor ((algebraMap B D b) • z) +
            eTensor ((algebraMap B D b) • z') := eTensor.map_add _ _
        _ = b • eTensor z + b • eTensor z' := congrArg₂ (· + ·) hz hz'
        _ = b • eTensor (z + z') := by rw [eTensor.map_add, ← smul_add]
    | tmul φ d =>
      change eTensor ((TensorProduct.comm C M D).symm
          ((algebraMap B D b) • (d ⊗ₜ[C] φ))) =
        (TensorProduct.comm C M B).symm (b • (e d ⊗ₜ[C] φ))
      simp only [TensorProduct.smul_tmul', TensorProduct.comm_symm_tmul,
        Algebra.smul_def]
      change eTensor (φ ⊗ₜ[C] ((algebraMap B D b) * d)) =
        φ ⊗ₜ[C] (b * e d)
      have hPure : eTensor (φ ⊗ₜ[C] ((algebraMap B D b) * d)) =
          φ ⊗ₜ[C] eC ((algebraMap B D b) * d) := by
        simp [eTensor]
      have hb' : eC (algebraMap B D b) = b := he b
      have hcoeff : eC ((algebraMap B D b) * d) = b * e d :=
        calc
          eC ((algebraMap B D b) * d) =
              eC (algebraMap B D b) * eC d := map_mul eC.toRingHom _ _
          _ = b * e d := by rw [hb']; rfl
      rw [hPure, hcoeff])

/-- The transport of the relative dualizing module along an algebra isomorphism of the target
carries a pure tensor to the pure tensor with transported coefficient. -/
theorem dualizingModule_retargetEquiv_tmul
    {A : Type u} {D : Type v} {B : Type w}
    [CommRing A] [CommRing D] [CommRing B] [Algebra A D] [Algebra A B] [Algebra B D]
    (F : FiniteOpenFactorization.{u, v, x} A D) (e : D ≃ₐ[A] B)
    (he : ∀ b : B, e (algebraMap B D b) = b)
    (φ : Module.Dual A F.middle) (d : D) :
    let : Module B (dualizingModule F) :=
      Module.compHom _ (algebraMap B D)
    let : AddCommGroup (dualizingModule (retargetFactorization F e)) :=
      dualizingModule.instAddCommGroup (retargetFactorization F e)
    let : Module B (dualizingModule (retargetFactorization F e)) :=
      dualizingModule.instModule (retargetFactorization F e)
    dualizingModule_retargetEquiv F e he (dualizingModule.tmul F φ d) =
      dualizingModule.tmul (retargetFactorization F e) φ (e d) := rfl

/-- The scalar extension of the relative dualizing module to an away localization of the target
is the relative dualizing module of the localized factorization. -/
noncomputable def dualizingTensorLocalizationEquiv
    {A : Type u} {B : Type v} {Bg : Type w}
    [CommRing A] [CommRing B] [CommRing Bg]
    [Algebra A B] [Algebra B Bg] [Algebra A Bg] [IsScalarTower A B Bg]
    (g : B) [IsLocalization.Away g Bg]
    (F : FiniteOpenFactorization.{u, v, x} A B) :
    Bg ⊗[B] (dualizingModule F) ≃ₗ[Bg] dualizingModule (locFact (Bg := Bg) g F) := by
  let C := F.middle
  letI : CommRing C := F.commRingMiddle
  letI : Algebra A C := F.algebraMiddle
  letI : Algebra C B := F.algebraTarget
  letI : IsScalarTower A C B := F.scalarTower
  letI : Module.Finite A C := F.finite_middle
  letI : Algebra C Bg := (locFact (Bg := Bg) g F).algebraTarget
  letI : IsScalarTower C B Bg := IsScalarTower.of_algebraMap_eq' (by
    ext c
    rfl)
  letI : IsScalarTower A C Bg := (locFact (Bg := Bg) g F).scalarTower
  let FLoc := locFact (Bg := Bg) g F
  letI : CommRing FLoc.middle := FLoc.commRingMiddle
  letI : Algebra A FLoc.middle := FLoc.algebraMiddle
  letI : Module FLoc.middle (Module.Dual A FLoc.middle) :=
    algebraDualModule A FLoc.middle
  let M := Module.Dual A C
  letI : Module C M := algebraDualModule A C
  let es := TensorProduct.comm C M B
  letI : AddCommGroup (M ⊗[C] B) := by
    change AddCommGroup (dualizingModule F)
    exact dualizingModule.instAddCommGroup F
  letI : Module B (M ⊗[C] B) := dualizingModule.instModule F
  letI : Module B (B ⊗[C] M) := TensorProduct.leftModule
  let eSwapRaw : (M ⊗[C] B) ≃ₗ[B] B ⊗[C] M :=
    es.toAddEquiv.toLinearEquiv (by
      intro b z
      change es.toAddEquiv (es.toAddEquiv.symm (b • es.toAddEquiv z)) = _
      exact es.toAddEquiv.apply_symm_apply _)
  let eSwap := (dualizingModuleTensorEquiv F).trans eSwapRaw
  let eBase := eSwap.baseChange B Bg
  let eCancel := TensorProduct.AlgebraTensorModule.cancelBaseChange C B Bg Bg M
  let eTgt := eBase.trans eCancel
  let eComm := TensorProduct.comm C Bg M
  letI : Module Bg (M ⊗[C] Bg) := dualizingModule.instModule (locFact (Bg := Bg) g F)
  let eComm' : Bg ⊗[C] M ≃ₗ[Bg] dualizingModule (locFact (Bg := Bg) g F) :=
    eComm.toAddEquiv.toLinearEquiv (by
      intro b z
      change eComm (b • z) = eComm (b • eComm.symm (eComm z))
      rw [eComm.symm_apply_apply])
  exact eTgt.trans eComm'

/-- The canonical map from the relative dualizing module into its scalar extension along an
away localization of the target. -/
def targetLocalizationMap
    {A : Type u} {B : Type v} {Bg : Type w}
    [CommRing A] [CommRing B] [CommRing Bg]
    [Algebra A B] [Algebra B Bg] [Algebra A Bg] [IsScalarTower A B Bg]
    (g : B) [IsLocalization.Away g Bg]
    (F : FiniteOpenFactorization.{u, v, x} A B) :
    dualizingModule F →ₗ[B] Bg ⊗[B] (dualizingModule F) :=
  TensorProduct.mk B Bg (dualizingModule F) 1

/-- The canonical map into the scalar extension of the relative dualizing module along an away
localization of the target exhibits that scalar extension as the localized module. -/
theorem targetLocalizationMap_isLocalized
    {A : Type u} {B : Type v} {Bg : Type w}
    [CommRing A] [CommRing B] [CommRing Bg]
    [Algebra A B] [Algebra B Bg] [Algebra A Bg] [IsScalarTower A B Bg]
    (g : B) [IsLocalization.Away g Bg]
    (F : FiniteOpenFactorization.{u, v, x} A B) :
    IsLocalizedModule (Submonoid.powers g) (targetLocalizationMap (Bg := Bg) g F) :=
  IsLocalization.tensorProduct_isLocalizedModule
    (R := B) (S := Submonoid.powers g) (A := Bg) (M := dualizingModule F)

/-- The scalar extension of the relative dualizing module to an away localization of the target
carries a pure tensor to the pure tensor with localized coefficient. -/
theorem dualizingTensorLocalizationEquiv_tmul
    {A : Type u} {B : Type v} {Bg : Type w}
    [CommRing A] [CommRing B] [CommRing Bg]
    [Algebra A B] [Algebra B Bg] [Algebra A Bg] [IsScalarTower A B Bg]
    (g : B) [IsLocalization.Away g Bg]
    (F : FiniteOpenFactorization.{u, v, x} A B)
    (φ : Module.Dual A F.middle) (b : B) :
    dualizingTensorLocalizationEquiv (Bg := Bg) g F
      (targetLocalizationMap (Bg := Bg) g F (dualizingModule.tmul F φ b)) =
      dualizingModule.tmul (locFact (Bg := Bg) g F) φ (algebraMap B Bg b) := by
  let C := F.middle
  let : CommRing C := F.commRingMiddle
  let : Algebra A C := F.algebraMiddle
  let : Algebra C B := F.algebraTarget
  let : IsScalarTower A C B := F.scalarTower
  let : Module.Finite A C := F.finite_middle
  let : Algebra C Bg := (locFact (Bg := Bg) g F).algebraTarget
  let : IsScalarTower C B Bg := IsScalarTower.of_algebraMap_eq' (by
    ext c
    rfl)
  let : IsScalarTower A C Bg := (locFact (Bg := Bg) g F).scalarTower
  let FLoc := locFact (Bg := Bg) g F
  let : CommRing FLoc.middle := FLoc.commRingMiddle
  let : Algebra A FLoc.middle := FLoc.algebraMiddle
  let : Module FLoc.middle (Module.Dual A FLoc.middle) :=
    algebraDualModule A FLoc.middle
  let M := Module.Dual A C
  let : Module C M := algebraDualModule A C
  let : AddCommGroup (M ⊗[C] B) := by
    change AddCommGroup (dualizingModule F)
    exact dualizingModule.instAddCommGroup F
  let : Module B (M ⊗[C] B) := dualizingModule.instModule F
  let : Module B (B ⊗[C] M) := TensorProduct.leftModule
  let eSwap : dualizingModule F ≃ₗ[B] B ⊗[C] M := (dualizingModuleTensorEquiv F).trans
    ((TensorProduct.comm C M B).toAddEquiv.toLinearEquiv fun _ _ =>
      (TensorProduct.comm C M B).toAddEquiv.apply_symm_apply _)
  let eBase := eSwap.baseChange B Bg
  let eCancel := TensorProduct.AlgebraTensorModule.cancelBaseChange C B Bg Bg M
  let eComm := TensorProduct.comm C Bg M
  let : Module Bg (M ⊗[C] Bg) :=
    dualizingModule.instModule FLoc
  let eComm' : Bg ⊗[C] M ≃ₗ[Bg] dualizingModule FLoc :=
    eComm.toAddEquiv.toLinearEquiv fun b z =>
      congrArg eComm (congrArg (b • ·) (eComm.symm_apply_apply z).symm)
  change ((eBase.trans eCancel).trans eComm')
    (1 ⊗ₜ[B] (dualizingModule.tmul F φ b)) =
      dualizingModule.tmul FLoc φ (algebraMap B Bg b)
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul]
  have hSwap : eSwap (dualizingModule.tmul F φ b) = b ⊗ₜ[C] φ := by
    change (TensorProduct.comm C M B) ((dualizingModuleTensorEquiv F).toFun
      (dualizingModule.tmul F φ b)) = _
    rw [dualizingModuleTensorEquiv_tmul]
    exact TensorProduct.comm_tmul C M B φ b
  rw [hSwap]
  change eComm' (eCancel (1 ⊗ₜ[B] (b ⊗ₜ[C] φ))) = _
  rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
  change eComm ((b • (1 : Bg)) ⊗ₜ[C] φ) = _
  rw [TensorProduct.comm_tmul]
  congr 1
  simp [Algebra.smul_def]

/-- If the base is replaced by its localization away from `f`, and `f` is already invertible in
the target, then the scalar extension of the target to that localization is the target itself. -/
noncomputable def baseChangeTargetEquiv
    {A : Type u} {B : Type v} {Af : Type w}
    [CommRing A] [CommRing B] [CommRing Af]
    [Algebra A B] [Algebra A Af] [Algebra Af B] [IsScalarTower A Af B]
    (f : A) [IsLocalization.Away f Af] :
    letI : Algebra B (Af ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    Af ⊗[A] B ≃ₐ[B] B := by
  let g := algebraMap A B f
  have hg : IsUnit g := by
    change IsUnit (algebraMap A B f)
    rw [IsScalarTower.algebraMap_apply A Af B f]
    exact (IsLocalization.Away.algebraMap_isUnit (R := A) (S := Af) f).map (algebraMap Af B)
  letI : Algebra B (Af ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  letI : IsLocalization.Away g B :=
    IsLocalization.away_of_isUnit_of_bijective (S := B) (r := g) hg Function.bijective_id
  letI : Algebra B (B ⊗[A] Af) := Algebra.TensorProduct.leftAlgebra
  letI : IsScalarTower A B (B ⊗[A] Af) := IsScalarTower.of_algebraMap_eq' (by
    ext a
    simp [Algebra.TensorProduct.algebraMap_apply])
  let eSwapRing : (Af ⊗[A] B) ≃+* (B ⊗[A] Af) :=
    (Algebra.TensorProduct.comm A Af B).toRingEquiv
  let eSwap : Af ⊗[A] B ≃ₐ[B] B ⊗[A] Af :=
    AlgEquiv.ofRingEquiv (f := eSwapRing) (by
      intro b
      change Algebra.TensorProduct.comm A Af B (1 ⊗ₜ[A] b) = b ⊗ₜ[A] 1
      simp)
  let eTensor : B ⊗[A] Af ≃ₐ[B] Localization.Away g :=
    IsLocalization.Away.tensorEquiv (R := A) (S := B) f Af
  let eAway : Localization.Away g ≃ₐ[B] B :=
    IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) B
  exact eSwap.trans (eTensor.trans eAway)

end Stacks.Discriminant
