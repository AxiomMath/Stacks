module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.NumberTheory.Cyclotomic.OneAddPow
public import StacksFrontier.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar
public import StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier
public import StacksFrontier.RingTheory.DiscreteValuationRing.BaseChangeClosure
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppSolution
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppMixedReentry
public import StacksFrontier.RingTheory.DiscreteValuationRing.ExtensionLevel
public import StacksFrontier.RingTheory.DiscreteValuationRing.FormallySmoothExtension
public import StacksFrontier.RingTheory.DiscreteValuationRing.Galois
public import StacksFrontier.RingTheory.DiscreteValuationRing.Inertia
public import StacksFrontier.RingTheory.DiscreteValuationRing.IntegralClosureBaseChangeConstruction
public import StacksFrontier.RingTheory.DiscreteValuationRing.Kummer
public import StacksFrontier.RingTheory.DiscreteValuationRing.PurelyInseparable
public import StacksFrontier.RingTheory.DiscreteValuationRing.RamificationIndex
public import StacksFrontier.RingTheory.DiscreteValuationRing.ReducedTensorTower
public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution
public import StacksFrontier.RingTheory.DiscreteValuationRing.Unramified
public import StacksFrontier.RingTheory.DiscreteValuationRing.WeakSolution
public import StacksFrontier.RingTheory.FormallySmooth.Topological
public import StacksFrontier.RingTheory.Nagata.CompleteLocalRing
public import StacksFrontier.RingTheory.IntegralClosure.Pi
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.CompleteIntegralClosure
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.SolvableInertia
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.PurelyInseparableCase
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.IteratedPackages

open Stacks.DegreePExtensionLevel
open Stacks.DiscreteValuationRing.EppLevelInduction

/-!
# Eliminating ramification: the totally ramified tensor-product case

The totally ramified tensor-product case.

Part of `StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue`;
see there for the overview and references.
-/

@[expose] public section

universe uA uB uC uK uL uM

namespace IsDiscreteValuationRing

open scoped TensorProduct

universe uK₁

attribute [local instance]
  IsDiscreteValuationRing.IntegralClosureBaseChange.commRingL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.commRingA₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.commRingB₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraKL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraLL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraBL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraAA₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraA₁K₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraBB₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraB₁L₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraAB₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraA₁B₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerKLL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerBLL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerAA₁K₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerBB₁L₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerABB₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerAA₁B₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isIntegralClosureA₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isIntegralClosureB₁

attribute [local instance]
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraK₁L₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerKK₁L₁

universe uF uD₁ uD₂ uD₃

universe u v

universe uL₁ uA₁ uB₁

/-- The finite-level bound with its input expressed on the given three carriers. -/
theorem exists_extensionLevel_mem_Ico
    (B L M : Type u)
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field L] [Field M] [Algebra B L] [Algebra L M]
    [IsFractionRing B L] [Module.Finite L M]
    (p : ℕ) [Fact p.Prime] (f : CyclotomicRing p ℤ ℚ →+* B)
    (P : Polynomial B) (π : B) (e₁ : ℕ)
    (hfinite : Stacks.DegreePExtensionLevel.IsDegreePExtensionOfFiniteLevel B L M p f P)
    (hπ : Irreducible π) (he₁ : 0 < e₁) (hw : Associated (wElt f) (π ^ e₁)) :
    ∃ hne : (Stacks.DegreePExtensionLevel.extensionLevelNumerators B L M P π).Nonempty,
      Stacks.DegreePExtensionLevel.extensionLevel B L M P π e₁ he₁ hne ∈ Set.Ico (0 : ℚ) (p : ℚ) :=
        by
  apply Exists.imp (fun _ h => h.2)
    (Stacks.DegreePExtensionLevel.exists_extensionLevel_isLeast_and_mem_Ico B L M p f P π e₁ ?_ hπ
      he₁ hw)
  let : Algebra L (ULift.{u} M) := ULift.algebra
  let : Algebra (ULift.{u} L) (ULift.{u} M) := ULift.algebra' L (ULift.{u} M)
  dsimp
  refine ⟨?_, ?_⟩
  · exact (Algebra.finrank_eq_of_equiv_equiv
      (ULift.ringEquiv.{u,u} (R := L)) (ULift.ringEquiv.{u,u} (R := M)) rfl).trans hfinite.1
  · obtain ⟨ξ, z, hz, hP, a, ha, heq⟩ := hfinite.2
    refine ⟨ULift.up ξ, ULift.up z, ?_, ?_, ULift.up a, ?_, ?_⟩
    · rw [Algebra.adjoin_singleton_eq_range_aeval] at hz ⊢
      apply top_unique
      intro y _
      have hy : y.down ∈ (Polynomial.aeval (R := L) z).range := by rw [hz]; trivial
      obtain ⟨q, hq⟩ := hy
      refine ⟨q.map (ULift.ringEquiv.{u,u} (R := L)).symm.toRingHom, ?_⟩
      apply ULift.down_injective
      change (ULift.ringEquiv.{u,u} (R := M)).toRingHom
        (Polynomial.eval₂ (algebraMap (ULift.{u} L) (ULift.{u} M)) (ULift.up z)
          (q.map (ULift.ringEquiv.{u,u} (R := L)).symm.toRingHom)) = y.down
      rw [Polynomial.eval₂_map, Polynomial.hom_eval₂]
      exact hq
    · rw [Polynomial.eval₂_map]
      apply ULift.down_injective
      change (ULift.ringEquiv.{u,u} (R := M)).toRingHom _ = _
      rw [Polynomial.hom_eval₂]
      exact hP
    · intro hu
      exact ha (hu.map (ULift.ringEquiv (R := B)).toRingHom)
    · exact congrArg ULift.up heq

private theorem isWeakSolution_of_iterated_package
    (A B K L K₁ K₂ R : Type*)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁] [Field K₂]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra K K₂] [Algebra K₁ K₂]
    [Algebra A K₂] [IsScalarTower K K₁ K₂]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₂]
    [Module.Finite K K₂] [Module.Finite K₁ K₂]
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra A R] [Algebra.IsIntegral A R]
    [Algebra R K₁] [IsFractionRing R K₁] [Algebra R K₂] [IsScalarTower R K₁ K₂]
    (D₂ : IsDiscreteValuationRing.IntegralClosureBaseChange A B K L K₂)
    (E S : Type*) [Field E] [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra K E] [Algebra K₁ E] [Algebra L E]
    [IsScalarTower K K₁ E]
    [Algebra R S] [IsDiscreteValuationRing.IsExtension R S]
    [Algebra B S] [Algebra.IsIntegral B S]
    [Algebra R E] [Algebra S E]
    [IsFractionRing S E]
    [IsScalarTower R S E] [IsScalarTower R K₁ E]
    (hA : ∀ a : A, algebraMap A K₂ a = algebraMap R K₂ (algebraMap A R a))
    (hB : ∀ b, algebraMap L E (algebraMap B L b) =
      algebraMap S E (algebraMap B S b))
    (hsquare : ∀ a, algebraMap B S (algebraMap A B a) =
      algebraMap R S (algebraMap A R a))
    (D : IsDiscreteValuationRing.IntegralClosureBaseChange R S K₁ E K₂)
    (hD : D.IsWeakSolution) :
    letI : Algebra K₁ (L ⊗[K] K₁) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra K₁ (ReducedTensorTower.Reduction (L ⊗[K] K₁)) :=
      Ideal.Quotient.algebra K₁
    ∀ e : ReducedTensorTower.Reduction (L ⊗[K] K₁) ≃ₐ[K₁] E,
      (∀ x, e (Ideal.Quotient.mk _ (x ⊗ₜ[K] (1 : K₁))) = algebraMap L E x) →
      D₂.IsWeakSolution := by
  let : Algebra K₁ (L ⊗[K] K₁) := Algebra.TensorProduct.rightAlgebra
  let : Algebra K₁ (ReducedTensorTower.Reduction (L ⊗[K] K₁)) :=
    Ideal.Quotient.algebra K₁
  intro e he
  exact isWeakSolution_of_iterated_packages A B K L K₁ K₂ R D₂
    (fun _ : (Fin 1) => E) (fun _ : (Fin 1) => S) hA (fun _ => hB) (fun _ => hsquare)
    (fun _ => D) (fun _ => hD) (e.trans (AlgEquiv.funUnique K₁ (Fin 1) E).symm)
    (fun _ x => he x)

/-- Shared core of the totally ramified tensor-product weak-solution theorems. -/
private theorem exists_finite_extension_isWeakSolution_of_totallyRamified_tensorProduct_aux
    (A B C K L M K₁ : Type u)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M] [Field K₁]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra B M] [Algebra A M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsDiscreteValuationRing.IsExtension A B] [IsDiscreteValuationRing.IsExtension B C]
    [IsDiscreteValuationRing.IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [Module.Finite L M]
    [Algebra K K₁] [Algebra A K₁] [IsScalarTower A K K₁]
    [Module.Finite K K₁] [Algebra.IsSeparable K K₁]
    [PerfectField (IsLocalRing.ResidueField A)]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    (hweak : IsDiscreteValuationRing.IsWeaklyUnramified A B)
    (htot : IsDiscreteValuationRing.IsTotallyRamifiedWithRespectTo A K K₁)
    (hL₁ : IsField (L ⊗[K] K₁)) (hM₁ : IsField (M ⊗[K] K₁))
    (hfinite :
      letI := hL₁.toField
      letI := hM₁.toField
      letI : Algebra (L ⊗[K] K₁) (M ⊗[K] K₁) :=
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M)
          (AlgHom.id K K₁)).toRingHom.toAlgebra
      Module.Finite (L ⊗[K] K₁) (M ⊗[K] K₁))
    (hnext :
      letI := hL₁.toField
      letI := hM₁.toField
      letI : Algebra (L ⊗[K] K₁) (M ⊗[K] K₁) :=
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M)
          (AlgHom.id K K₁)).toRingHom.toAlgebra
      letI : Algebra K₁ (L ⊗[K] K₁) := Algebra.TensorProduct.rightAlgebra
      letI : Algebra K₁ (M ⊗[K] K₁) := Algebra.TensorProduct.rightAlgebra
      let A₁ := integralClosure A K₁
      let B₁ := integralClosure B (L ⊗[K] K₁)
      let C₁ := integralClosure C (M ⊗[K] K₁)
      letI : Algebra A₁ (L ⊗[K] K₁) :=
        ((algebraMap K₁ (L ⊗[K] K₁)).comp (algebraMap A₁ K₁)).toAlgebra
      letI : Algebra A₁ (M ⊗[K] K₁) :=
        ((algebraMap K₁ (M ⊗[K] K₁)).comp (algebraMap A₁ K₁)).toAlgebra
      letI : Algebra B₁ (M ⊗[K] K₁) :=
        ((algebraMap (L ⊗[K] K₁) (M ⊗[K] K₁)).comp
          (algebraMap B₁ (L ⊗[K] K₁))).toAlgebra
      ∀ [IsDiscreteValuationRing A₁] [IsDiscreteValuationRing B₁]
        [IsDiscreteValuationRing C₁]
        [Algebra A₁ B₁] [Algebra B₁ C₁] [Algebra A₁ C₁]
        [@IsScalarTower A₁ B₁ C₁
          (inferInstance : Algebra A₁ B₁).toSMul
          (inferInstance : Algebra B₁ C₁).toSMul
          (inferInstance : Algebra A₁ C₁).toSMul]
        [@IsScalarTower A₁ B₁ (L ⊗[K] K₁)
          (inferInstance : Algebra A₁ B₁).toSMul
          (inferInstance : Algebra B₁ (L ⊗[K] K₁)).toSMul
          (inferInstance : Algebra A₁ (L ⊗[K] K₁)).toSMul]
        [@IsScalarTower A₁ K₁ (L ⊗[K] K₁)
          (inferInstance : Algebra A₁ K₁).toSMul
          (inferInstance : Algebra K₁ (L ⊗[K] K₁)).toSMul
          (inferInstance : Algebra A₁ (L ⊗[K] K₁)).toSMul]
        [@IsScalarTower B₁ C₁ (M ⊗[K] K₁)
          (inferInstance : Algebra B₁ C₁).toSMul
          (inferInstance : Algebra C₁ (M ⊗[K] K₁)).toSMul
          (inferInstance : Algebra B₁ (M ⊗[K] K₁)).toSMul]
        [@IsScalarTower B₁ (L ⊗[K] K₁) (M ⊗[K] K₁)
          (inferInstance : Algebra B₁ (L ⊗[K] K₁)).toSMul
          (inferInstance : Algebra (L ⊗[K] K₁) (M ⊗[K] K₁)).toSMul
          (inferInstance : Algebra B₁ (M ⊗[K] K₁)).toSMul]
        [@IsScalarTower A₁ C₁ (M ⊗[K] K₁)
          (inferInstance : Algebra A₁ C₁).toSMul
          (inferInstance : Algebra C₁ (M ⊗[K] K₁)).toSMul
          (inferInstance : Algebra A₁ (M ⊗[K] K₁)).toSMul]
        [@IsScalarTower A₁ K₁ (M ⊗[K] K₁)
          (inferInstance : Algebra A₁ K₁).toSMul
          (inferInstance : Algebra K₁ (M ⊗[K] K₁)).toSMul
          (inferInstance : Algebra A₁ (M ⊗[K] K₁)).toSMul]
        [@IsScalarTower K₁ (L ⊗[K] K₁) (M ⊗[K] K₁)
          (inferInstance : Algebra K₁ (L ⊗[K] K₁)).toSMul
          (inferInstance : Algebra (L ⊗[K] K₁) (M ⊗[K] K₁)).toSMul
          (inferInstance : Algebra K₁ (M ⊗[K] K₁)).toSMul]
        [IsDiscreteValuationRing.IsExtension A₁ B₁] [IsDiscreteValuationRing.IsExtension B₁ C₁]
        [IsDiscreteValuationRing.IsExtension A₁ C₁]
        [IsFractionRing A₁ K₁] [IsFractionRing B₁ (L ⊗[K] K₁)]
        [IsFractionRing C₁ (M ⊗[K] K₁)]
        [IsAdicComplete (IsLocalRing.maximalIdeal A₁) A₁]
        [IsAdicComplete (IsLocalRing.maximalIdeal B₁) B₁]
        [PerfectField (IsLocalRing.ResidueField A₁)]
        [CharP (IsLocalRing.ResidueField A₁) p]
        [Module.Finite (L ⊗[K] K₁) (M ⊗[K] K₁)],
        IsDiscreteValuationRing.IsWeaklyUnramified A₁ B₁ →
        ((∀ x : IsLocalRing.ResidueField B,
          (∃ a : IsLocalRing.ResidueField A,
            algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) a = x) ↔
            ∀ n : ℕ, 1 ≤ n → ∃ y : IsLocalRing.ResidueField B, y ^ (p ^ n) = x) →
          ∀ x : IsLocalRing.ResidueField B₁,
          (∃ a : IsLocalRing.ResidueField A₁,
            algebraMap (IsLocalRing.ResidueField A₁) (IsLocalRing.ResidueField B₁) a = x) ↔
            ∀ n : ℕ, 1 ≤ n → ∃ y : IsLocalRing.ResidueField B₁, y ^ (p ^ n) = x) →
        ∃ (F : Type u) (_ : Field F) (_ : Algebra K₁ F) (_ : Algebra A₁ F)
          (_ : @IsScalarTower A₁ K₁ F
          (inferInstance : Algebra A₁ K₁).toSMul
          (inferInstance : Algebra K₁ F).toSMul
          (inferInstance : Algebra A₁ F).toSMul) (_ : Module.Finite K₁ F),
          ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{u,u,u,u,u,u,u,u}
            A₁ C₁ K₁ (M ⊗[K] K₁) F, D.IsWeakSolution) :
    ∃ (F : Type u) (_ : Field F) (_ : Algebra K F) (_ : Algebra A F)
      (_ : IsScalarTower A K F) (_ : Module.Finite K F),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{u,u,u,u,u,u,u,u}
          A C K M F, D.IsWeakSolution
 := by
  classical
  let L₁ := L ⊗[K] K₁
  let M₁ := M ⊗[K] K₁
  let : Field L₁ := hL₁.toField
  let : Field M₁ := hM₁.toField
  let ι : L₁ →ₐ[K] M₁ :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M) (AlgHom.id K K₁)
  let : Algebra L₁ M₁ := ι.toRingHom.toAlgebra
  let : Algebra K₁ L₁ := Algebra.TensorProduct.rightAlgebra
  let : Algebra K₁ M₁ := Algebra.TensorProduct.rightAlgebra
  let : Module.Finite L₁ M₁ := hfinite
  have hι (x : L) (a : K₁) : ι (x ⊗ₜ[K] a) = algebraMap L M x ⊗ₜ[K] a :=
    Algebra.TensorProduct.map_tmul (IsScalarTower.toAlgHom K L M) (AlgHom.id K K₁) x a
  let : @IsScalarTower L L₁ M₁
      (inferInstance : Algebra L L₁).toSMul (inferInstance : Algebra L₁ M₁).toSMul
      (inferInstance : Algebra L M₁).toSMul := IsScalarTower.of_algebraMap_eq fun x => (hι x 1).symm
  let : @IsScalarTower K₁ L₁ M₁
      (inferInstance : Algebra K₁ L₁).toSMul (inferInstance : Algebra L₁ M₁).toSMul
      (inferInstance : Algebra K₁ M₁).toSMul := IsScalarTower.of_algebraMap_eq fun x => by
    change (1 : M) ⊗ₜ[K] x = ι ((1 : L) ⊗ₜ[K] x)
    rw [hι, map_one]
  let : @IsScalarTower B L₁ M₁
      (inferInstance : Algebra B L₁).toSMul (inferInstance : Algebra L₁ M₁).toSMul
      (inferInstance : Algebra B M₁).toSMul := IsScalarTower.of_algebraMap_eq fun b => by
    rw [IsScalarTower.algebraMap_apply B L M₁,
      IsScalarTower.algebraMap_apply L L₁ M₁,
      ← IsScalarTower.algebraMap_apply B L L₁]
  let : @IsScalarTower A B M
      (inferInstance : Algebra A B).toSMul (inferInstance : Algebra B M).toSMul
      (inferInstance : Algebra A M).toSMul := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A C M, IsScalarTower.algebraMap_apply A B C,
      ← IsScalarTower.algebraMap_apply B C M]
  let : @IsScalarTower A K₁ L₁
      (inferInstance : Algebra A K₁).toSMul (inferInstance : Algebra K₁ L₁).toSMul
      (inferInstance : Algebra A L₁).toSMul := IsScalarTower.of_algebraMap_eq fun a => by
    change (algebraMap A L a) ⊗ₜ[K] (1 : K₁) = (1 : L) ⊗ₜ[K] algebraMap A K₁ a
    rw [IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A K K₁]
    change (Algebra.TensorProduct.includeLeft : _ →ₐ[K] _) (algebraMap K _ _) =
      (Algebra.TensorProduct.includeRight : _ →ₐ[K] _) (algebraMap K _ _)
    rw [AlgHom.commutes, AlgHom.commutes]
  let : @IsScalarTower A K₁ M₁
      (inferInstance : Algebra A K₁).toSMul (inferInstance : Algebra K₁ M₁).toSMul
      (inferInstance : Algebra A M₁).toSMul := IsScalarTower.of_algebraMap_eq fun a => by
    change (algebraMap A M a) ⊗ₜ[K] (1 : K₁) = (1 : M) ⊗ₜ[K] algebraMap A K₁ a
    rw [IsScalarTower.algebraMap_apply A K M, IsScalarTower.algebraMap_apply A K K₁]
    change (Algebra.TensorProduct.includeLeft : _ →ₐ[K] _) (algebraMap K _ _) =
      (Algebra.TensorProduct.includeRight : _ →ₐ[K] _) (algebraMap K _ _)
    rw [AlgHom.commutes, AlgHom.commutes]
  let A₁ := integralClosure A K₁
  let B₁ := integralClosure B L₁
  let C₁ := integralClosure C M₁
  let : IsIntegralClosure C B M := isIntegralClosure_of_isAdicComplete B C L M
  let : Module.Finite B (integralClosure B M) :=
    (isDiscreteValuationRing_and_finite_integralClosure_of_isAdicComplete B L M).2
  let : Module.Finite B C :=
    Module.Finite.equiv (IsIntegralClosure.equiv B (integralClosure B M) M C).toLinearEquiv
  let : IsAdicComplete (IsLocalRing.maximalIdeal C) C := isAdicComplete_of_finite B C
  obtain ⟨hA₁, hAA₁, hAfin, hAc, hAf⟩ := integralClosure_isCompleteDVR A K K₁
  obtain ⟨hB₁, hBB₁, hBfin, hBc, hBf⟩ := integralClosure_isCompleteDVR B L L₁
  obtain ⟨hC₁, hCC₁, hCfin, hCc, hCf⟩ := integralClosure_isCompleteDVR C M M₁
  let := hA₁
  let := hB₁
  let := hC₁
  let := hAA₁
  let := hBB₁
  let := hCC₁
  let := hAfin
  let := hBfin
  let := hCfin
  let := hAc
  let := hBc
  let := hCc
  let := hAf
  let := hBf
  let := hCf
  let f := mapIntegralClosureOfTower A B K₁ L₁
  let g := mapIntegralClosureOfTower B C L₁ M₁
  let h := mapIntegralClosureOfTower A C K₁ M₁
  let : Algebra A₁ B₁ := f.toRingHom.toAlgebra
  let : Algebra B₁ C₁ := g.toRingHom.toAlgebra
  let : Algebra A₁ C₁ := h.toRingHom.toAlgebra
  let : Algebra A₁ L₁ := ((algebraMap K₁ L₁).comp (algebraMap A₁ K₁)).toAlgebra
  let : Algebra A₁ M₁ := ((algebraMap K₁ M₁).comp (algebraMap A₁ K₁)).toAlgebra
  let : Algebra B₁ M₁ := ((algebraMap L₁ M₁).comp (algebraMap B₁ L₁)).toAlgebra
  let : @IsScalarTower A₁ K₁ L₁
      (inferInstance : Algebra A₁ K₁).toSMul (inferInstance : Algebra K₁ L₁).toSMul
      (inferInstance : Algebra A₁ L₁).toSMul := IsScalarTower.of_algebraMap_eq' rfl
  let : @IsScalarTower A₁ K₁ M₁
      (inferInstance : Algebra A₁ K₁).toSMul (inferInstance : Algebra K₁ M₁).toSMul
      (inferInstance : Algebra A₁ M₁).toSMul := IsScalarTower.of_algebraMap_eq' rfl
  let : @IsScalarTower B₁ L₁ M₁
      (inferInstance : Algebra B₁ L₁).toSMul (inferInstance : Algebra L₁ M₁).toSMul
      (inferInstance : Algebra B₁ M₁).toSMul := IsScalarTower.of_algebraMap_eq' rfl
  let : @IsScalarTower A₁ B₁ L₁
      (inferInstance : Algebra A₁ B₁).toSMul (inferInstance : Algebra B₁ L₁).toSMul
      (inferInstance : Algebra A₁ L₁).toSMul := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : @IsScalarTower B₁ C₁ M₁
      (inferInstance : Algebra B₁ C₁).toSMul (inferInstance : Algebra C₁ M₁).toSMul
      (inferInstance : Algebra B₁ M₁).toSMul := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : @IsScalarTower A₁ C₁ M₁
      (inferInstance : Algebra A₁ C₁).toSMul (inferInstance : Algebra C₁ M₁).toSMul
      (inferInstance : Algebra A₁ M₁).toSMul := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : @IsScalarTower A₁ B₁ C₁
      (inferInstance : Algebra A₁ B₁).toSMul (inferInstance : Algebra B₁ C₁).toSMul
      (inferInstance : Algebra A₁ C₁).toSMul := IsScalarTower.of_algebraMap_eq fun a => by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply K₁ L₁ M₁ a.1
  let : @IsScalarTower A A₁ B₁
      (inferInstance : Algebra A A₁).toSMul (inferInstance : Algebra A₁ B₁).toSMul
      (inferInstance : Algebra A B₁).toSMul :=
    IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  let : @IsScalarTower A A₁ C₁
      (inferInstance : Algebra A A₁).toSMul (inferInstance : Algebra A₁ C₁).toSMul
      (inferInstance : Algebra A C₁).toSMul :=
    IsScalarTower.of_algebraMap_eq fun x => (h.commutes x).symm
  let : @IsScalarTower B B₁ C₁
      (inferInstance : Algebra B B₁).toSMul (inferInstance : Algebra B₁ C₁).toSMul
      (inferInstance : Algebra B C₁).toSMul :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  let : IsDiscreteValuationRing.IsExtension A₁ B₁ :=
    (integralClosure_factor_isExtension A B K L K₁ L₁).choose_spec.choose_spec.1
  let : IsDiscreteValuationRing.IsExtension A₁ C₁ :=
    (integralClosure_factor_isExtension A C K M K₁ M₁).choose_spec.choose_spec.1
  let : IsDiscreteValuationRing.IsExtension B₁ C₁ :=
    (integralClosure_factor_isExtension B C L M L₁ M₁).choose_spec.choose_spec.1
  let : PerfectField (IsLocalRing.ResidueField A₁) :=
    perfectField_residueField_of_finite A A₁
  let : CharP (IsLocalRing.ResidueField A₁) p :=
    charP_of_injective_algebraMap
      (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A₁)).injective p
  have hmap := (IsDiscreteValuationRing.ramificationIndex_characterization A B).2.1
  rw [show IsDiscreteValuationRing.ramificationIndex A B = 1 from hweak, pow_one] at hmap
  obtain ⟨_, _, hBdom, hBt, hinj, hmax, hBdom', _, _, e, he, hinj', hmax'⟩ :=
    IsDiscreteValuationRing.isField_tensorProduct_and_isDVR_baseChange_of_totallyRamified
      A B K L K₁ hmap htot
  obtain ⟨erA⟩ := exists_residueField_algEquiv_of_totallyRamified A K K₁ htot
  obtain ⟨erB⟩ := exists_residueField_algEquiv_of_tensorProduct A B A₁ B₁ hmap erA e
    (by simpa only [Ideal.map_map] using hmax')
  let eA : IsLocalRing.ResidueField A₁ ≃ₐ[A] IsLocalRing.ResidueField A := erA
  let eB : IsLocalRing.ResidueField B₁ ≃ₐ[B] IsLocalRing.ResidueField B := erB
  have heq : e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom = f.toRingHom := by
    ext a
    exact he a
  rw [heq] at hmax'
  have hweak₁ : IsDiscreteValuationRing.IsWeaklyUnramified A₁ B₁ :=
    (isWeaklyUnramified_iff_ramificationIdx_eq_one A₁ B₁).mpr
      (forall_ramificationIdx_eq_one_of_map_maximalIdeal A₁ B₁ hmax' _ inferInstance)
  let : IsLocalHom (algebraMap A B₁) := by
    rw [IsScalarTower.algebraMap_eq A B B₁]
    infer_instance
  let ρ : IsLocalRing.ResidueField A →ₐ[A] IsLocalRing.ResidueField B :=
    IsScalarTower.toAlgHom A (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)
  let ρ₁ : IsLocalRing.ResidueField A₁ →ₐ[A] IsLocalRing.ResidueField B₁ :=
    IsScalarTower.toAlgHom A (IsLocalRing.ResidueField A₁) (IsLocalRing.ResidueField B₁)
  have hsurj : Function.Surjective
      (algebraMap A (IsLocalRing.ResidueField A₁)) :=
    surjective_algebraMap_residueField_of_totallyRamified A K K₁ htot
  have hsq : ∀ a : IsLocalRing.ResidueField A₁, eB (ρ₁ a) = ρ (eA a) := by
    intro a
    obtain ⟨a₀, rfl⟩ := hsurj a
    rw [ρ₁.commutes, eA.commutes, ρ.commutes]
    calc
      eB (algebraMap A (IsLocalRing.ResidueField B₁) a₀) =
          eB (algebraMap B (IsLocalRing.ResidueField B₁) (algebraMap A B a₀)) := by
            congr 1
            change IsLocalRing.residue B₁ (algebraMap A B₁ a₀) =
              IsLocalRing.residue B₁ (algebraMap B B₁ (algebraMap A B a₀))
            rw [IsScalarTower.algebraMap_apply A B B₁]
      _ = algebraMap B (IsLocalRing.ResidueField B) (algebraMap A B a₀) :=
        eB.commutes (algebraMap A B a₀)
      _ = algebraMap A (IsLocalRing.ResidueField B) a₀ := by
        rfl
  obtain ⟨F, hF, hKF, hAF, hAKF, hfinF, D, hD⟩ := hnext hweak₁ fun hresidue => by
    have hresidue' : ∀ x : IsLocalRing.ResidueField B,
        (∃ a : IsLocalRing.ResidueField A, ρ a = x) ↔
          ∀ n : ℕ, 1 ≤ n → ∃ y : IsLocalRing.ResidueField B, y ^ (p ^ n) = x := by
      simpa [ρ] using hresidue
    simpa [ρ₁] using
      Stacks.DiscreteValuationRing.EppLevelInduction.forall_exists_pow_iff_of_algEquiv_square
        ρ ρ₁ eA eB hsq p hresidue'
  let := hF
  let := hKF
  let := hAF
  let : @IsScalarTower A₁ K₁ F
      (inferInstance : Algebra A₁ K₁).toSMul (inferInstance : Algebra K₁ F).toSMul
      (inferInstance : Algebra A₁ F).toSMul := hAKF
  let := hfinF
  let : Algebra K F := ((algebraMap K₁ F).comp (algebraMap K K₁)).toAlgebra
  let : Algebra A F := ((algebraMap K F).comp (algebraMap A K)).toAlgebra
  let : @IsScalarTower K K₁ F
      (inferInstance : Algebra K K₁).toSMul (inferInstance : Algebra K₁ F).toSMul
      (inferInstance : Algebra K F).toSMul := IsScalarTower.of_algebraMap_eq' rfl
  let : @IsScalarTower A K F
      (inferInstance : Algebra A K).toSMul (inferInstance : Algebra K F).toSMul
      (inferInstance : Algebra A F).toSMul := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite K F := Module.Finite.trans (R := K) K₁ F
  obtain ⟨D'⟩ := nonempty_integralClosureBaseChange A C K M F
  refine ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, D', ?_⟩
  let : Algebra K₁ (ReducedTensorTower.Reduction M₁) := Ideal.Quotient.algebra K₁
  let er : ReducedTensorTower.Reduction M₁ ≃ₐ[K₁] M₁ :=
    (Ideal.quotientEquivAlgOfEq K₁ (nilradical_eq_zero M₁)).trans (AlgEquiv.quotientBot K₁ M₁)
  apply isWeakSolution_of_iterated_package A C K M K₁ F A₁ D' M₁ C₁ ?_ ?_ ?_ D hD er
    (fun _ => rfl)
  · intro a
    change algebraMap K₁ F (algebraMap K K₁ (algebraMap A K a)) = _
    rw [← IsScalarTower.algebraMap_apply A K K₁,
      IsScalarTower.algebraMap_apply A A₁ K₁, ← IsScalarTower.algebraMap_apply A₁ K₁ F]
  · intro c
    rfl
  · intro a
    apply Subtype.ext
    change algebraMap C M₁ (algebraMap A C a) = algebraMap K₁ M₁ (algebraMap A K₁ a)
    rw [← IsScalarTower.algebraMap_apply A C M₁, ← IsScalarTower.algebraMap_apply A K₁ M₁]

theorem exists_finite_extension_isWeakSolution_of_totallyRamified_tensorProduct
    (A B C K L M K₁ : Type u)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M] [Field K₁]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra B M] [Algebra A M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsDiscreteValuationRing.IsExtension A B] [IsDiscreteValuationRing.IsExtension B C]
    [IsDiscreteValuationRing.IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [Module.Finite L M]
    [Algebra K K₁] [Algebra A K₁] [IsScalarTower A K K₁]
    [Module.Finite K K₁] [Algebra.IsSeparable K K₁]
    [PerfectField (IsLocalRing.ResidueField A)]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    (hweak : IsDiscreteValuationRing.IsWeaklyUnramified A B)
    (hresidue : ∀ x : IsLocalRing.ResidueField B,
      (∃ a : IsLocalRing.ResidueField A,
        algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) a = x) ↔
        ∀ n : ℕ, 1 ≤ n → ∃ y : IsLocalRing.ResidueField B, y ^ (p ^ n) = x)
    (htot : IsDiscreteValuationRing.IsTotallyRamifiedWithRespectTo A K K₁)
    (hL₁ : IsField (L ⊗[K] K₁)) (hM₁ : IsField (M ⊗[K] K₁))
    (hfinite :
      letI := hL₁.toField
      letI := hM₁.toField
      letI : Algebra (L ⊗[K] K₁) (M ⊗[K] K₁) :=
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M)
          (AlgHom.id K K₁)).toRingHom.toAlgebra
      Module.Finite (L ⊗[K] K₁) (M ⊗[K] K₁))
    (hnext :
      letI := hL₁.toField
      letI := hM₁.toField
      letI : Algebra (L ⊗[K] K₁) (M ⊗[K] K₁) :=
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M)
          (AlgHom.id K K₁)).toRingHom.toAlgebra
      letI : Algebra K₁ (L ⊗[K] K₁) := Algebra.TensorProduct.rightAlgebra
      letI : Algebra K₁ (M ⊗[K] K₁) := Algebra.TensorProduct.rightAlgebra
      let A₁ := integralClosure A K₁
      let B₁ := integralClosure B (L ⊗[K] K₁)
      let C₁ := integralClosure C (M ⊗[K] K₁)
      letI : Algebra A₁ (L ⊗[K] K₁) :=
        ((algebraMap K₁ (L ⊗[K] K₁)).comp (algebraMap A₁ K₁)).toAlgebra
      letI : Algebra A₁ (M ⊗[K] K₁) :=
        ((algebraMap K₁ (M ⊗[K] K₁)).comp (algebraMap A₁ K₁)).toAlgebra
      letI : Algebra B₁ (M ⊗[K] K₁) :=
        ((algebraMap (L ⊗[K] K₁) (M ⊗[K] K₁)).comp
          (algebraMap B₁ (L ⊗[K] K₁))).toAlgebra
      ∀ [IsDiscreteValuationRing A₁] [IsDiscreteValuationRing B₁]
        [IsDiscreteValuationRing C₁]
        [Algebra A₁ B₁] [Algebra B₁ C₁] [Algebra A₁ C₁]
        [@IsScalarTower A₁ B₁ C₁
          (inferInstance : Algebra A₁ B₁).toSMul
          (inferInstance : Algebra B₁ C₁).toSMul
          (inferInstance : Algebra A₁ C₁).toSMul]
        [@IsScalarTower A₁ B₁ (L ⊗[K] K₁)
          (inferInstance : Algebra A₁ B₁).toSMul
          (inferInstance : Algebra B₁ (L ⊗[K] K₁)).toSMul
          (inferInstance : Algebra A₁ (L ⊗[K] K₁)).toSMul]
        [@IsScalarTower A₁ K₁ (L ⊗[K] K₁)
          (inferInstance : Algebra A₁ K₁).toSMul
          (inferInstance : Algebra K₁ (L ⊗[K] K₁)).toSMul
          (inferInstance : Algebra A₁ (L ⊗[K] K₁)).toSMul]
        [@IsScalarTower B₁ C₁ (M ⊗[K] K₁)
          (inferInstance : Algebra B₁ C₁).toSMul
          (inferInstance : Algebra C₁ (M ⊗[K] K₁)).toSMul
          (inferInstance : Algebra B₁ (M ⊗[K] K₁)).toSMul]
        [@IsScalarTower B₁ (L ⊗[K] K₁) (M ⊗[K] K₁)
          (inferInstance : Algebra B₁ (L ⊗[K] K₁)).toSMul
          (inferInstance : Algebra (L ⊗[K] K₁) (M ⊗[K] K₁)).toSMul
          (inferInstance : Algebra B₁ (M ⊗[K] K₁)).toSMul]
        [@IsScalarTower A₁ C₁ (M ⊗[K] K₁)
          (inferInstance : Algebra A₁ C₁).toSMul
          (inferInstance : Algebra C₁ (M ⊗[K] K₁)).toSMul
          (inferInstance : Algebra A₁ (M ⊗[K] K₁)).toSMul]
        [@IsScalarTower A₁ K₁ (M ⊗[K] K₁)
          (inferInstance : Algebra A₁ K₁).toSMul
          (inferInstance : Algebra K₁ (M ⊗[K] K₁)).toSMul
          (inferInstance : Algebra A₁ (M ⊗[K] K₁)).toSMul]
        [@IsScalarTower K₁ (L ⊗[K] K₁) (M ⊗[K] K₁)
          (inferInstance : Algebra K₁ (L ⊗[K] K₁)).toSMul
          (inferInstance : Algebra (L ⊗[K] K₁) (M ⊗[K] K₁)).toSMul
          (inferInstance : Algebra K₁ (M ⊗[K] K₁)).toSMul]
        [IsDiscreteValuationRing.IsExtension A₁ B₁] [IsDiscreteValuationRing.IsExtension B₁ C₁]
        [IsDiscreteValuationRing.IsExtension A₁ C₁]
        [IsFractionRing A₁ K₁] [IsFractionRing B₁ (L ⊗[K] K₁)]
        [IsFractionRing C₁ (M ⊗[K] K₁)]
        [IsAdicComplete (IsLocalRing.maximalIdeal A₁) A₁]
        [IsAdicComplete (IsLocalRing.maximalIdeal B₁) B₁]
        [PerfectField (IsLocalRing.ResidueField A₁)]
        [CharP (IsLocalRing.ResidueField A₁) p]
        [Module.Finite (L ⊗[K] K₁) (M ⊗[K] K₁)],
        IsDiscreteValuationRing.IsWeaklyUnramified A₁ B₁ →
        (∀ x : IsLocalRing.ResidueField B₁,
          (∃ a : IsLocalRing.ResidueField A₁,
            algebraMap (IsLocalRing.ResidueField A₁) (IsLocalRing.ResidueField B₁) a = x) ↔
            ∀ n : ℕ, 1 ≤ n → ∃ y : IsLocalRing.ResidueField B₁, y ^ (p ^ n) = x) →
        ∃ (F : Type u) (_ : Field F) (_ : Algebra K₁ F) (_ : Algebra A₁ F)
          (_ : @IsScalarTower A₁ K₁ F
          (inferInstance : Algebra A₁ K₁).toSMul
          (inferInstance : Algebra K₁ F).toSMul
          (inferInstance : Algebra A₁ F).toSMul) (_ : Module.Finite K₁ F),
          ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{u,u,u,u,u,u,u,u}
            A₁ C₁ K₁ (M ⊗[K] K₁) F, D.IsWeakSolution) :
    ∃ (F : Type u) (_ : Field F) (_ : Algebra K F) (_ : Algebra A F)
      (_ : IsScalarTower A K F) (_ : Module.Finite K F),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{u,u,u,u,u,u,u,u}
          A C K M F, D.IsWeakSolution
 := by
  exact exists_finite_extension_isWeakSolution_of_totallyRamified_tensorProduct_aux
    A B C K L M K₁ p hweak htot hL₁ hM₁ hfinite (fun hw hr => hnext hw (hr hresidue))

/-- Compose a recursive weak solution across a totally ramified mixed-characteristic level step.

This version deliberately assumes no global perfect-core range condition. It is the composition
primitive used by the Epp-condition recursion, where each step absorbs only the finite support it
actually exposes. -/
theorem exists_finite_extension_isWeakSolution_of_totallyRamified_tensorProduct_of_perfectResidue
    (A B C K L M K₁ : Type u)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M] [Field K₁]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra B M] [Algebra A M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsDiscreteValuationRing.IsExtension A B] [IsDiscreteValuationRing.IsExtension B C]
    [IsDiscreteValuationRing.IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [Module.Finite L M]
    [Algebra K K₁] [Algebra A K₁] [IsScalarTower A K K₁]
    [Module.Finite K K₁] [Algebra.IsSeparable K K₁]
    [PerfectField (IsLocalRing.ResidueField A)]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    (hweak : IsDiscreteValuationRing.IsWeaklyUnramified A B)
    (htot : IsDiscreteValuationRing.IsTotallyRamifiedWithRespectTo A K K₁)
    (hL₁ : IsField (L ⊗[K] K₁)) (hM₁ : IsField (M ⊗[K] K₁))
    (hfinite :
      letI := hL₁.toField
      letI := hM₁.toField
      letI : Algebra (L ⊗[K] K₁) (M ⊗[K] K₁) :=
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M)
          (AlgHom.id K K₁)).toRingHom.toAlgebra
      Module.Finite (L ⊗[K] K₁) (M ⊗[K] K₁))
    (hnext :
      letI := hL₁.toField
      letI := hM₁.toField
      letI : Algebra (L ⊗[K] K₁) (M ⊗[K] K₁) :=
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M)
          (AlgHom.id K K₁)).toRingHom.toAlgebra
      letI : Algebra K₁ (L ⊗[K] K₁) := Algebra.TensorProduct.rightAlgebra
      letI : Algebra K₁ (M ⊗[K] K₁) := Algebra.TensorProduct.rightAlgebra
      let A₁ := integralClosure A K₁
      let B₁ := integralClosure B (L ⊗[K] K₁)
      let C₁ := integralClosure C (M ⊗[K] K₁)
      letI : Algebra A₁ (L ⊗[K] K₁) :=
        ((algebraMap K₁ (L ⊗[K] K₁)).comp (algebraMap A₁ K₁)).toAlgebra
      letI : Algebra A₁ (M ⊗[K] K₁) :=
        ((algebraMap K₁ (M ⊗[K] K₁)).comp (algebraMap A₁ K₁)).toAlgebra
      letI : Algebra B₁ (M ⊗[K] K₁) :=
        ((algebraMap (L ⊗[K] K₁) (M ⊗[K] K₁)).comp
          (algebraMap B₁ (L ⊗[K] K₁))).toAlgebra
      ∀ [IsDiscreteValuationRing A₁] [IsDiscreteValuationRing B₁]
        [IsDiscreteValuationRing C₁]
        [Algebra A₁ B₁] [Algebra B₁ C₁] [Algebra A₁ C₁]
        [@IsScalarTower A₁ B₁ C₁
          (inferInstance : Algebra A₁ B₁).toSMul
          (inferInstance : Algebra B₁ C₁).toSMul
          (inferInstance : Algebra A₁ C₁).toSMul]
        [@IsScalarTower A₁ B₁ (L ⊗[K] K₁)
          (inferInstance : Algebra A₁ B₁).toSMul
          (inferInstance : Algebra B₁ (L ⊗[K] K₁)).toSMul
          (inferInstance : Algebra A₁ (L ⊗[K] K₁)).toSMul]
        [@IsScalarTower A₁ K₁ (L ⊗[K] K₁)
          (inferInstance : Algebra A₁ K₁).toSMul
          (inferInstance : Algebra K₁ (L ⊗[K] K₁)).toSMul
          (inferInstance : Algebra A₁ (L ⊗[K] K₁)).toSMul]
        [@IsScalarTower B₁ C₁ (M ⊗[K] K₁)
          (inferInstance : Algebra B₁ C₁).toSMul
          (inferInstance : Algebra C₁ (M ⊗[K] K₁)).toSMul
          (inferInstance : Algebra B₁ (M ⊗[K] K₁)).toSMul]
        [@IsScalarTower B₁ (L ⊗[K] K₁) (M ⊗[K] K₁)
          (inferInstance : Algebra B₁ (L ⊗[K] K₁)).toSMul
          (inferInstance : Algebra (L ⊗[K] K₁) (M ⊗[K] K₁)).toSMul
          (inferInstance : Algebra B₁ (M ⊗[K] K₁)).toSMul]
        [@IsScalarTower A₁ C₁ (M ⊗[K] K₁)
          (inferInstance : Algebra A₁ C₁).toSMul
          (inferInstance : Algebra C₁ (M ⊗[K] K₁)).toSMul
          (inferInstance : Algebra A₁ (M ⊗[K] K₁)).toSMul]
        [@IsScalarTower A₁ K₁ (M ⊗[K] K₁)
          (inferInstance : Algebra A₁ K₁).toSMul
          (inferInstance : Algebra K₁ (M ⊗[K] K₁)).toSMul
          (inferInstance : Algebra A₁ (M ⊗[K] K₁)).toSMul]
        [@IsScalarTower K₁ (L ⊗[K] K₁) (M ⊗[K] K₁)
          (inferInstance : Algebra K₁ (L ⊗[K] K₁)).toSMul
          (inferInstance : Algebra (L ⊗[K] K₁) (M ⊗[K] K₁)).toSMul
          (inferInstance : Algebra K₁ (M ⊗[K] K₁)).toSMul]
        [IsDiscreteValuationRing.IsExtension A₁ B₁] [IsDiscreteValuationRing.IsExtension B₁ C₁]
        [IsDiscreteValuationRing.IsExtension A₁ C₁]
        [IsFractionRing A₁ K₁] [IsFractionRing B₁ (L ⊗[K] K₁)]
        [IsFractionRing C₁ (M ⊗[K] K₁)]
        [IsAdicComplete (IsLocalRing.maximalIdeal A₁) A₁]
        [IsAdicComplete (IsLocalRing.maximalIdeal B₁) B₁]
        [PerfectField (IsLocalRing.ResidueField A₁)]
        [CharP (IsLocalRing.ResidueField A₁) p]
        [Module.Finite (L ⊗[K] K₁) (M ⊗[K] K₁)],
        IsDiscreteValuationRing.IsWeaklyUnramified A₁ B₁ →
        ∃ (F : Type u) (_ : Field F) (_ : Algebra K₁ F) (_ : Algebra A₁ F)
          (_ : @IsScalarTower A₁ K₁ F
          (inferInstance : Algebra A₁ K₁).toSMul
          (inferInstance : Algebra K₁ F).toSMul
          (inferInstance : Algebra A₁ F).toSMul) (_ : Module.Finite K₁ F),
          ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{u,u,u,u,u,u,u,u}
            A₁ C₁ K₁ (M ⊗[K] K₁) F, D.IsWeakSolution) :
    ∃ (F : Type u) (_ : Field F) (_ : Algebra K F) (_ : Algebra A F)
      (_ : IsScalarTower A K F) (_ : Module.Finite K F),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{u,u,u,u,u,u,u,u}
          A C K M F, D.IsWeakSolution
 := by
  exact exists_finite_extension_isWeakSolution_of_totallyRamified_tensorProduct_aux
    A B C K L M K₁ p hweak htot hL₁ hM₁ hfinite (fun hw _ => hnext hw)

end IsDiscreteValuationRing
