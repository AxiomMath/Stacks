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
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.TameCase
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.PurelyInseparableCase
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.IteratedPackages
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.FiniteLevelCyclotomic

open Stacks.DegreePExtensionLevel
open Stacks.DiscreteValuationRing.EppLevelInduction

/-!
# Eliminating ramification: induction over intermediate fields

The prime-degree step, inertia fixed fields, the induction over intermediate fields, and Epp's
theorem in the complete case (Tag 09F8).

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

private theorem exists_finite_extension_isWeakSolution_of_normal_factor_induction
    (p : ℕ) [Fact p.Prime]
    (A B C K L M : Type u)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M]
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
    [CharP (IsLocalRing.ResidueField A) p]
    [IsAlgClosed (IsLocalRing.ResidueField A)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [Module.Finite L M]
    (hresidue : ∀ x : IsLocalRing.ResidueField B,
      (∃ a : IsLocalRing.ResidueField A,
          algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) a = x) ↔
        ∀ n : ℕ, 1 ≤ n → ∃ y : IsLocalRing.ResidueField B, y ^ (p ^ n) = x)
    [Normal L M]
    (hcyclo : CharZero K → Nonempty (CyclotomicRing p ℤ ℚ →+* A))
    (hsol : ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{u,u,u,u,u,u,u,u} A B K L K₁,
        D.IsWeakSolution)
    (hnext : NormalTowerSolvable.{u} p (Module.finrank L M)) :
    ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{u,u,u,u,u,u,u,u} A C K M K₁,
        D.IsWeakSolution
 := by
  obtain ⟨K₁, hK₁, hKK₁, hAK₁, htower, hfin, D, hD⟩ := hsol
  let := hK₁
  let := hKK₁
  let := hAK₁
  let := htower
  let := hfin
  apply exists_finite_extension_isWeakSolution_of_normal_factor_induction_of_cyclotomic_extension
    p A B C K L M hresidue ?_ hnext
  refine ⟨K₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, D, hD, ?_⟩
  intro hc
  let := hc
  let : CharZero K := (algebraMap K K₁).charZero
  obtain ⟨f⟩ := hcyclo inferInstance
  exact ⟨(algebraMap A (integralClosure A K₁)).comp f⟩

/-- Scalar towers `A → B → C → M` and `A → C → M` give a scalar tower `A → B → M`. -/
private theorem isScalarTower_of_isScalarTower_top
    (A B C M : Type*) [CommRing A] [CommRing B] [CommRing C] [CommRing M]
    [Algebra A B] [Algebra B C] [Algebra A C] [Algebra C M] [Algebra B M] [Algebra A M]
    [IsScalarTower A B C] [IsScalarTower B C M] [IsScalarTower A C M] :
    IsScalarTower A B M :=
  IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A C M, IsScalarTower.algebraMap_apply A B C,
      ← IsScalarTower.algebraMap_apply B C M]

/-- The top ring of a finite extension of fraction fields over a complete discrete valuation ring
is the integral closure, is finite, and is complete. -/
private theorem isIntegralClosure_and_finite_and_isAdicComplete
    (B C L M : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Field L] [Field M]
    [Algebra B C] [Algebra B L] [Algebra C M] [Algebra L M] [Algebra B M]
    [IsScalarTower B L M] [IsScalarTower B C M] [IsFractionRing B L] [IsFractionRing C M]
    [IsDiscreteValuationRing.IsExtension B C] [Module.Finite L M]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B] :
    IsIntegralClosure C B M ∧ Module.Finite B C ∧
      IsAdicComplete (IsLocalRing.maximalIdeal C) C := by
  have : IsIntegralClosure C B M := isIntegralClosure_of_isAdicComplete B C L M
  have : Module.Finite B (integralClosure B M) :=
    (isDiscreteValuationRing_and_finite_integralClosure_of_isAdicComplete B L M).2
  have : Module.Finite B C := Module.Finite.equiv
    (IsIntegralClosure.equiv B (integralClosure B M) M C).toLinearEquiv
  exact ⟨inferInstance, inferInstance, isAdicComplete_of_finite B C⟩

private theorem exists_finite_extension_isWeakSolution_of_prime_degree
    (p : ℕ) [Fact p.Prime]
    (A B C K L M : Type u)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M]
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
    [CharP (IsLocalRing.ResidueField A) p]
    [IsAlgClosed (IsLocalRing.ResidueField A)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [Module.Finite L M]
    (hresidue : ∀ x : IsLocalRing.ResidueField B,
      (∃ a : IsLocalRing.ResidueField A,
          algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) a = x) ↔
        ∀ n : ℕ, 1 ≤ n → ∃ y : IsLocalRing.ResidueField B, y ^ (p ^ n) = x)
    (hweak : IsDiscreteValuationRing.IsWeaklyUnramified A B)
    (hcyclo : CharZero K → Nonempty (CyclotomicRing p ℤ ℚ →+* A))
    (hprime : IsPurelyInseparable L M ∧ Module.finrank L M = p ∨
      IsGalois L M ∧ (Module.finrank L M).Prime) :
    ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{u,u,u,u,u,u,u,u} A C K M K₁,
        D.IsWeakSolution
 := by
  rcases hprime with ⟨hpure, hdeg⟩ | ⟨hgal, hdeg⟩
  · let := hpure
    exact exists_finite_extension_isWeakSolution_of_isPurelyInseparable A B C K L M p hdeg hweak
  let := hgal
  by_cases hqp : Module.finrank L M = p
  · rcases charZero_or_charP_of_injective (algebraMap A K) (IsFractionRing.injective A K)
        (IsLocalRing.residue A) p with hc | hc
    · let := hc
      obtain ⟨f⟩ := hcyclo hc
      exact exists_finite_extension_isWeakSolution_of_isGalois_of_cyclotomic_of_perfectResidue
        p A B C K L M hweak hresidue hqp ((algebraMap A B).comp f)
    · let := hc
      obtain ⟨K₁, hK₁, hKK₁, hAK₁, htower, hfin, hgal, htot, D, hD⟩ :=
        IsDiscreteValuationRing.exists_isGalois_totallyRamified_isWeakSolution_of_charP
          A B C K L M p (Fact.out : p.Prime) hqp hweak hresidue
      exact ⟨K₁, hK₁, hKK₁, hAK₁, htower, hfin, D, hD⟩
  obtain ⟨_, _, _⟩ := isIntegralClosure_and_finite_and_isAdicComplete B C L M
  have htame : ringChar (IsLocalRing.ResidueField A) = 0 ∨
      Nat.Coprime (ringChar (IsLocalRing.ResidueField A))
          (IsDiscreteValuationRing.ramificationIndex A C) ∧
        Algebra.IsSeparableExtension (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField C) := by
    refine Or.inr ⟨?_, Algebra.isSeparableExtension_of_perfectField _ _⟩
    rw [ringChar.eq (IsLocalRing.ResidueField A) p]
    have hd : IsDiscreteValuationRing.ramificationIndex B C ∣ Module.finrank L M := by
      rw [IsFractionRing.finrank_eq B L C M, ramificationIndex_eq_ramificationIdx B C]
      exact ramificationIdx_dvd_finrank_of_isLocalRing B C
    have he : IsDiscreteValuationRing.ramificationIndex A C =
        IsDiscreteValuationRing.ramificationIndex B C := by
      have h := Ideal.ramificationIdx_tower (R := A)
        (IsLocalRing.maximalIdeal B) (IsLocalRing.maximalIdeal C)
      rw [← ramificationIndex_eq_ramificationIdx A C,
        ← ramificationIndex_eq_ramificationIdx A B,
        ← ramificationIndex_eq_ramificationIdx B C] at h
      simpa only [show IsDiscreteValuationRing.ramificationIndex A B = 1 from hweak, one_mul]
        using h
    rw [he]
    exact ((Nat.coprime_primes (Fact.out : p.Prime) hdeg).mpr (Ne.symm hqp)).of_dvd_right hd
  obtain ⟨K₁, hK₁, hKK₁, hAK₁, htower, hfin, -, D, hD⟩ :=
    exists_finite_extension_isWeakSolution_of_tame A C K M htame
  exact ⟨K₁, hK₁, hKK₁, hAK₁, htower, hfin, D, hD⟩

/-- The integral closure in the fixed field of the inertia group is formally unramified.

When the fixed field is everything, no extension is needed at all, and this with
`isWeaklyUnramified_of_formallyUnramified` is why. -/
@[sga "7 I 0.3" "partial"]
theorem formallyUnramified_integralClosure_fixedField_inertia
    (A K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Module.Finite K L] [IsGalois K L]
    [Algebra A L] [IsScalarTower A K L]
    [IsLocalRing (integralClosure A L)] :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    let E := IntermediateField.fixedField
      ((IsLocalRing.maximalIdeal (integralClosure A L)).inertia Gal(L/K))
    IsLocalRing (integralClosure A E) → Algebra.FormallyUnramified A (integralClosure A E)
 := by
  classical
  let R := integralClosure A L
  let := IsIntegralClosure.MulSemiringAction A K L R
  let : SMulCommClass Gal(L/K) A R :=
    ⟨fun g a b => by
      simp only [Algebra.smul_def]
      change galRestrict A K L R g (algebraMap A R a * b) =
        algebraMap A R a * galRestrict A K L R g b
      rw [map_mul, AlgEquiv.commutes]⟩
  let P := IsLocalRing.maximalIdeal R
  let I := P.inertia Gal(L/K)
  let E := IntermediateField.fixedField I
  let S := integralClosure A E
  dsimp only
  intro hS
  let : IsLocalRing S := hS
  let R' := FixedPoints.subalgebra A R I
  let inclusion : R' →ₐ[A] L := R.val.comp R'.val
  let iota : R' →ₐ[A] E :=
    inclusion.codRestrict (E.toSubalgebra.restrictScalars A) (fun b => by
      change (inclusion b : L) ∈ E
      rw [IntermediateField.mem_fixedField_iff]
      intro g hg
      exact (algebraMap_galRestrict_apply A g (b : R)).symm.trans
        (congrArg (algebraMap R L) (b.property ⟨g, hg⟩)))
  let : Algebra R' E := iota.toAlgebra
  let : IsScalarTower A R' E := IsScalarTower.of_algebraMap_eq fun a => (iota.commutes a).symm
  obtain ⟨hIC, het⟩ :=
    IsDiscreteValuationRing.inertia_fixedSubalgebra_isIntegralClosure_and_etale_localization A K L P
  let : IsIntegralClosure R' A E := hIC
  let e : S ≃ₐ[A] R' := IsIntegralClosure.equiv A S E R'
  let : IsLocalRing R' := e.toRingEquiv.isLocalRing
  let : Algebra.IsIntegral R' R := Algebra.IsIntegral.tower_top A
  let : IsLocalHom (algebraMap R' R) := Algebra.IsIntegral.isLocalHom R' R
  let q := P.under R'
  have hq : q = IsLocalRing.maximalIdeal R' := IsLocalRing.maximalIdeal_comap (algebraMap R' R)
  let : Algebra.Etale A (Localization.AtPrime q) := het
  let l : R' ≃ₐ[R'] Localization.AtPrime q := IsLocalization.atUnits R' q.primeCompl (by
    intro x hx
    change IsUnit x
    simpa only [hq, Ideal.mem_primeCompl_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, not_not] using hx)
  let e' : S ≃ₐ[A] Localization.AtPrime q := e.trans (l.restrictScalars A)
  exact Algebra.FormallyUnramified.of_equiv (R := A) (A := Localization.AtPrime q) (B := S) e'.symm

/-- The inertia group of the maximal ideal is normal, so its fixed field is a normal subextension.

The fixed field is where the inertia branch of a layer recursion splits, and normality is what
lets the recursion re-enter on it. -/
theorem normal_inertia_maximalIdeal
    (G R : Type*) [Group G] [CommRing R] [IsLocalRing R] [MulSemiringAction G R] :
    ((IsLocalRing.maximalIdeal R).inertia G).Normal := by
  refine ⟨fun σ hσ τ => ?_⟩
  rw [Ideal.mem_inertia] at hσ ⊢
  intro x
  have h := hσ (τ⁻¹ • x)
  have h' : τ • (σ • (τ⁻¹ • x) - τ⁻¹ • x) ∈ IsLocalRing.maximalIdeal R := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h ⊢
    exact fun hu => h ((MulEquiv.isUnit_map (MulSemiringAction.toRingAut G R τ)).mp hu)
  simpa only [mul_smul, smul_sub, smul_inv_smul] using h'

private theorem exists_finite_extension_isWeakSolution_of_intermediateField_induction
    (p : ℕ) [Fact p.Prime]
    (A B C K L M : Type u)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M]
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
    [CharP (IsLocalRing.ResidueField A) p]
    [IsAlgClosed (IsLocalRing.ResidueField A)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [Module.Finite L M]
    (hresidue : ∀ x : IsLocalRing.ResidueField B,
      (∃ a : IsLocalRing.ResidueField A,
          algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) a = x) ↔
        ∀ n : ℕ, 1 ≤ n → ∃ y : IsLocalRing.ResidueField B, y ^ (p ^ n) = x)
    [Normal L M]
    (hweak : IsDiscreteValuationRing.IsWeaklyUnramified A B)
    (hcyclo : CharZero K → Nonempty (CyclotomicRing p ℤ ℚ →+* A))
    (E : IntermediateField L M) [Normal L E]
    (hfirst : NormalTowerSolvable.{u} p (Module.finrank L E))
    (hnext : NormalTowerSolvable.{u} p (Module.finrank E M)) :
    ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{u,u,u,u,u,u,u,u} A C K M K₁,
        D.IsWeakSolution
 := by
  classical
  have := isScalarTower_of_isScalarTower_top A B C M
  let : IsScalarTower A L M := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A K M, IsScalarTower.algebraMap_apply A K L,
      IsScalarTower.algebraMap_apply K L M]
  let : IsIntegralClosure C B M := isIntegralClosure_of_isAdicComplete B C L M
  let : IsScalarTower A B E := IsScalarTower.of_algebraMap_eq fun a =>
    E.val.injective (IsScalarTower.algebraMap_apply A B M a)
  let : @IsScalarTower B E M
      (inferInstance : Algebra B E).toSMul (inferInstance : Algebra E M).toSMul
      (inferInstance : Algebra B M).toSMul := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : @IsScalarTower K E M
      (inferInstance : Algebra K E).toSMul (inferInstance : Algebra E M).toSMul
      (inferInstance : Algebra K M).toSMul := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let S := integralClosure B E
  obtain ⟨hS, hBS, hSfin, hSc, hSf⟩ := integralClosure_isCompleteDVR B L E
  let := hS
  let := hBS
  let := hSfin
  let := hSc
  let := hSf
  let : Algebra A S := ((algebraMap B S).comp (algebraMap A B)).toAlgebra
  let : IsScalarTower A B S := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A S E := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A B E, IsScalarTower.algebraMap_apply B S E]
    rfl
  let : IsScalarTower A K E := IsScalarTower.of_algebraMap_eq fun a => by
    apply E.val.injective
    change algebraMap A M a = algebraMap K M (algebraMap A K a)
    exact IsScalarTower.algebraMap_apply A K M a
  let : FaithfulSMul A S := (faithfulSMul_iff_algebraMap_injective A S).mpr
    ((FaithfulSMul.algebraMap_injective B S).comp (FaithfulSMul.algebraMap_injective A B))
  let : IsLocalHom (algebraMap A S) := RingHom.isLocalHom_comp
    (algebraMap B S) (algebraMap A B)
  let : IsDiscreteValuationRing.IsExtension A S := ⟨⟩
  let : Algebra S M := ((algebraMap E M).comp (algebraMap S E)).toAlgebra
  let : @IsScalarTower S E M
      (inferInstance : Algebra S E).toSMul (inferInstance : Algebra E M).toSMul
      (inferInstance : Algebra S M).toSMul := IsScalarTower.of_algebraMap_eq' rfl
  let : @IsScalarTower B S M
      (inferInstance : Algebra B S).toSMul (inferInstance : Algebra S M).toSMul
      (inferInstance : Algebra B M).toSMul := IsScalarTower.of_algebraMap_eq fun b => by
    rw [IsScalarTower.algebraMap_apply B E M, IsScalarTower.algebraMap_apply B S E]
    rfl
  let f : S →ₐ[B] C := IsIntegralClosure.lift B C M
  let : Algebra S C := f.toRingHom.toAlgebra
  let : IsScalarTower B S C := IsScalarTower.of_algebraMap_eq fun b => (f.commutes b).symm
  let : @IsScalarTower S C M
      (inferInstance : Algebra S C).toSMul (inferInstance : Algebra C M).toSMul
      (inferInstance : Algebra S M).toSMul := IsScalarTower.of_algebraMap_eq fun s =>
        (IsIntegralClosure.algebraMap_lift B C M s).symm
  let : IsScalarTower A S C := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A B C, IsScalarTower.algebraMap_apply B S C]
    rfl
  let : FaithfulSMul S C := (faithfulSMul_iff_algebraMap_injective S C).mpr fun x y h => by
    apply IsFractionRing.injective S E
    apply (algebraMap E M).injective
    have h' := congrArg (algebraMap C M) h
    rw [← IsScalarTower.algebraMap_apply S C M, ← IsScalarTower.algebraMap_apply S C M] at h'
    exact h'
  let : IsLocalHom (algebraMap S C) := isLocalHom_of_isIntegral_tower B S C
  let : IsDiscreteValuationRing.IsExtension S C := ⟨⟩
  have hsol := hfirst A B S K L E hweak hresidue le_rfl hcyclo
  exact exists_finite_extension_isWeakSolution_of_normal_factor_induction p A S C K E M
    (residueField_forall_exists_pow_iff_of_finite A B S p hresidue) hcyclo hsol hnext

/-- Strong induction on the degree proves elimination for a normal top extension
once a cyclotomic parameter is available in mixed characteristic. -/
private theorem normalTowerSolvable (p : ℕ) [Fact p.Prime] (n : ℕ) :
    NormalTowerSolvable.{u} p n := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A B C K L M
    intros
    rename_i hweak hfinite hresidue hnormal hdegree hcyclo
    have := isScalarTower_of_isScalarTower_top A B C M
    obtain ⟨_, _, _⟩ := isIntegralClosure_and_finite_and_isAdicComplete B C L M
    have hself (hBC : IsDiscreteValuationRing.IsWeaklyUnramified B C) :
        ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
          (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
          ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{u,u,u,u,u,u,u,u} A C K M K₁,
            D.IsWeakSolution := by
      obtain ⟨D⟩ := nonempty_integralClosureBaseChange A C K M K
      exact ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
        D, isWeakSolution_self A C K M D (isWeaklyUnramified_trans A B C hweak hBC)⟩
    by_cases h1 : Module.finrank L M = 1
    · apply hself
      have hd := ramificationIdx_dvd_finrank_of_isLocalRing B C
      rw [← IsFractionRing.finrank_eq B L C M, h1] at hd
      exact (isWeaklyUnramified_iff_ramificationIdx_eq_one B C).mpr
        (Nat.dvd_one.mp hd)
    have hnontriv : 1 < Module.finrank L M := lt_of_le_of_ne Module.finrank_pos (Ne.symm h1)
    by_cases hproper : ∃ E : IntermediateField L M, Normal L E ∧ E ≠ ⊥ ∧ E ≠ ⊤
    · obtain ⟨E, hE, hbot, htop⟩ := hproper
      let := hE
      have hE1 : 1 < Module.finrank L E := lt_of_le_of_ne Module.finrank_pos
        (Ne.symm fun h => hbot (IntermediateField.finrank_eq_one_iff.mp h))
      have hE2 : 1 < Module.finrank E M := lt_of_le_of_ne Module.finrank_pos
        (Ne.symm fun h => htop (IntermediateField.finrank_eq_one_iff_eq_top.mp h))
      have hmul := Module.finrank_mul_finrank L E M
      have hlt1 : Module.finrank L E < n := by nlinarith
      have hlt2 : Module.finrank E M < n := by nlinarith
      exact exists_finite_extension_isWeakSolution_of_intermediateField_induction
        p A B C K L M hresidue hweak hcyclo E
        (ih _ hlt1) (ih _ hlt2)
    have htriv (E : IntermediateField L M) [Normal L E] : E = ⊥ ∨ E = ⊤ := by
      by_contra! h
      exact hproper ⟨E, inferInstance, h⟩
    rcases htriv (separableClosure L M) with hsep | hsep
    · let : IsPurelyInseparable L M := separableClosure.eq_bot_iff.mp hsep
      have hchar : CharP L p := by
        rcases charZero_or_charP_of_injective (algebraMap A L)
          (by rw [IsScalarTower.algebraMap_eq A K L]
              exact (algebraMap K L).injective.comp (IsFractionRing.injective A K))
          (IsLocalRing.residue A) p with hc | hc
        · let := hc
          exact False.elim (h1 (Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
            (IsPurelyInseparable.bijective_algebraMap_of_isSeparable L M)))
        · exact hc
      let := hchar
      have hbot : (⊥ : IntermediateField L M) ≠ ⊤ := by
        intro h
        apply h1
        have := congrArg (fun E : IntermediateField L M => Module.finrank L E) h
        simpa using this.symm
      obtain ⟨y, -, hy⟩ := exists_intermediateField_finrank_eq_of_isPurelyInseparable L M p hbot
      let E := IntermediateField.adjoin L {y}
      let : IsPurelyInseparable L E := IsPurelyInseparable.tower_bot L E M
      have hEtop : E = ⊤ := (htriv E).resolve_left fun h => by
        have he := IntermediateField.finrank_eq_one_iff.mpr h
        change Module.finrank L (IntermediateField.adjoin L {y}) = 1 at he
        rw [hy] at he
        exact (Fact.out : p.Prime).ne_one he
      have hdeg : Module.finrank L M = p := by
        have he : Module.finrank L E = Module.finrank L M := by rw [hEtop]; simp
        exact he.symm.trans hy
      exact exists_finite_extension_isWeakSolution_of_prime_degree
        p A B C K L M hresidue hweak hcyclo (Or.inl ⟨inferInstance, hdeg⟩)
    · let : Algebra.IsSeparable L M := (separableClosure.eq_top_iff L M).mp hsep
      let : IsGalois L M := ⟨⟩
      let R := integralClosure B M
      let : IsDiscreteValuationRing R :=
        (isDiscreteValuationRing_and_finite_integralClosure_of_isAdicComplete B L M).1
      let := IsIntegralClosure.MulSemiringAction B L M R
      let P := IsLocalRing.maximalIdeal R
      let I := P.inertia Gal(M/L)
      let : I.Normal := normal_inertia_maximalIdeal Gal(M/L) R
      let E := IntermediateField.fixedField I
      rcases htriv E with hE | hE
      · have hI : I = ⊤ := by
          have h := IsGalois.fixedField_eq_iff_fixingSubgroup_eq.mp hE
          simpa only [IntermediateField.fixingSubgroup_bot] using h.symm
        let : CharP (IsLocalRing.ResidueField B) p := charP_of_injective_algebraMap
          (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)).injective p
        have hsolI : Group.IsSolvable I := isSolvable_inertia B L M p P
        rw [hI] at hsolI
        let := hsolI
        let : Group.IsSolvable Gal(M/L) := Group.isSolvable_of_surjective
          (f := (Subgroup.topEquiv : (⊤ : Subgroup Gal(M/L)) ≃* Gal(M/L)).toMonoidHom)
          Subgroup.topEquiv.surjective
        obtain ⟨E', hgal, hp, hcyc, -, -, -⟩ :=
          exists_intermediateField_prime_finrank_of_isSolvable L M hnontriv
        let := hgal
        have htop : E' = ⊤ := (htriv E').resolve_left fun h =>
          hp.ne_one (IntermediateField.finrank_eq_one_iff.mpr h)
        have hp' : (Module.finrank L M).Prime := by
          have he := ((IntermediateField.equivOfEq htop).trans
            (IntermediateField.topEquiv :
              (⊤ : IntermediateField L M) ≃ₐ[L] M)).toLinearEquiv.finrank_eq
          exact he ▸ hp
        exact exists_finite_extension_isWeakSolution_of_prime_degree
          p A B C K L M hresidue hweak hcyclo (Or.inr ⟨inferInstance, hp'⟩)
      · let eE : E ≃ₐ[L] M := (IntermediateField.equivOfEq hE).trans IntermediateField.topEquiv
        let eR := (eE.restrictScalars B).mapIntegralClosure
        let : IsLocalRing (integralClosure B E) := eR.symm.toRingEquiv.isLocalRing
        let : Algebra.FormallyUnramified B (integralClosure B E) :=
          formallyUnramified_integralClosure_fixedField_inertia B L M inferInstance
        let : Algebra.FormallyUnramified B C := Algebra.FormallyUnramified.of_equiv
          (eR.trans (IsIntegralClosure.equiv B R M C))
        exact hself (isWeaklyUnramified_of_formallyUnramified B C)


set_option backward.isDefEq.respectTransparency false in
/-- After a finite extension of a characteristic-zero field, its integral
closure contains a cyclotomic ring.

Pure field theory over a characteristic-zero base: no discrete valuation rings, no residue
fields. -/
theorem exists_finite_extension_nonempty_cyclotomicRingHom
    (A : Type*) (K : Type u) [CommRing A] [Field K] [CharZero K] [Algebra A K]
    (n : ℕ) [NeZero n] :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : Algebra A E)
      (_ : IsScalarTower A K E) (_ : Module.Finite K E),
      Nonempty (CyclotomicRing n ℤ ℚ →+* integralClosure A E) := by
  let E := CyclotomicField n K
  let : Module.Finite K E := Polynomial.IsSplittingField.instFiniteDimensionalSplittingField _
  let : Polynomial.IsSplittingField ℚ (CyclotomicField n ℚ) (Polynomial.cyclotomic n ℚ) := by
    unfold CyclotomicField
    infer_instance
  let f₀ : CyclotomicField n ℚ →ₐ[ℚ] E :=
    Polynomial.IsSplittingField.lift (CyclotomicField n ℚ) (Polynomial.cyclotomic n ℚ) (by
      rw [Polynomial.map_cyclotomic]
      simpa only [Polynomial.map_cyclotomic] using
        (IsCyclotomicExtension.splits_cyclotomic K E (Set.mem_singleton n)))
  let f : CyclotomicRing n ℤ ℚ →+* E :=
    f₀.toRingHom.comp (algebraMap (CyclotomicRing n ℤ ℚ) (CyclotomicField n ℚ))
  let : Module.Finite ℤ (CyclotomicRing n ℤ ℚ) :=
    IsCyclotomicExtension.finite_of_singleton n ℤ (CyclotomicRing n ℤ ℚ)
  let g : CyclotomicRing n ℤ ℚ →+* integralClosure A E :=
    f.codRestrict (integralClosure A E).toSubring fun x =>
      ((IsIntegral.of_finite ℤ x).map f.toIntAlgHom).tower_top
  exact ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ⟨g⟩⟩

private theorem exists_finite_extension_isWeakSolution_of_normal_same_universe
    (p : ℕ) [Fact p.Prime]
    (A B C K L M : Type u)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M]
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
    [CharP (IsLocalRing.ResidueField A) p]
    [IsAlgClosed (IsLocalRing.ResidueField A)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [Module.Finite L M]
    (hresidue : ∀ x : IsLocalRing.ResidueField B,
      (∃ a : IsLocalRing.ResidueField A,
          algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) a = x) ↔
        ∀ n : ℕ, 1 ≤ n → ∃ y : IsLocalRing.ResidueField B, y ^ (p ^ n) = x)
    [Normal L M]
    (hweak : IsDiscreteValuationRing.IsWeaklyUnramified A B)
 :
    ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{u,u,u,u,u,u,u,u} A C K M K₁,
        D.IsWeakSolution
 := by
  classical
  by_cases hc : CharZero K
  · let := hc
    let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    obtain ⟨E, hE, hKE, hAE, htower, hfin, hf⟩ :=
      exists_finite_extension_nonempty_cyclotomicRingHom A K p
    let := hE
    let := hKE
    let := hAE
    let := htower
    let := hfin
    obtain ⟨D₀⟩ := nonempty_integralClosureBaseChange A B K L K
    obtain ⟨D₁⟩ := nonempty_integralClosureBaseChange A B K L E
    have hD₁ : D₁.IsWeakSolution := isWeakSolution_of_finite_extension A B K L K E
      D₀ D₁ (isWeakSolution_self A B K L D₀ hweak)
    exact exists_finite_extension_isWeakSolution_of_normal_factor_induction_of_cyclotomic_extension
      p A B C K L M hresidue
      ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
        D₁, hD₁, fun _ => hf⟩
      (normalTowerSolvable p (Module.finrank L M))
  · exact normalTowerSolvable p (Module.finrank L M) A B C K L M hweak hresidue
      le_rfl (fun h => False.elim (hc h))

private theorem exists_finite_extension_isWeakSolution_of_same_universe
    (p : ℕ) [Fact p.Prime]
    (A B C K L M : Type u)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M]
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
    [CharP (IsLocalRing.ResidueField A) p]
    [IsAlgClosed (IsLocalRing.ResidueField A)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [Module.Finite L M]
    (hresidue : ∀ x : IsLocalRing.ResidueField B,
      (∃ a : IsLocalRing.ResidueField A,
          algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) a = x) ↔
        ∀ n : ℕ, 1 ≤ n → ∃ y : IsLocalRing.ResidueField B, y ^ (p ^ n) = x)
    (hweak : IsDiscreteValuationRing.IsWeaklyUnramified A B)
 :
    ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{u,u,u,u,u,u,u,u} A C K M K₁,
        D.IsWeakSolution
 := by
  apply exists_finite_extension_isWeakSolution_of_normal A B C K L M p hweak hresidue
  intro C' N
  intros
  exact exists_finite_extension_isWeakSolution_of_normal_same_universe
    p A B C' K L N hresidue hweak

attribute [local instance] ULift.algebra'

/-- Epp's theorem in the complete case: under the residue-field intersection
hypothesis, every finite extension at the top of a weakly unramified tower admits
a finite base extension which is a weak solution for the full tower. -/
@[stacks 09F8]
theorem exists_finite_extension_isWeakSolution
    (A : Type uA) (B : Type uB) (C : Type uC)
    (K : Type uK) (L : Type uL) (M : Type uM)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M]
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
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    [IsAlgClosed (IsLocalRing.ResidueField A)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (hweak : IsDiscreteValuationRing.IsWeaklyUnramified A B)
    [Module.Finite L M]
    (hresidue : ∀ x : IsLocalRing.ResidueField B,
      (∃ a : IsLocalRing.ResidueField A,
          algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) a = x) ↔
        ∀ n : ℕ, 1 ≤ n → ∃ y : IsLocalRing.ResidueField B, y ^ (p ^ n) = x) :
    ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA, uC, uK, uM, uK,
          max uM uK, uK, max uM uK} A C K M K₁,
        D.IsWeakSolution := by
  classical
  let A' := ULift.{max uA uB uC uK uL uM} A
  let B' := ULift.{max uA uB uC uK uL uM} B
  let C' := ULift.{max uA uB uC uK uL uM} C
  let K' := ULift.{max uA uB uC uK uL uM} K
  let L' := ULift.{max uA uB uC uK uL uM} L
  let M' := ULift.{max uA uB uC uK uL uM} M
  let : IsDomain A' := MulEquiv.isDomain A (ULift.ringEquiv (R := A)).toMulEquiv
  let : IsDomain B' := MulEquiv.isDomain B (ULift.ringEquiv (R := B)).toMulEquiv
  let : IsDomain C' := MulEquiv.isDomain C (ULift.ringEquiv (R := C)).toMulEquiv
  let : IsDiscreteValuationRing A' :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (ULift.ringEquiv (R := A)).symm
  let : IsDiscreteValuationRing B' :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (ULift.ringEquiv (R := B)).symm
  let : IsDiscreteValuationRing C' :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (ULift.ringEquiv (R := C)).symm
  let : IsDiscreteValuationRing.IsExtension A' B' := isExtension_of_equiv A B A' B'
    (ULift.ringEquiv (R := A)).symm (ULift.ringEquiv (R := B)).symm (fun _ => rfl)
  let : IsDiscreteValuationRing.IsExtension B' C' := isExtension_of_equiv B C B' C'
    (ULift.ringEquiv (R := B)).symm (ULift.ringEquiv (R := C)).symm (fun _ => rfl)
  let : IsDiscreteValuationRing.IsExtension A' C' := isExtension_of_equiv A C A' C'
    (ULift.ringEquiv (R := A)).symm (ULift.ringEquiv (R := C)).symm (fun _ => rfl)
  let : Module.Finite A A' :=
    Module.Finite.equiv (ULift.algEquiv (R := A) (A := A)).symm.toLinearEquiv
  let : Module.Finite B B' :=
    Module.Finite.equiv (ULift.algEquiv (R := B) (A := B)).symm.toLinearEquiv
  let : Module.Finite C C' :=
    Module.Finite.equiv (ULift.algEquiv (R := C) (A := C)).symm.toLinearEquiv
  let : IsLocalHom (algebraMap A A') := Algebra.IsIntegral.isLocalHom A A'
  let : IsLocalHom (algebraMap B B') := Algebra.IsIntegral.isLocalHom B B'
  let : IsLocalHom (algebraMap C C') := Algebra.IsIntegral.isLocalHom C C'
  let : IsDiscreteValuationRing.IsExtension A A' := ⟨⟩
  let : IsDiscreteValuationRing.IsExtension B B' := ⟨⟩
  let : IsLocalHom (algebraMap A B') := by
    rw [IsScalarTower.algebraMap_eq A B B']
    infer_instance
  let : IsAdicComplete (IsLocalRing.maximalIdeal A') A' := isAdicComplete_of_finite A A'
  let : IsAdicComplete (IsLocalRing.maximalIdeal B') B' := isAdicComplete_of_finite B B'
  let : IsAlgClosed (IsLocalRing.ResidueField A') := isAlgClosed_residueField_of_finite A A'
  let : CharP (IsLocalRing.ResidueField A') p := charP_of_injective_algebraMap
    (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A')).injective p
  let : IsFractionRing A K' := IsFractionRing.of_algEquiv (ULift.algEquiv (R := A) (A := K)).symm
  let : IsFractionRing B L' := IsFractionRing.of_algEquiv (ULift.algEquiv (R := B) (A := L)).symm
  let : IsFractionRing C M' := IsFractionRing.of_algEquiv (ULift.algEquiv (R := C) (A := M)).symm
  let : IsFractionRing A' K' := IsFractionRing.of_ringEquiv_left
    (ULift.ringEquiv (R := A)) (fun _ => rfl)
  let : IsFractionRing B' L' := IsFractionRing.of_ringEquiv_left
    (ULift.ringEquiv (R := B)) (fun _ => rfl)
  let : IsFractionRing C' M' := IsFractionRing.of_ringEquiv_left
    (ULift.ringEquiv (R := C)) (fun _ => rfl)
  let : Module.Finite L M' := Module.Finite.equiv
    (ULift.algEquiv (R := L) (A := M)).symm.toLinearEquiv
  let : Module.Finite L' M' := Module.Finite.of_restrictScalars_finite L L' M'
  have hw : IsDiscreteValuationRing.IsWeaklyUnramified A' B' :=
    isWeaklyUnramified_of_equiv A B A' B'
      (ULift.ringEquiv (R := A)).symm (ULift.ringEquiv (R := B)).symm (fun _ => rfl) hweak
  have hr := residueField_forall_exists_pow_iff_of_finite_square A B A' B' p hresidue
  obtain ⟨E, hE, hKE, hAE, htower, hfin, D, hD⟩ :=
    exists_finite_extension_isWeakSolution_of_same_universe p A' B' C' K' L' M' hr hw
  let := hE
  let := hKE
  let := hAE
  let := htower
  let := hfin
  let aKE : Algebra K E := ((algebraMap K' E).comp (algebraMap K K')).toAlgebra
  have hKK : @IsScalarTower K K' E
      (inferInstance : Algebra K K').toSMul (inferInstance : Algebra K' E).toSMul
      (inferInstance : Algebra K E).toSMul := IsScalarTower.of_algebraMap_eq' rfl
  have hKEeq : hKE = ULift.algebra' K E := by
    apply Algebra.algebra_ext
    intro x
    cases x
    rfl
  clear_value aKE
  cases hKEeq
  let : Algebra A E := ((algebraMap K E).comp (algebraMap A K)).toAlgebra
  let : IsScalarTower A K E := IsScalarTower.of_algebraMap_eq' rfl
  let : @IsScalarTower A K' E
      (inferInstance : Algebra A K').toSMul (inferInstance : Algebra K' E).toSMul
      (inferInstance : Algebra A E).toSMul := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Module.Finite K K' :=
    Module.Finite.equiv (ULift.algEquiv (R := K) (A := K)).symm.toLinearEquiv
  let : Module.Finite K E := Module.Finite.trans (R := K) K' E
  obtain ⟨D', hD'⟩ := exists_isWeakSolution_of_integral_ring_extension A C A' C' K' M' E
    (fun a => by
      rw [IsScalarTower.algebraMap_apply A' K' E]
      rfl) (fun _ => rfl) D hD
  obtain ⟨D'', hD''⟩ := exists_isWeakSolution_of_ulift_fraction_fields
    A C K M E D' hD'
  obtain ⟨_, _, _⟩ := isIntegralClosure_and_finite_and_isAdicComplete B C L M
  obtain ⟨F, hF, hKF, hAF, htowerF, hfinF, hDF⟩ :=
    exists_finite_extension_forall_isWeakSolution A K (fun _ : Fin 1 => C)
      (fun _ => M) (fun _ => E) (fun _ => D'') (fun _ => hD'')
  obtain ⟨DF, hDF⟩ := hDF 0
  exact ⟨F, hF, hKF, hAF, htowerF, hfinF, DF, hDF⟩

end IsDiscreteValuationRing
