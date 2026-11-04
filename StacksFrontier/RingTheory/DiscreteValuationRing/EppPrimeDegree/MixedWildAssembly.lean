module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppConstantNumeratorFamily
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedResidueAbsorption
public import StacksFrontier.RingTheory.DiscreteValuationRing.RamificationTower
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppPrimeDegree.MixedFiniteLevel
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppPrimeDegree.WildCharP

open Stacks.DegreePExtensionLevel
open Stacks.DiscreteValuationRing.EppLevelInduction

/-!
# Prime-degree input: the mixed wild case and the final assembly

The cyclotomic entry point of the mixed-characteristic solver, the mixed wild prime-degree
solver, and the assembly of the family tower solvability and Epp's theorem for perfect fields.
-/

@[expose] public section

open IsLocalRing
open IsDiscreteValuationRing
open scoped TensorProduct

namespace Stacks.EppTheorem

universe u v w uΩ

/-- The cyclotomic entry point for the mixed-characteristic degree-`p` solver.  The first
totally ramified step either solves the tower immediately or produces the finite-level
presentation consumed above. -/
private theorem exists_finite_extension_isWeakSolution_of_mixedCyclotomic
    (p : ℕ) [Fact p.Prime]
    (A B C K L M : Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Field L] [Field M]
    [Algebra A B] [Algebra B C] [Algebra A C] [Algebra A K]
    [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra B M] [Algebra A M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsExtension A B] [IsExtension B C] [IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    [CharZero K] [CharP (ResidueField A) p] [ExpChar (ResidueField B) p]
    [PerfectField (ResidueField A)]
    [IsAdicComplete (maximalIdeal A) A]
    [IsAdicComplete (maximalIdeal B) B]
    (hweak : IsWeaklyUnramified A B)
    (hepp : EppCondition A B p)
    [Module.Finite L M] [IsGalois L M]
    (hdegree : Module.finrank L M = p)
    (f : CyclotomicRing p ℤ ℚ →+* B) :
    ∃ (K2 : Type u) (_ : Field K2) (_ : Algebra K K2) (_ : Algebra A K2)
      (_ : IsScalarTower A K K2) (_ : Module.Finite K K2),
      ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A C K M K2,
        D.IsWeakSolution := by
  obtain ⟨K1, hK1, hKK1, hAK1, hAKK1, hfinK1, htot, hnext⟩ :=
    exists_totallyRamified_galoisExtension_isWeakSolution_or_finiteLevel
      A B C K L M p hweak f hdegree
  let := hK1
  let := hKK1
  let := hAK1
  let := hAKK1
  let := hfinK1
  rcases hnext with ⟨D, hD⟩ | hnext
  · exact ⟨K1, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, D, hD⟩
  · obtain ⟨hL1, hM1, hB1, _hfrac, hfin1, P, hint, hquot, hshape, hfunc, hfinite1⟩ := hnext
    apply exists_finite_extension_isWeakSolution_of_totallyRamified_tensorProduct_of_perfectResidue
      A B C K L M K1 p hweak htot hL1 hM1 hfin1
    let fieldL1 := hL1.toField
    let fieldM1 := hM1.toField
    let algL1M1 : Algebra (L ⊗[K] K1) (M ⊗[K] K1) :=
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M)
        (AlgHom.id K K1)).toRingHom.toAlgebra
    let algK1L1 : Algebra K1 (L ⊗[K] K1) := Algebra.TensorProduct.rightAlgebra
    let algK1M1 : Algebra K1 (M ⊗[K] K1) := Algebra.TensorProduct.rightAlgebra
    dsimp only
    intro hA1dvr hB1dvr hC1dvr algA1B1 algB1C1 algA1C1
      towerA1B1C1 towerA1B1L1 towerA1K1L1 towerB1C1M1 towerB1L1M1
      towerA1C1M1 towerA1K1M1 towerK1L1M1 extA1B1 extB1C1 extA1C1
      fracA1 fracB1 fracC1 completeA1 completeB1 perfectA1 charPA1 finiteL1M1 hweak1
    let algA1L1 : Algebra (integralClosure A K1) (L ⊗[K] K1) :=
      ((algebraMap K1 (L ⊗[K] K1)).comp
        (algebraMap (integralClosure A K1) K1)).toAlgebra
    let algA1M1 : Algebra (integralClosure A K1) (M ⊗[K] K1) :=
      ((algebraMap K1 (M ⊗[K] K1)).comp
        (algebraMap (integralClosure A K1) K1)).toAlgebra
    let algB1M1 : Algebra (integralClosure B (L ⊗[K] K1)) (M ⊗[K] K1) :=
      ((algebraMap (L ⊗[K] K1) (M ⊗[K] K1)).comp
        (algebraMap (integralClosure B (L ⊗[K] K1)) (L ⊗[K] K1))).toAlgebra
    let := hA1dvr
    let := hB1dvr
    let := hC1dvr
    let := algA1B1
    let := algB1C1
    let := algA1C1
    let := towerA1B1C1
    let := towerA1B1L1
    let := towerA1K1L1
    let := towerB1C1M1
    let := towerB1L1M1
    let := towerA1C1M1
    let := towerA1K1M1
    let := towerK1L1M1
    let := extA1B1
    let := extB1C1
    let := extA1C1
    let := fracA1
    let := fracB1
    let := fracC1
    let := completeA1
    let := completeB1
    let := perfectA1
    let := charPA1
    let := finiteL1M1
    obtain ⟨_, hAA1, hAfin, _, _⟩ := integralClosure_isCompleteDVR A K K1
    obtain ⟨_, hBB1, hBfin, _, _⟩ := integralClosure_isCompleteDVR B L (L ⊗[K] K1)
    let : Module.Finite A (integralClosure A K1) := hAfin
    let : Module.Finite B (integralClosure B (L ⊗[K] K1)) := hBfin
    let : IsExtension A (integralClosure A K1) := hAA1
    let : IsExtension B (integralClosure B (L ⊗[K] K1)) := hBB1
    let : IsLocalHom (algebraMap A (integralClosure A K1)) :=
      Algebra.IsIntegral.isLocalHom A _
    let : IsLocalHom (algebraMap B (integralClosure B (L ⊗[K] K1))) :=
      Algebra.IsIntegral.isLocalHom B _
    let : IsScalarTower A B (integralClosure B (L ⊗[K] K1)) :=
      IsScalarTower.of_algebraMap_eq fun a =>
        Subtype.ext (IsScalarTower.algebraMap_apply A B (L ⊗[K] K1) a)
    let : IsScalarTower A K1 (L ⊗[K] K1) :=
      IsScalarTower.of_algebraMap_eq fun a => by
        show (algebraMap A L a) ⊗ₜ[K] (1 : K1) =
          (1 : L) ⊗ₜ[K] algebraMap A K1 a
        rw [IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A K K1,
          ← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']
    let : IsScalarTower A (integralClosure A K1)
        (integralClosure B (L ⊗[K] K1)) :=
      IsScalarTower.of_algebraMap_eq fun a => by
        apply Subtype.ext
        show algebraMap A (L ⊗[K] K1) a =
          algebraMap (integralClosure B (L ⊗[K] K1)) (L ⊗[K] K1)
            (algebraMap (integralClosure A K1)
              (integralClosure B (L ⊗[K] K1)) (algebraMap A (integralClosure A K1) a))
        rw [← IsScalarTower.algebraMap_apply
            (integralClosure A K1) (integralClosure B (L ⊗[K] K1)) (L ⊗[K] K1),
          IsScalarTower.algebraMap_apply (integralClosure A K1) K1 (L ⊗[K] K1),
          ← IsScalarTower.algebraMap_apply A (integralClosure A K1) K1,
          ← IsScalarTower.algebraMap_apply A K1 (L ⊗[K] K1)]
    let : IsLocalHom (algebraMap A (integralClosure B (L ⊗[K] K1))) := by
      rw [IsScalarTower.algebraMap_eq A B (integralClosure B (L ⊗[K] K1))]
      infer_instance
    let : CharZero K1 := charZero_of_injective_algebraMap (algebraMap K K1).injective
    let : ExpChar (ResidueField (integralClosure B (L ⊗[K] K1))) p :=
      expChar_of_injective_algebraMap
        (algebraMap (ResidueField (integralClosure A K1))
          (ResidueField (integralClosure B (L ⊗[K] K1)))).injective p
    have hepp1 : EppCondition (integralClosure A K1)
        (integralClosure B (L ⊗[K] K1)) p := EppCondition.of_finite_square hepp
    exact exists_finite_extension_isWeakSolution_of_mixedFiniteLevel p
      (integralClosure A K1) (integralClosure B (L ⊗[K] K1))
      (integralClosure C (M ⊗[K] K1)) K1 (L ⊗[K] K1) (M ⊗[K] K1)
      hweak1 hepp1 ((algebraMap B (integralClosure B (L ⊗[K] K1))).comp f)
      (P.map (algebraMap B (integralClosure B (L ⊗[K] K1))))
      (Stacks.DiscreteValuationRing.EppLevelInduction.cyclotomic_properties_map f P ⟨hint, hquot,
        hshape, hfunc⟩ _) hfinite1

/-- The remaining characteristic-zero part of the wild prime-degree obligation.

The equal-characteristic case is already discharged by
`exists_finite_extension_isWeakSolution_of_wild_charP`.  Naming the mixed-characteristic
interface separately prevents the final tower assembly from carrying an artificial
characteristic split and makes the exact remaining producer explicit. -/
abbrev MixedWildPrimeDegreeSolvable (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (A B C K L M : Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Field L] [Field M]
    [Algebra A B] [Algebra B C] [Algebra A C] [Algebra A K]
    [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra B M] [Algebra A M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsExtension A B] [IsExtension B C] [IsExtension A C]
    [IsFractionRing B L] [IsFractionRing C M] [IsFractionRing A K]
    [CharP (ResidueField A) p] [ExpChar (ResidueField B) p]
    [PerfectField (ResidueField A)]
    [IsAdicComplete (maximalIdeal A) A]
    [IsAdicComplete (maximalIdeal B) B]
    [CharZero K]
    (hweak : IsWeaklyUnramified A B)
    [Module.Finite L M] [IsGalois L M]
    (hepp : EppCondition A B p)
    (hdegree : Module.finrank L M = p),
    ∃ (K₂ : Type u) (_ : Field K₂) (_ : Algebra K K₂) (_ : Algebra A K₂)
      (_ : IsScalarTower A K K₂) (_ : Module.Finite K K₂),
      ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A C K M K₂,
        D.IsWeakSolution

/-- The mixed-characteristic wild prime-degree obligation.  First adjoin the cyclotomic
parameter to the base.  The reduced tensor factors of the lower and upper fields are matched;
degree-`p` factors use the finite-level solver, while every strictly smaller factor is tame.  The
finitely many factor solutions are then synchronized and descended to the original tower. -/
theorem mixedWildPrimeDegreeSolvable (p : ℕ) [Fact p.Prime] :
    MixedWildPrimeDegreeSolvable.{u} p := by
  intro A B C K L M
  intros
  rename_i hweak _ hgal hepp hdegree
  classical
  let : IsGalois L M := hgal
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let : IsScalarTower A B M := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A C M, IsScalarTower.algebraMap_apply A B C,
      ← IsScalarTower.algebraMap_apply B C M]
  let : IsIntegralClosure C B M := isIntegralClosure_of_isAdicComplete B C L M
  let : Module.Finite B (integralClosure B M) :=
    (isDiscreteValuationRing_and_finite_integralClosure_of_isAdicComplete B L M).2
  let : Module.Finite B C := Module.Finite.equiv
    (IsIntegralClosure.equiv B (integralClosure B M) M C).toLinearEquiv
  let : IsAdicComplete (maximalIdeal C) C := isAdicComplete_of_finite B C
  obtain ⟨K1, hK1, hKK1, hAK1, hAKK1, hfinK1, hcycloR⟩ :=
    exists_finite_extension_nonempty_cyclotomicRingHom A K p
  let := hK1
  let := hKK1
  let := hAK1
  let := hAKK1
  let := hfinK1
  obtain ⟨D⟩ := nonempty_integralClosureBaseChange A B K L K1
  let := D.commRingL₁
  let := D.algebraKL₁
  let := D.algebraLL₁
  let := D.algebraK₁L₁
  have hD : D.IsWeakSolution :=
    isWeakSolution_of_isWeaklyUnramified_of_perfect_residueField A B K L K1 D hweak
  obtain ⟨D'⟩ := nonempty_integralClosureBaseChange A C K M K1
  let := D'.commRingL₁
  let := D'.algebraKL₁
  let := D'.algebraLL₁
  let := D'.algebraK₁L₁
  obtain ⟨n, H, hH, hLH, hKH, hBH, hAH, hBLH, hABH, hAKH, hfinH, hn, eH, heH⟩ :=
    finiteFieldFactors_compatible A B K L K1 D
  let := hH
  let := hLH
  let := hKH
  let := hBH
  let := hAH
  let := hBLH
  let := hABH
  let := hAKH
  let := hfinH
  obtain ⟨m, F, hF, hMF, hKF, hCF, hAF, hCMF, hACF, hAKF, hfinF, hm, eF, heF⟩ :=
    finiteFieldFactors_compatible A C K M K1 D'
  let := hF
  let := hMF
  let := hKF
  let := hCF
  let := hAF
  let := hCMF
  let := hACF
  let := hAKF
  let := hfinF
  let : ∀ i, Algebra K (H i) := fun i =>
    ((algebraMap K1 (H i)).comp (algebraMap K K1)).toAlgebra
  let : ∀ i, Algebra K (F i) := fun i =>
    ((algebraMap K1 (F i)).comp (algebraMap K K1)).toAlgebra
  let : ∀ i, IsScalarTower K K1 (H i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, IsScalarTower K K1 (F i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra K1 (L ⊗[K] K1) := Algebra.TensorProduct.rightAlgebra
  let : Algebra K1 (M ⊗[K] K1) := Algebra.TensorProduct.rightAlgebra
  let : Algebra K1 (ReducedTensorTower.Reduction (L ⊗[K] K1)) :=
    Ideal.Quotient.algebra K1
  let : Algebra K1 (ReducedTensorTower.Reduction (M ⊗[K] K1)) :=
    Ideal.Quotient.algebra K1
  let eH' := reducedTensorFactorsEquiv K L K1 D.L₁ H D.eL₁ eH D.eL₁_right heH
  let eF' := reducedTensorFactorsEquiv K M K1 D'.L₁ F D'.eL₁ eF D'.eL₁_right heF
  let phi (i : Fin m) : (M ⊗[K] K1) →ₐ[K1] F i :=
    ((Pi.evalAlgHom K1 F i).comp eF'.toAlgHom).comp (Ideal.Quotient.mkₐ K1 _)
  have hphiLeft (i : Fin m) (x : M) :
      phi i (x ⊗ₜ[K] (1 : K1)) = algebraMap M (F i) x :=
    reducedTensorFactorsEquiv_left K M K1 D'.L₁ F D'.eL₁ eF D'.eL₁_right heF
      D'.eL₁_left x i
  have hphiRight (i : Fin m) (x : K1) :
      phi i ((1 : M) ⊗ₜ[K] x) = algebraMap K1 (F i) x := (phi i).commutes x
  have hphi (i : Fin m) (x : M) (y : K1) :
      phi i (x ⊗ₜ[K] y) = algebraMap M (F i) x * algebraMap K1 (F i) y := by
    rw [show x ⊗ₜ[K] y = (x ⊗ₜ[K] (1 : K1)) * ((1 : M) ⊗ₜ[K] y) by
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul],
      map_mul, hphiLeft, hphiRight]
  have hphiSurj (i : Fin m) : Function.Surjective (phi i) := by
    have hev : Function.Surjective (Pi.evalAlgHom K1 F i) := fun x =>
      ⟨Pi.single i x, by simp⟩
    exact hev.comp (eF'.surjective.comp Ideal.Quotient.mk_surjective)
  let : ∀ i, IsScalarTower K M (F i) := fun i => IsScalarTower.of_algebraMap_eq fun x => by
    have hx := congrArg (phi i) ((Algebra.TensorProduct.algebraMap_apply (R := K) (A := M)
      (B := K1) x).symm.trans (Algebra.TensorProduct.algebraMap_apply' x))
    rw [hphiLeft, hphiRight] at hx
    exact hx.symm
  let : ∀ i, Algebra L (F i) := fun i =>
    ((algebraMap M (F i)).comp (algebraMap L M)).toAlgebra
  let : ∀ i, IsScalarTower L M (F i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, IsScalarTower K L (F i) := fun i => IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply K M (F i), IsScalarTower.algebraMap_apply K L M]
    rfl
  let : ∀ i, Algebra B (F i) := fun i =>
    ((algebraMap M (F i)).comp (algebraMap B M)).toAlgebra
  let : ∀ i, IsScalarTower B M (F i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, IsScalarTower B L (F i) := fun i => IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply B M (F i), IsScalarTower.algebraMap_apply B L M]
    rfl
  let : ∀ i, IsScalarTower B C (F i) := fun i => IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply B M (F i), IsScalarTower.algebraMap_apply B C M,
      ← IsScalarTower.algebraMap_apply C M (F i)]
  let : ∀ i, IsScalarTower A B (F i) := fun i => IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply A C (F i), IsScalarTower.algebraMap_apply A B C,
      ← IsScalarTower.algebraMap_apply B C (F i)]
  have hfac (i : Fin m) := exists_fieldFactor_normal_and_finrank_le K L M K1 (F i) H eH'
    (fun j x => reducedTensorFactorsEquiv_left K L K1 D.L₁ H D.eL₁ eH
      D.eL₁_right heH D.eL₁_left x j) (phi i) (hphi i) (hphiSurj i)
  choose j g hLHFin hfinHF hnormal hbound using hfac
  let : ∀ i, Algebra (H (j i)) (F i) := fun i => (g i).toRingHom.toAlgebra
  let : ∀ i, IsScalarTower L (H (j i)) (F i) := hLHFin
  let : ∀ i, IsScalarTower K1 (H (j i)) (F i) := fun i => IsScalarTower.of_algHom (g i)
  let := hfinHF
  let := hnormal
  let : ∀ i, IsScalarTower B (H (j i)) (F i) := fun i =>
    IsScalarTower.of_algebraMap_eq fun b => by
      rw [IsScalarTower.algebraMap_apply B L (F i),
        IsScalarTower.algebraMap_apply L (H (j i)) (F i),
        ← IsScalarTower.algebraMap_apply B L (H (j i))]
  let R := integralClosure A K1
  let S (i : Fin m) := integralClosure B (H (j i))
  let T (i : Fin m) := integralClosure C (F i)
  obtain ⟨hR, hAR, hRfin, hRc, hRf⟩ := integralClosure_isCompleteDVR A K K1
  let := hR
  let := hAR
  let := hRfin
  let := hRc
  let := hRf
  have hS (i : Fin m) := integralClosure_isCompleteDVR B L (H (j i))
  choose hS hBS hSfin hSc hSf using hS
  let := hS
  let := hBS
  let := hSfin
  let := hSc
  let := hSf
  have hT (i : Fin m) := integralClosure_isCompleteDVR C M (F i)
  choose hT hCT hTfin hTc hTf using hT
  let := hT
  let := hCT
  let := hTfin
  let := hTc
  let := hTf
  let : ∀ i, Algebra B (T i) := fun i =>
    ((algebraMap C (T i)).comp (algebraMap B C)).toAlgebra
  let : ∀ i, IsScalarTower B C (T i) :=
    fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, Module.Finite B (T i) := fun i => Module.Finite.trans C (T i)
  let f (i : Fin m) := mapIntegralClosureOfTower A B K1 (H (j i))
  let h (i : Fin m) := mapIntegralClosureOfTower A C K1 (F i)
  let t (i : Fin m) := mapIntegralClosureOfTower B C (H (j i)) (F i)
  let : ∀ i, Algebra R (S i) := fun i => (f i).toRingHom.toAlgebra
  let : ∀ i, Algebra R (T i) := fun i => (h i).toRingHom.toAlgebra
  let : ∀ i, Algebra (S i) (T i) := fun i => (t i).toRingHom.toAlgebra
  let : ∀ i, Algebra R (H (j i)) := fun i =>
    ((algebraMap K1 (H (j i))).comp (algebraMap R K1)).toAlgebra
  let : ∀ i, Algebra R (F i) := fun i =>
    ((algebraMap K1 (F i)).comp (algebraMap R K1)).toAlgebra
  let : ∀ i, Algebra (S i) (F i) := fun i =>
    ((algebraMap (H (j i)) (F i)).comp (algebraMap (S i) (H (j i)))).toAlgebra
  let : ∀ i, @IsScalarTower R K1 (H (j i))
      (inferInstance : Algebra R K1).toSMul (inferInstance : Algebra K1 (H (j i))).toSMul
      (inferInstance : Algebra R (H (j i))).toSMul :=
    fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, @IsScalarTower R K1 (F i)
      (inferInstance : Algebra R K1).toSMul (inferInstance : Algebra K1 (F i)).toSMul
      (inferInstance : Algebra R (F i)).toSMul :=
    fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, @IsScalarTower (S i) (H (j i)) (F i)
      (inferInstance : Algebra (S i) (H (j i))).toSMul
      (inferInstance : Algebra (H (j i)) (F i)).toSMul
      (inferInstance : Algebra (S i) (F i)).toSMul :=
    fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, @IsScalarTower R (S i) (H (j i))
      (inferInstance : Algebra R (S i)).toSMul
      (inferInstance : Algebra (S i) (H (j i))).toSMul
      (inferInstance : Algebra R (H (j i))).toSMul :=
    fun _ => IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : ∀ i, @IsScalarTower (S i) (T i) (F i)
      (inferInstance : Algebra (S i) (T i)).toSMul
      (inferInstance : Algebra (T i) (F i)).toSMul
      (inferInstance : Algebra (S i) (F i)).toSMul :=
    fun _ => IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : ∀ i, IsScalarTower B (S i) (T i) :=
    fun i => IsScalarTower.of_algebraMap_eq fun b => by
      apply Subtype.ext
      show algebraMap C (F i) (algebraMap B C b) =
        algebraMap (H (j i)) (F i) (algebraMap B (H (j i)) b)
      rw [← IsScalarTower.algebraMap_apply B C (F i),
        ← IsScalarTower.algebraMap_apply B (H (j i)) (F i)]
  let : ∀ i, Module.Finite (S i) (T i) := fun i =>
    Module.Finite.of_restrictScalars_finite B (S i) (T i)
  let : ∀ i, @IsScalarTower R (T i) (F i)
      (inferInstance : Algebra R (T i)).toSMul
      (inferInstance : Algebra (T i) (F i)).toSMul
      (inferInstance : Algebra R (F i)).toSMul :=
    fun _ => IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : ∀ i, @IsScalarTower R (S i) (T i)
      (inferInstance : Algebra R (S i)).toSMul
      (inferInstance : Algebra (S i) (T i)).toSMul
      (inferInstance : Algebra R (T i)).toSMul := fun i =>
    IsScalarTower.of_algebraMap_eq fun a =>
      Subtype.ext (IsScalarTower.algebraMap_apply K1 (H (j i)) (F i) a.1)
  let : ∀ i, IsScalarTower A R (S i) := fun i =>
    IsScalarTower.of_algebraMap_eq fun a => ((f i).commutes a).symm
  let : ∀ i, IsExtension R (S i) := fun i =>
    (integralClosure_factor_isExtension A B K L K1 (H (j i))).choose_spec.choose_spec.1
  let : ∀ i, IsExtension R (T i) := fun i =>
    (integralClosure_factor_isExtension A C K M K1 (F i)).choose_spec.choose_spec.1
  let : ∀ i, IsExtension (S i) (T i) := fun i =>
    (integralClosure_factor_isExtension B C L M (H (j i)) (F i)).choose_spec.choose_spec.1
  let : PerfectField (ResidueField R) := perfectField_residueField_of_isIntegral A R
  let : CharP (ResidueField R) p := CharP.of_ringHom_of_ne_zero
    (algebraMap (ResidueField A) (ResidueField R)) p (Fact.out : p.Prime).ne_zero
  have hweakRS (i : Fin m) : IsWeaklyUnramified R (S i) :=
    (isWeaklyUnramified_iff_ramificationIdx_eq_one R (S i)).mpr
      (isWeakSolution_factor A B K L K1 D H eH heH hD (j i)
        (IsLocalRing.maximalIdeal (S i)) (IsLocalRing.maximalIdeal.isMaximal _))
  let : ∀ i, IsLocalHom (algebraMap A (S i)) := fun i => by
    rw [IsScalarTower.algebraMap_eq A B (S i)]
    infer_instance
  have hsol (i : Fin m) :
      ∃ (E2 : Type u) (_ : Field E2) (_ : Algebra K1 E2) (_ : Algebra R E2)
        (_ : @IsScalarTower R K1 E2
          (inferInstance : Algebra R K1).toSMul
          (inferInstance : Algebra K1 E2).toSMul
          (inferInstance : Algebra R E2).toSMul) (_ : Module.Finite K1 E2),
        ∃ D2 : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u}
          R (T i) K1 (F i) E2, D2.IsWeakSolution := by
    let E := H (j i)
    let FF := F i
    let : CharZero K1 := charZero_of_injective_algebraMap (algebraMap K K1).injective
    let : CharZero E := charZero_of_injective_algebraMap (algebraMap K1 E).injective
    let : CharP (ResidueField (S i)) p := CharP.of_ringHom_of_ne_zero
      (algebraMap (ResidueField R) (ResidueField (S i))) p (Fact.out : p.Prime).ne_zero
    let : ExpChar (ResidueField (S i)) p := ExpChar.prime (Fact.out : p.Prime)
    have heppRS : EppCondition R (S i) p := EppCondition.of_finite_square hepp
    by_cases hdegreeF : Module.finrank E FF = p
    · let : IsGalois E FF := ⟨⟩
      obtain ⟨fR⟩ := hcycloR
      exact exists_finite_extension_isWeakSolution_of_mixedCyclotomic p
        R (S i) (T i) K1 E FF (hweakRS i) heppRS hdegreeF
        ((algebraMap R (S i)).comp fR)
    · have hle : Module.finrank E FF ≤ p := by
        simpa only [E, FF, hdegree] using hbound i
      have hlt : Module.finrank E FF < p := lt_of_le_of_ne hle hdegreeF
      have hdegreeCoprime : Nat.Coprime p (Module.finrank E FF) :=
        Nat.coprime_of_lt_prime (ne_of_gt Module.finrank_pos) hlt (Fact.out : p.Prime)
      have hd : ramificationIndex (S i) (T i) ∣ Module.finrank E FF := by
        rw [IsFractionRing.finrank_eq (S i) E (T i) FF,
          ramificationIndex_eq_ramificationIdx (S i) (T i)]
        exact ramificationIdx_dvd_finrank_of_isLocalRing (S i) (T i)
      have hram : ramificationIndex R (T i) = ramificationIndex (S i) (T i) := by
        have hramTower := Ideal.ramificationIdx_tower (R := R)
          (IsLocalRing.maximalIdeal (S i)) (IsLocalRing.maximalIdeal (T i))
        rw [← ramificationIndex_eq_ramificationIdx R (T i),
          ← ramificationIndex_eq_ramificationIdx R (S i),
          ← ramificationIndex_eq_ramificationIdx (S i) (T i)] at hramTower
        simpa only [show ramificationIndex R (S i) = 1 from hweakRS i, one_mul]
          using hramTower
      have htame : ringChar (ResidueField R) = 0 ∨
          Nat.Coprime (ringChar (ResidueField R)) (ramificationIndex R (T i)) ∧
            Algebra.IsSeparableExtension (ResidueField R) (ResidueField (T i)) := by
        refine Or.inr ⟨?_, Algebra.isSeparableExtension_of_perfectField _ _⟩
        rw [ringChar.eq (ResidueField R) p]
        rw [hram]
        exact hdegreeCoprime.of_dvd_right hd
      obtain ⟨E2, hE2, hK1E2, hRE2, hRKE2, hfinE2, _hsep, D2, hD2⟩ :=
        exists_finite_extension_isWeakSolution_of_tame_or_charZero R (T i) K1 FF htame
      exact ⟨E2, hE2, hK1E2, hRE2, hRKE2, hfinE2, D2, hD2⟩
  apply exists_finite_extension_isWeakSolution_of_factor_solutions A C K M K1 R F
    (fun i => ↥(T i)) ?_ ?_ ?_ hsol eF'
    (fun i x => reducedTensorFactorsEquiv_left K M K1 D'.L₁ F D'.eL₁ eF
      D'.eL₁_right heF D'.eL₁_left x i)
  · intro a
    rw [← IsScalarTower.algebraMap_apply A K K1, ← IsScalarTower.algebraMap_apply A R K1]
  · intro i c
    rw [← IsScalarTower.algebraMap_apply C M (F i),
      ← IsScalarTower.algebraMap_apply C (T i) (F i)]
  · intro i a
    apply Subtype.ext
    show algebraMap C (F i) (algebraMap A C a) =
      algebraMap K1 (F i) (algebraMap A K1 a)
    rw [← IsScalarTower.algebraMap_apply A C (F i),
      ← IsScalarTower.algebraMap_apply A K1 (F i)]

/-- A mixed-characteristic wild solver, together with the proved Artin--Schreier solver, gives
the characteristic-free wild prime-degree obligation consumed by the tower assembly. -/
theorem wildPrimeDegreeSolvable_of_mixedWildPrimeDegreeSolvable
    (p : ℕ) [Fact p.Prime]
    (hmixed : MixedWildPrimeDegreeSolvable.{u} p) : WildPrimeDegreeSolvable.{u} p := by
  intro A B C K L M
  intros
  rename_i hweak _ hgal hepp hdegree
  rcases charZero_or_charP_of_injective (algebraMap A K)
      (IsFractionRing.injective A K) (residue A) p with hzero | hpchar
  · let := hzero
    exact hmixed A B C K L M hweak hepp hdegree
  · let := hpchar
    exact exists_finite_extension_isWeakSolution_of_wild_charP
      p (Fact.out : p.Prime) A B C K L M hweak hepp hdegree

/-- The entire finite normal-family recursion follows from the mixed-characteristic wild
prime-degree solver.  All other branches in this implication are already proved: equal
characteristic above, tame and purely inseparable prime layers in
`primeDegreeSolvable_of_wildPrimeDegreeSolvable`, finite-family synchronization in
`familyPrimeDegreeSolvable_of_primeDegreeSolvable`, and composite-degree induction in
`familyTowerSolvable_all`. -/
theorem familyTowerSolvable_all_of_mixedWildPrimeDegreeSolvable
    (p : ℕ) [Fact p.Prime]
    (hmixed : MixedWildPrimeDegreeSolvable.{u} p) :
    ∀ n, FamilyTowerSolvable.{u} p n :=
  familyTowerSolvable_all p
    (familyPrimeDegreeSolvable_of_primeDegreeSolvable p
      (primeDegreeSolvable_of_wildPrimeDegreeSolvable p
        (wildPrimeDegreeSolvable_of_mixedWildPrimeDegreeSolvable p hmixed)))

/-- The complete finite-family layer recursion, with the mixed prime-degree producer discharged. -/
theorem familyTowerSolvable_all_proved (p : ℕ) [Fact p.Prime] :
    ∀ n, FamilyTowerSolvable.{u} p n :=
  familyTowerSolvable_all_of_mixedWildPrimeDegreeSolvable p
    (mixedWildPrimeDegreeSolvable p)

/-- Epp's complete perfect-residue tower theorem with the finite-family recursion discharged. -/
theorem exists_finite_extension_isWeakSolution_of_perfectField_proved
    (p : ℕ) [Fact p.Prime]
    (A B C K L M : Type u)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra B M] [Algebra A M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsExtension A B] [IsExtension B C] [IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    [CharP (ResidueField A) p] [ExpChar (ResidueField B) p]
    [PerfectField (ResidueField A)]
    [IsAdicComplete (maximalIdeal A) A]
    [IsAdicComplete (maximalIdeal B) B]
    (hweak : IsWeaklyUnramified A B)
    [Module.Finite L M]
    (hepp : EppCondition A B p) :
    ∃ (K1 : Type u) (_ : Field K1) (_ : Algebra K K1) (_ : Algebra A K1)
      (_ : IsScalarTower A K K1) (_ : Module.Finite K K1),
      ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A C K M K1,
        D.IsWeakSolution :=
  exists_finite_extension_isWeakSolution_of_perfectField p A B C K L M hweak hepp
    (familyTowerSolvable_all_proved p)

end Stacks.EppTheorem

end
