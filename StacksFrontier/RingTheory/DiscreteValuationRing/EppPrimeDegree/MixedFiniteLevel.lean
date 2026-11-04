module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppConstantNumeratorFamily
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedResidueAbsorption
public import StacksFrontier.RingTheory.DiscreteValuationRing.RamificationTower
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppPrimeDegree.FiniteSupportAbsorption
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppPrimeDegree.ReducedFactorPackages

open Stacks.DegreePExtensionLevel
open Stacks.DiscreteValuationRing.EppLevelInduction

/-!
# Prime-degree input: the mixed-characteristic finite-level induction

The level-bounded recursive obligation in mixed characteristic and its induction on the level
and the least numerator, giving the finite-level solver.
-/

@[expose] public section

open IsLocalRing
open IsDiscreteValuationRing
open scoped TensorProduct

namespace Stacks.EppTheorem

universe u v w uΩ

/-- The mixed-characteristic recursive obligation up to a prescribed level bound.  Quantifying
over every presentation whose actual level is at most `t` is what permits an inner induction on
the least numerator: a reduced factor may acquire a smaller numerator without immediately
crossing the outer level-drop bound. -/
private abbrev MixedFiniteLevelUpToSolvable (p : ℕ) [Fact p.Prime] (t : ℚ) : Prop :=
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
    [IsDiscreteValuationRing.IsExtension A B]
    [IsDiscreteValuationRing.IsExtension B C]
    [IsDiscreteValuationRing.IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    [CharZero K] [CharP (ResidueField A) p] [ExpChar (ResidueField B) p]
    [PerfectField (ResidueField A)]
    [IsAdicComplete (maximalIdeal A) A]
    [IsAdicComplete (maximalIdeal B) B]
    (hweak : IsDiscreteValuationRing.IsWeaklyUnramified A B)
    (hepp : EppCondition A B p)
    [Module.Finite L M]
    (f : CyclotomicRing p ℤ ℚ →+* B) (P : Polynomial B)
    (hP : intProp f P ∧ quotChar f P ∧ shapeProp f P ∧ funcEq f P)
    (hfinite : Stacks.DegreePExtensionLevel.IsDegreePExtensionOfFiniteLevel B L M p f P)
    (pi : B) (e : ℕ) (he : 0 < e)
    (hne : (Stacks.DegreePExtensionLevel.extensionLevelNumerators B L M P pi).Nonempty)
    (hpi : Irreducible pi) (hw : Associated (wElt f) (pi ^ e))
    (hle : Stacks.DegreePExtensionLevel.extensionLevel B L M P pi e he hne ≤ t),
    ∃ (K2 : Type u) (_ : Field K2) (_ : Algebra K K2) (_ : Algebra A K2)
      (_ : IsScalarTower A K K2) (_ : Module.Finite K K2),
      ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A C K M K2,
        D.IsWeakSolution

/-- The inner induction obligation for the mixed recursion.  The outer level is only bounded by
`t`; the exact least numerator is fixed to `n`.  Reduced factors can keep a level too large for
the outer induction while strictly decreasing this natural-number measure. -/
private abbrev MixedFiniteNumeratorUpToSolvable
    (p : ℕ) [Fact p.Prime] (t : ℚ) (n : ℕ) : Prop :=
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
    [IsDiscreteValuationRing.IsExtension A B]
    [IsDiscreteValuationRing.IsExtension B C]
    [IsDiscreteValuationRing.IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    [CharZero K] [CharP (ResidueField A) p] [ExpChar (ResidueField B) p]
    [PerfectField (ResidueField A)]
    [IsAdicComplete (maximalIdeal A) A]
    [IsAdicComplete (maximalIdeal B) B]
    (hweak : IsDiscreteValuationRing.IsWeaklyUnramified A B)
    (hepp : EppCondition A B p)
    [Module.Finite L M]
    (f : CyclotomicRing p ℤ ℚ →+* B) (P : Polynomial B)
    (hP : intProp f P ∧ quotChar f P ∧ shapeProp f P ∧ funcEq f P)
    (hfinite : Stacks.DegreePExtensionLevel.IsDegreePExtensionOfFiniteLevel B L M p f P)
    (pi : B) (e : ℕ) (he : 0 < e)
    (hne : (Stacks.DegreePExtensionLevel.extensionLevelNumerators B L M P pi).Nonempty)
    (hpi : Irreducible pi) (hw : Associated (wElt f) (pi ^ e))
    (hsinf : sInf (Stacks.DegreePExtensionLevel.extensionLevelNumerators B L M P pi) = n)
    (hle : Stacks.DegreePExtensionLevel.extensionLevel B L M P pi e he hne ≤ t),
    ∃ (K2 : Type u) (_ : Field K2) (_ : Algebra K K2) (_ : Algebra A K2)
      (_ : IsScalarTower A K K2) (_ : Module.Finite K K2),
      ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A C K M K2,
        D.IsWeakSolution

private lemma mixedLevelBound_mono (p x y : ℚ) (hxy : x ≤ y) :
    max 0 (max (x - 1) (2 * x - p)) ≤
      max 0 (max (y - 1) (2 * y - p)) := by
  gcongr

/-- The residue field of a DVR extension of `A` has characteristic `p` if that of `A` does. -/
private theorem charP_residueField_of_isExtension
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B]
    [IsDiscreteValuationRing.IsExtension A B] (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField A) p] : CharP (ResidueField B) p :=
  CharP.of_ringHom_of_ne_zero
    (algebraMap (ResidueField A) (ResidueField B)) p (Fact.out : p.Prime).ne_zero

/-- Level zero is already weakly unramified, hence the identity field extension solves the
tower.  This is the base case of the mixed all-conjugates recursion. -/
private theorem mixedFiniteLevelUpToSolvable_zero
    (p : ℕ) [Fact p.Prime] : MixedFiniteLevelUpToSolvable.{u} p 0 := by
  intro A B C K L M
  intros
  rename_i hweak _hepp hfin f P hP hfinite pi e he hne hpi hw hle
  have hzero : Stacks.DegreePExtensionLevel.extensionLevel B L M P pi e he hne = 0 := by
    apply le_antisymm hle
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  let : CharP (ResidueField B) p := charP_residueField_of_isExtension A B p
  let : IsIntegralClosure C B M :=
    isIntegralClosure_of_isAdicComplete B C L M
  have hBC : IsDiscreteValuationRing.IsWeaklyUnramified B C :=
    IsDiscreteValuationRing.isWeaklyUnramified_of_extensionLevel_eq_zero
      B C L M p f P hP pi hpi e he hne hzero
  have hAC : IsDiscreteValuationRing.IsWeaklyUnramified A C :=
    isWeaklyUnramified_trans A B C hweak hBC
  refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance,
    Module.Finite.self K, canonicalBaseChange A C K M K, ?_⟩
  exact isWeakSolution_of_isWeaklyUnramified_of_perfect_residueField A C K M K _ hAC

/-- A successful mixed level step is closed under the outer recursion hypothesis.  Direct weak
solutions are returned immediately; a field-valued totally ramified tensor step is solved at its
smaller level and then composed back to the original tower. -/
private theorem exists_finite_extension_isWeakSolution_of_mixedLevelStepOutcome
    (p : ℕ) [Fact p.Prime] (bound : ℚ)
    (ih : MixedFiniteLevelUpToSolvable.{u} p bound)
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
    [IsDiscreteValuationRing.IsExtension A B]
    [IsDiscreteValuationRing.IsExtension B C]
    [IsDiscreteValuationRing.IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    [CharZero K] [CharP (ResidueField A) p] [ExpChar (ResidueField B) p]
    [PerfectField (ResidueField A)]
    [IsAdicComplete (maximalIdeal A) A]
    [IsAdicComplete (maximalIdeal B) B]
    (hweak : IsDiscreteValuationRing.IsWeaklyUnramified A B)
    (hepp : EppCondition A B p)
    [Module.Finite L M]
    (f : CyclotomicRing p ℤ ℚ →+* B) (P : Polynomial B) (l : ℚ)
    (hP : intProp f P ∧ quotChar f P ∧ shapeProp f P ∧ funcEq f P)
    (hbound : max 0 (max (l - 1) (2 * l - (p : ℚ))) ≤ bound)
    (hout : Stacks.DiscreteValuationRing.EppLevelInduction.MixedLevelStepOutcome A B C K L M p f P
      l) :
    ∃ (K2 : Type u) (_ : Field K2) (_ : Algebra K K2) (_ : Algebra A K2)
      (_ : IsScalarTower A K K2) (_ : Module.Finite K K2),
      ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A C K M K2,
        D.IsWeakSolution := by
  rcases hout with ⟨K1, hK1, hKK1, hAK1, hAKK1, hfinK1, hsepK1, htot, hnext⟩
  let := hK1
  let := hKK1
  let := hAK1
  let := hAKK1
  let := hfinK1
  let := hsepK1
  rcases hnext with hsol | hnext
  · obtain ⟨D, hD⟩ := hsol
    exact ⟨K1, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, D, hD⟩
  · obtain ⟨hL1, hM1, hB1, hfrac, hfin, hfinite1,
      pi1, e1, he1, hne1, hpi1, hw1, hle1⟩ := hnext
    apply exists_finite_extension_isWeakSolution_of_totallyRamified_tensorProduct_of_perfectResidue
      A B C K L M K1 p hweak htot hL1 hM1 hfin
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
    obtain ⟨_, hBB1, hBfin, _, _⟩ :=
      integralClosure_isCompleteDVR B L (L ⊗[K] K1)
    let : Module.Finite A (integralClosure A K1) := hAfin
    let : Module.Finite B (integralClosure B (L ⊗[K] K1)) := hBfin
    let : IsDiscreteValuationRing.IsExtension A (integralClosure A K1) := hAA1
    let : IsDiscreteValuationRing.IsExtension B
        (integralClosure B (L ⊗[K] K1)) := hBB1
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
        rw [IsScalarTower.algebraMap_apply A K L,
          IsScalarTower.algebraMap_apply A K K1]
        exact Algebra.TensorProduct.tmul_one_eq_one_tmul _
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
    exact ih (integralClosure A K1) (integralClosure B (L ⊗[K] K1))
      (integralClosure C (M ⊗[K] K1)) K1 (L ⊗[K] K1) (M ⊗[K] K1)
      hweak1 hepp1
      ((algebraMap B (integralClosure B (L ⊗[K] K1))).comp f)
      (P.map (algebraMap B (integralClosure B (L ⊗[K] K1))))
      (Stacks.DiscreteValuationRing.EppLevelInduction.cyclotomic_properties_map f P hP
        (algebraMap B (integralClosure B (L ⊗[K] K1))) )
      hfinite1 pi1 e1 he1 hne1 hpi1 hw1 (hle1.trans hbound)

/-- The inner least-numerator recursion for a fixed outer level bound.  A finite-support step is
performed simultaneously in every reduced tensor factor.  A factor either reaches the prescribed
level drop, or its least numerator is strictly smaller and the strong induction hypothesis applies.
-/
private theorem mixedFiniteNumeratorUpToSolvable
    (p : ℕ) [Fact p.Prime] (t : ℚ) (ht : 0 ≤ t) (htp : t < (p : ℚ))
    (outer : MixedFiniteLevelUpToSolvable.{u} p
      (max 0 (max (t - 1) (2 * t - (p : ℚ)))))
    (n : ℕ) : MixedFiniteNumeratorUpToSolvable.{u} p t n := by
  induction n using Nat.strong_induction_on with
  | _ n inner =>
    intro A B C K L M
    intros
    rename_i hweak hepp hfin f P hP hfinite pi e he hne hpi hw hsinf hle
    let l := Stacks.DegreePExtensionLevel.extensionLevel B L M P pi e he hne
    have hl0 : 0 ≤ l := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    by_cases hlz : l = 0
    · exact mixedFiniteLevelUpToSolvable_zero p A B C K L M hweak hepp f P hP
        hfinite pi e he hne hpi hw (by change l ≤ 0; exact le_of_eq hlz)
    have hlpos : 0 < l := lt_of_le_of_ne hl0 (Ne.symm hlz)
    obtain ⟨piA, hpiA⟩ := IsDiscreteValuationRing.exists_irreducible A
    rcases
      exists_totallyRamified_isWeakSolution_or_extensionLevel_le_or_finiteSupport_of_uniformizer
        A B C K L M p hweak piA hpiA f P hP hfinite l
        ⟨pi, e, he, hne, hpi, hw, rfl⟩ hlpos with hout | hsupport
    · exact exists_finite_extension_isWeakSolution_of_mixedLevelStepOutcome
        p (max 0 (max (t - 1) (2 * t - (p : ℚ)))) outer
        A B C K L M hweak hepp f P l hP
        (mixedLevelBound_mono p l t hle) hout
    rcases hsupport with ⟨s, hs, _hmissing, hprep, _hreentry⟩
    rcases hprep with
      ⟨ep, hep, hnep, hpip, hwp, hlevelp, np, mp, xi, z, H, H0, sigma0, r0,
        hnpeq, hnmem, hnleast, hnpos, hnbound, _hmpeq, hmpos, hmle, hme, hnm,
        hpm, hbound, hz, hPz, hHd, hH0d, hH, hr0sigma, hr0q, hseq, hcore, hxi⟩
    let : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
    let : CharP (ResidueField B) p := charP_residueField_of_isExtension A B p
    obtain ⟨_, hgalLM, _⟩ :=
      isGalois_and_ramification_cases_of_adjoin_root_cyclotomic_quotient
        B L M p f P hP xi z
        (by simpa only [Polynomial.aeval_def, IsScalarTower.algebraMap_eq B L M] using hPz)
        hz (algebraMap A B piA) hpip
    let : IsGalois L M := hgalLM
    have hpimap : Irreducible (algebraMap A B piA) :=
      irreducible_algebraMap_of_isWeaklyUnramified hweak hpiA
    have hpiassoc : Associated pi (algebraMap A B piA) :=
      IsDiscreteValuationRing.associated_of_irreducible B hpi hpimap
    have hnumEq :=
      Stacks.DiscreteValuationRing.EppLevelInduction.extensionLevelNumerators_eq_of_associated
      (K := L) (L := M) P hpiassoc
    have hnpn : np = n := by
      rw [hnpeq, ← hsinf, hnumEq]
    obtain ⟨R, hRcomm, hRdom, hRdvr, hAR, hRfin, hARext, hRcomplete, hRperfect,
        K1, hK1field, hRK1, hRfrac, hKK1, hAK1, hAKK1, hARK1, hK1fin,
        hweakAR, _hgalResidue, habs⟩ :=
      EppCondition.exists_fractionField_isWeaklyUnramified_forall_exists_pow_eq_of_residueOverfield
        (R := A) (K := K) (fun _ : ULift.{u} Unit => B) (fun _ => hepp)
        (fun _ => s) (fun _ => hs) 0
    let := hRcomm
    let := hRdom
    let := hRdvr
    let := hAR
    let := hRfin
    let := hARext
    let := hRcomplete
    let := hRperfect
    let := hK1field
    let := hRK1
    let := hRfrac
    let := hKK1
    let := hAK1
    let := hAKK1
    let := hARK1
    let := hK1fin
    let : CharZero K1 := charZero_of_injective_algebraMap (algebraMap K K1).injective
    let : CharP (ResidueField R) p := charP_residueField_of_isExtension A R p
    let : HenselianLocalRing B := henselianLocalRing_of_isAdicComplete_maximalIdeal B
    let : IsAdicComplete (maximalIdeal C) C := by
      let : IsIntegralClosure C B M := isIntegralClosure_of_isAdicComplete B C L M
      let : Module.Finite B (integralClosure B M) :=
        (isDiscreteValuationRing_and_finite_integralClosure_of_isAdicComplete B L M).2
      let : Module.Finite B C := Module.Finite.equiv
        (IsIntegralClosure.equiv B (integralClosure B M) M C).toLinearEquiv
      exact isAdicComplete_of_finite B C
    let : HenselianLocalRing C := henselianLocalRing_of_isAdicComplete_maximalIdeal C
    apply exists_finite_extension_isWeakSolution_of_forall_individualFactorSolutions
      A C K M K1 R
    · intro a
      rw [← IsScalarTower.algebraMap_apply A K K1,
        ← IsScalarTower.algebraMap_apply A R K1]
    · intro mf F hFfield hKF hMF hK1F hKMF hKK1F hMfin decomp hleft hright
      let := hFfield
      let := hKF
      let := hMF
      let := hK1F
      let := hKMF
      let := hKK1F
      let := hMfin
      let : ∀ i, Algebra C (F i) := fun i =>
        ((algebraMap M (F i)).comp (algebraMap C M)).toAlgebra
      let : ∀ i, Algebra B (F i) := fun i =>
        ((algebraMap M (F i)).comp (algebraMap B M)).toAlgebra
      let : ∀ i, Algebra A (F i) := fun i =>
        ((algebraMap C (F i)).comp (algebraMap A C)).toAlgebra
      let : ∀ i, IsScalarTower C M (F i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
      let : ∀ i, IsScalarTower B M (F i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
      let : ∀ i, IsScalarTower A C (F i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
      let : ∀ i, Algebra L (F i) := fun i =>
        ((algebraMap M (F i)).comp (algebraMap L M)).toAlgebra
      let : ∀ i, IsScalarTower L M (F i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
      let : ∀ i, IsScalarTower B L (F i) := fun i =>
        IsScalarTower.of_algebraMap_eq fun x => by
          rw [IsScalarTower.algebraMap_apply B M (F i),
            IsScalarTower.algebraMap_apply B L M]
          rfl
      let : ∀ i, IsScalarTower B C (F i) := fun i =>
        IsScalarTower.of_algebraMap_eq fun x => by
          rw [IsScalarTower.algebraMap_apply B M (F i),
            IsScalarTower.algebraMap_apply B C M,
            ← IsScalarTower.algebraMap_apply C M (F i)]
      let : ∀ i, IsScalarTower K L (F i) := fun i =>
        IsScalarTower.of_algebraMap_eq fun x => by
          rw [IsScalarTower.algebraMap_apply K M (F i),
            IsScalarTower.algebraMap_apply K L M]
          rfl
      obtain ⟨D⟩ := nonempty_integralClosureBaseChange A B K L K1
      let := D.commRingL₁
      let := D.algebraKL₁
      let := D.algebraLL₁
      let := D.algebraK₁L₁
      obtain ⟨nf, FH, hFHfield, hLFH, hK1FH, hBFH, hAFH, hBLFH, hABFH, hAK1FH,
          hLFHfin, hnf, eFH, heFH⟩ := exists_finiteFieldFactors_of_package A B K L K1 D
      let := hFHfield
      let := hLFH
      let := hK1FH
      let := hBFH
      let := hAFH
      let := hBLFH
      let := hABFH
      let := hAK1FH
      let := hLFHfin
      let : ∀ j, Algebra K (FH j) := fun j =>
        ((algebraMap K1 (FH j)).comp (algebraMap K K1)).toAlgebra
      let : ∀ j, IsScalarTower K K1 (FH j) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
      let : Algebra K1 (L ⊗[K] K1) := Algebra.TensorProduct.rightAlgebra
      let : Algebra K1 (ReducedTensorTower.Reduction (L ⊗[K] K1)) :=
        Ideal.Quotient.algebra K1
      let eFH' := reducedTensorFactorsEquiv K L K1 D.L₁ FH D.eL₁ eFH D.eL₁_right heFH
      have heFHleft (j : Fin nf) (x : L) :
          eFH' (Ideal.Quotient.mk _
            ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K1) x)) j =
              algebraMap L (FH j) x :=
        reducedTensorFactorsEquiv_left K L K1 D.L₁ FH D.eL₁ eFH
          D.eL₁_right heFH D.eL₁_left x j
      have heFHright (j : Fin nf) (x : K1) :
          eFH' (Ideal.Quotient.mk _
            ((Algebra.TensorProduct.includeRight : K1 →ₐ[K] L ⊗[K] K1) x)) j =
              algebraMap K1 (FH j) x := by
        show eFH' (algebraMap K1 (ReducedTensorTower.Reduction (L ⊗[K] K1)) x) j = _
        rw [eFH'.commutes]
        rfl
      let : ∀ j, IsScalarTower K L (FH j) := fun j =>
        IsScalarTower.of_algebraMap_eq fun x => by
          have htk : (algebraMap K L x) ⊗ₜ[K] (1 : K1) =
              (1 : L) ⊗ₜ[K] algebraMap K K1 x := Algebra.TensorProduct.tmul_one_eq_one_tmul _
          have hx := congrArg (fun q => eFH' (Ideal.Quotient.mk _ q) j) htk
          change eFH' (Ideal.Quotient.mk _
              ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K1)
                (algebraMap K L x))) j =
            eFH' (Ideal.Quotient.mk _
              ((Algebra.TensorProduct.includeRight : K1 →ₐ[K] L ⊗[K] K1)
                (algebraMap K K1 x))) j at hx
          rw [heFHleft, heFHright] at hx
          exact hx.symm
      let : Algebra K1 (M ⊗[K] K1) := Algebra.TensorProduct.rightAlgebra
      let phi (i : Fin mf) : (M ⊗[K] K1) →ₐ[K1] F i :=
        { __ := ((Pi.evalAlgHom K F i).comp decomp.toAlgHom).toRingHom.comp
            (Ideal.Quotient.mk _)
          commutes' x := hright i x }
      have hphi (i : Fin mf) (x : M) (y : K1) :
          phi i (x ⊗ₜ[K] y) = algebraMap M (F i) x * algebraMap K1 (F i) y := by
        rw [show x ⊗ₜ[K] y = (x ⊗ₜ[K] (1 : K1)) * ((1 : M) ⊗ₜ[K] y) by
          simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul], map_mul]
        show decomp (Ideal.Quotient.mk _
          ((Algebra.TensorProduct.includeLeft : M →ₐ[K] M ⊗[K] K1) x)) i *
            decomp (Ideal.Quotient.mk _
              ((Algebra.TensorProduct.includeRight : K1 →ₐ[K] M ⊗[K] K1) y)) i = _
        rw [hleft, hright]
      have hphisurj (i : Fin mf) : Function.Surjective (phi i) := by
        have hev : Function.Surjective (Pi.evalAlgHom K F i) := fun x =>
          ⟨Pi.single i x, by simp⟩
        exact hev.comp (decomp.surjective.comp Ideal.Quotient.mk_surjective)
      have hfac (i : Fin mf) :=
        exists_fieldFactor_normal_and_finrank_le K L M K1 (F i) FH eFH' heFHleft
          (phi i) (hphi i) (hphisurj i)
      choose j g hLHF hfinHF hnormalHF hboundHF using hfac
      let : ∀ i, Algebra (FH (j i)) (F i) := fun i => (g i).toRingHom.toAlgebra
      let : ∀ i, IsScalarTower L (FH (j i)) (F i) := hLHF
      let : ∀ i, IsScalarTower K1 (FH (j i)) (F i) := fun i => IsScalarTower.of_algHom (g i)
      let := hfinHF
      let : ∀ j, Algebra B (FH j) := fun j =>
        ((algebraMap L (FH j)).comp (algebraMap B L)).toAlgebra
      let : ∀ j, IsScalarTower B L (FH j) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
      let : ∀ j, Algebra A (FH j) := fun j =>
        ((algebraMap B (FH j)).comp (algebraMap A B)).toAlgebra
      let : ∀ j, IsScalarTower A B (FH j) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
      let : ∀ i, Algebra R (F i) := fun i =>
        ((algebraMap K1 (F i)).comp (algebraMap R K1)).toAlgebra
      let : ∀ i, IsScalarTower R K1 (F i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
      let : ∀ i, IsScalarTower A R (F i) := fun i =>
        IsScalarTower.of_algebraMap_eq fun a =>
          (algebraMap_reducedFactor_base_eq_of_tower A C K M K1 F
            decomp hleft hright i a).trans
            (congrArg (algebraMap K1 (F i)) (IsScalarTower.algebraMap_apply A R K1 a))
      let : ∀ i, IsScalarTower B (FH (j i)) (F i) := fun i =>
        IsScalarTower.of_algebraMap_eq fun x => by
          rw [IsScalarTower.algebraMap_apply B L (F i),
            IsScalarTower.algebraMap_apply L (FH (j i)) (F i),
            ← IsScalarTower.algebraMap_apply B L (FH (j i))]
      have hweakLower :=
        isWeaklyUnramified_integralClosure_factor_of_perfectResidue
          A B K L K1 R hweak FH (eFH'.restrictScalars K) heFHleft heFHright
      intro i
      let E := FH (j i)
      let FF := F i
      let T := integralClosure C FF
      let : Algebra R E := ((algebraMap K1 E).comp (algebraMap R K1)).toAlgebra
      let : IsScalarTower R K1 E := IsScalarTower.of_algebraMap_eq' rfl
      let : IsScalarTower A K1 E := IsScalarTower.of_algebraMap_eq fun a => by
        show algebraMap B E (algebraMap A B a) = algebraMap K1 E (algebraMap A K1 a)
        exact algebraMap_reducedFactor_base_eq_of_tower A B K L K1 FH
          (eFH'.restrictScalars K) heFHleft heFHright (j i) a
      let : FaithfulSMul R E := (faithfulSMul_iff_algebraMap_injective R E).mpr
        ((algebraMap K1 E).injective.comp (IsFractionRing.injective R K1))
      let : IsScalarTower A R E := IsScalarTower.of_algebraMap_eq fun a => by
        rw [IsScalarTower.algebraMap_apply A K1 E, IsScalarTower.algebraMap_apply A R K1]
        rfl
      let S := integralClosure B E
      let : IsDiscreteValuationRing S := isDiscreteValuationRing_integralClosure_factor B L E
      let : Algebra R S := algebraIntegralClosureBase A B R E
      let : IsFractionRing S E := isFractionRing_integralClosure_factor B L E
      let : IsScalarTower R S E := isScalarTower_base_integralClosure_factor A B R E
      let : IsDiscreteValuationRing.IsExtension R S :=
        isExtension_base_integralClosure_factor A B R L E
      let : IsScalarTower A B S := IsScalarTower.of_algebraMap_eq fun a =>
        Subtype.ext (IsScalarTower.algebraMap_apply A B E a)
      let : IsScalarTower A R S := IsScalarTower.of_algebraMap_eq fun a => by
        apply Subtype.ext
        show algebraMap B E (algebraMap A B a) =
          algebraMap K1 E (algebraMap R K1 (algebraMap A R a))
        rw [← IsScalarTower.algebraMap_apply A B E,
          ← IsScalarTower.algebraMap_apply A R K1,
          ← IsScalarTower.algebraMap_apply A K1 E]
      obtain ⟨_, hBSext, hBSfin, hScomplete, _⟩ := integralClosure_isCompleteDVR B L E
      let : IsDiscreteValuationRing.IsExtension B S := hBSext
      let : Module.Finite B S := hBSfin
      let : IsAdicComplete (maximalIdeal S) S := hScomplete
      let : IsDiscreteValuationRing T := isDiscreteValuationRing_integralClosure_factor C M FF
      let : FaithfulSMul R FF := (faithfulSMul_iff_algebraMap_injective R FF).mpr
        ((algebraMap K1 FF).injective.comp (IsFractionRing.injective R K1))
      let : Algebra R T := algebraIntegralClosureBase A C R FF
      let : IsFractionRing T FF := isFractionRing_integralClosure_factor C M FF
      let : IsScalarTower R T FF := isScalarTower_base_integralClosure_factor A C R FF
      let : IsDiscreteValuationRing.IsExtension R T :=
        isExtension_base_integralClosure_factor A C R M FF
      let algSFF : Algebra S FF := ((algebraMap E FF).comp (algebraMap S E)).toAlgebra
      let hSEFFTower : IsScalarTower S E FF := IsScalarTower.of_algebraMap_eq' rfl
      let towerSEFFExact : @IsScalarTower S E FF
          (inferInstance : Algebra S E).toSMul
          (inferInstance : Algebra E FF).toSMul algSFF.toSMul := hSEFFTower
      let : IsScalarTower B E FF := IsScalarTower.of_algebraMap_eq fun x => by
        rw [IsScalarTower.algebraMap_apply B L (F i),
          IsScalarTower.algebraMap_apply B L E,
          IsScalarTower.algebraMap_apply L E FF]
      let : IsScalarTower R E FF := IsScalarTower.of_algebraMap_eq fun r => by
        rw [IsScalarTower.algebraMap_apply R K1 FF,
          IsScalarTower.algebraMap_apply R K1 E,
          IsScalarTower.algebraMap_apply K1 E FF]
      have hRSFF (r : R) : algebraMap R FF r = algebraMap S FF (algebraMap R S r) := by
        show algebraMap K1 FF (algebraMap R K1 r) =
          algebraMap E FF (algebraMap S E (algebraMap R S r))
        rw [IsScalarTower.algebraMap_apply K1 E FF,
          ← IsScalarTower.algebraMap_apply R K1 E,
          IsScalarTower.algebraMap_apply R S E]
      let : IsScalarTower R S FF := IsScalarTower.of_algebraMap_eq hRSFF
      let algST : Algebra S T := (mapIntegralClosureOfTower B C E FF).toRingHom.toAlgebra
      let : Algebra S T := algST
      let hSTFFTower : IsScalarTower S T FF := IsScalarTower.of_algebraMap_eq fun x => by
        show algebraMap E FF x.1 = algebraMap E FF x.1
        rfl
      let towerSTFFExact : @IsScalarTower S T FF algST.toSMul
          (inferInstance : Algebra T FF).toSMul algSFF.toSMul := hSTFFTower
      have hSTFF (x : S) : algebraMap S FF x = algebraMap T FF (algebraMap S T x) := by
        show algebraMap E FF x.1 = algebraMap E FF x.1
        rfl
      have hRTFF (r : R) : algebraMap R FF r = algebraMap T FF (algebraMap R T r) :=
        IsScalarTower.algebraMap_apply R T FF r
      let : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun r => by
        apply IsFractionRing.injective T FF
        exact (hRTFF r).symm.trans ((hRSFF r).trans (hSTFF (algebraMap R S r)))
      let : IsDiscreteValuationRing.IsExtension S T :=
        (integralClosure_factor_isExtension B C L M E FF).choose_spec.choose_spec.1
      obtain ⟨_, _, _, hTcomplete, _⟩ := integralClosure_isCompleteDVR C M FF
      let : IsAdicComplete (maximalIdeal T) T := hTcomplete
      let : IsLocalHom (algebraMap B S) := inferInstance
      let : IsLocalHom (algebraMap A S) := by
        rw [IsScalarTower.algebraMap_eq A B S]
        infer_instance
      let : IsLocalHom (algebraMap R S) := isLocalHom_algebraMap_of_tower A R S
      let : FaithfulSMul A S := (faithfulSMul_iff_algebraMap_injective A S).mpr (by
        rw [IsScalarTower.algebraMap_eq A R S]
        exact (FaithfulSMul.algebraMap_injective R S).comp
          (FaithfulSMul.algebraMap_injective A R))
      let : IsDiscreteValuationRing.IsExtension A S := ⟨⟩
      have hweakRS : IsDiscreteValuationRing.IsWeaklyUnramified R S := by
        simpa only [S, E] using hweakLower (j i)
      let : CharP (ResidueField S) p := charP_of_injective_algebraMap
        (algebraMap (ResidueField R) (ResidueField S)).injective p
      have hweakAS : IsDiscreteValuationRing.IsWeaklyUnramified A S :=
        isWeaklyUnramified_trans A R S hweakAR hweakRS
      have hweakBS : IsDiscreteValuationRing.IsWeaklyUnramified B S :=
        (Stacks.DiscreteValuationRing.Ramification.isWeaklyUnramified_of_isWeaklyUnramified A B S
          hweakAS).2
      have heppRS : EppCondition R S p := EppCondition.of_finite_square hepp
      have hBmap (b0 : B) : algebraMap L E (algebraMap B L b0) =
          algebraMap S E (algebraMap B S b0) := by
        rw [← IsScalarTower.algebraMap_apply B L E,
          ← IsScalarTower.algebraMap_apply B S E]
      have hfactor := cyclotomicFiniteLevelFactorPackage_of_matching_reducedFactors
        K B S L M K1 E FF p (Fact.out : p.Prime) f P hP hfinite hBmap
        (phi i).toRingHom (hphi i) (hphisurj i)
      dsimp only at hfactor
      rcases hfactor with ⟨hfinEF, hdegreeEF⟩
      let := hfinEF
      rcases hdegreeEF with ⟨hdegreeOne, hsurjEF⟩ | ⟨hdegreeP, hgalEF, hfiniteSF⟩
      · refine ⟨K1, inferInstance, inferInstance, inferInstance,
          inferInstance, Module.Finite.self K1, ?_⟩
        let hweakRT := isWeaklyUnramified_of_finrank_eq_one
          R S T K1 E FF hweakRS hdegreeOne
        exact ⟨canonicalBaseChange R T K1 FF K1,
          isWeakSolution_of_isWeaklyUnramified_of_perfect_residueField
            R T K1 FF K1 _ hweakRT⟩
      · let : IsGalois E FF := hgalEF
        let fS := (algebraMap B S).comp f
        let PS := P.map (algebraMap B S)
        have hPS : intProp fS PS ∧ quotChar fS PS ∧ shapeProp fS PS ∧ funcEq fS PS :=
          Stacks.DiscreteValuationRing.EppLevelInduction.cyclotomic_properties_map f P hP
            (algebraMap B S)
        let q : (E ⊗[L] M) →ₐ[E] FF :=
          Algebra.TensorProduct.lift (Algebra.ofId E FF)
            (IsScalarTower.toAlgHom L M FF) (fun _ _ => .all _ _)
        have hq_tmul (a : E) (b : M) :
            q (a ⊗ₜ[L] b) = algebraMap E FF a * algebraMap M FF b := by
          simp [q]
        have hqsurj : Function.Surjective q := by
          intro x
          obtain ⟨v, rfl⟩ := hphisurj i x
          induction v using TensorProduct.induction_on with
          | zero => exact ⟨0, by rw [map_zero q, map_zero (phi i)]⟩
          | tmul m0 k0 =>
              refine ⟨algebraMap K1 E k0 ⊗ₜ[L] m0, ?_⟩
              rw [hq_tmul, ← IsScalarTower.algebraMap_apply K1 E FF, mul_comm,
                ← hphi i]
          | add x0 y0 hx0 hy0 =>
              obtain ⟨x1, hx1⟩ := hx0
              obtain ⟨y1, hy1⟩ := hy0
              exact ⟨x1 + y1, by rw [map_add, hx1, hy1, map_add]⟩
        let zF : FF := q (1 ⊗ₜ[L] z)
        have hzFdef : zF = algebraMap M FF z := by simp [zF, q]
        have hzF : Algebra.adjoin E {zF} = ⊤ :=
          adjoin_eq_top_of_surjective_tensorProduct_factor L E M FF z hz q hqsurj
        have hcoeff :
            ((algebraMap E FF).comp (algebraMap S E)).comp (algebraMap B S) =
              ((algebraMap M FF).comp (algebraMap L M)).comp (algebraMap B L) := by
          ext b0
          show algebraMap E FF (algebraMap S E (algebraMap B S b0)) =
            algebraMap M FF (algebraMap L M (algebraMap B L b0))
          rw [← hBmap]
          exact (IsScalarTower.algebraMap_apply L E FF (algebraMap B L b0)).symm.trans
            (IsScalarTower.algebraMap_apply L M FF (algebraMap B L b0))
        have hPzF : Polynomial.aeval zF PS =
            algebraMap E FF (algebraMap L E xi) := by
          rw [Polynomial.aeval_def, Polynomial.eval₂_map]
          show Polynomial.eval₂
            (((algebraMap E FF).comp (algebraMap S E)).comp (algebraMap B S)) zF P = _
          rw [hcoeff, hzFdef]
          have hz' := congrArg (algebraMap M FF) hPz
          rw [Polynomial.aeval_def, IsScalarTower.algebraMap_eq B L M,
            Polynomial.hom_eval₂] at hz'
          exact hz'.trans ((IsScalarTower.algebraMap_apply L M FF xi).symm.trans
            (IsScalarTower.algebraMap_apply L E FF xi))
        have hresMap : algebraMap (ResidueField B) (ResidueField S) =
            IsLocalRing.ResidueField.map (algebraMap B S) := by
          refine RingHom.ext fun y => ?_
          obtain ⟨b0, rfl⟩ := IsLocalRing.residue_surjective y
          rw [IsLocalRing.ResidueField.algebraMap_residue]
          exact (RingHom.congr_fun
            (IsLocalRing.ResidueField.map_comp_residue (algebraMap B S)) b0).symm
        have habsS : ∀ x ∈ @Finset.image ℕ (ResidueField B) (Classical.decEq _)
            (fun k => H0.coeff k) H0.support,
            IsLocalRing.ResidueField.map (algebraMap B S) x ∈
              (algebraMap (ResidueField R) (ResidueField S)).fieldRange := by
          intro x hx
          obtain ⟨r, hr⟩ := habs (ULift.up ()) (ResidueField S) x (by
            rw [hseq]
            exact hx)
          refine ⟨r, ?_⟩
          simpa only [pow_zero, pow_one, ← hresMap] using hr
        have hxiS :=
          Stacks.DiscreteValuationRing.EppLevelInduction.exists_mapped_scaled_parameter_relation
          (algebraMap B S) (algebraMap L E) (by
            ext b0
            exact hBmap b0)
          (algebraMap A B piA) mp np H xi hxi
        have hpiR : Irreducible (algebraMap A R piA) :=
          irreducible_algebraMap_of_isWeaklyUnramified hweakAR hpiA
        have hpiSquare : algebraMap B S (algebraMap A B piA) =
            algebraMap R S (algebraMap A R piA) := by
          rw [← IsScalarTower.algebraMap_apply A B S,
            ← IsScalarTower.algebraMap_apply A R S]
        have hwS : Associated (wElt fS) ((algebraMap B S (algebraMap A B piA)) ^ ep) := by
          have hmapped := hwp.map (algebraMap B S)
          simpa only [fS, wElt, zetaA, RingHom.comp_apply, map_sub, map_one, map_pow]
            using hmapped
        have hstepF :=
          mixedLevelStepOutcome_or_numerator_lt_of_mapped_preparation
          R B S T K1 E FF p hweakBS hweakRS (algebraMap A R piA) hpiR
          (algebraMap A B piA) hpiSquare fS PS hPS hfiniteSF l ep hep np mp
          hnpos hnbound hmpos hmle hme hnm hpm hbound hwS
          (algebraMap L E xi) zF hzF hPzF H H0 sigma0 r0 hr0sigma hr0q hH hHd
          hcore habsS hxiS
        rcases hstepF with houtF | ⟨hneF, hsmaller⟩
        · exact exists_finite_extension_isWeakSolution_of_mixedLevelStepOutcome
            p (max 0 (max (t - 1) (2 * t - (p : ℚ)))) outer
            R S T K1 E FF hweakRS heppRS fS PS l hPS
            (mixedLevelBound_mono p l t hle) houtF
        · let nF := sInf (Stacks.DegreePExtensionLevel.extensionLevelNumerators S E FF PS
            (algebraMap B S (algebraMap A B piA)))
          have hnFt : nF < n := by simpa only [nF, hnpn] using hsmaller
          have hleF : Stacks.DegreePExtensionLevel.extensionLevel S E FF PS
              (algebraMap B S (algebraMap A B piA)) ep hep hneF ≤ t := by
            rw [Stacks.DegreePExtensionLevel.extensionLevel]
            calc
              (nF : ℚ) / (ep : ℚ) ≤ (np : ℚ) / (ep : ℚ) := by
                apply div_le_div_of_nonneg_right
                · exact_mod_cast Nat.le_of_lt hsmaller
                · exact_mod_cast (Nat.zero_le ep)
              _ = l := by rw [hlevelp, Stacks.DegreePExtensionLevel.extensionLevel, hnpeq]
              _ ≤ t := hle
          exact inner nF hnFt R S T K1 E FF hweakRS heppRS fS PS hPS hfiniteSF
            (algebraMap B S (algebraMap A B piA)) ep hep hneF
            (irreducible_algebraMap_of_isWeaklyUnramified hweakBS hpimap) hwS rfl hleF

/-- Outer induction on the rational extension level, with the least-numerator recursion above
discharging factors that decrease the numerator without yet crossing the level bound. -/
private theorem mixedFiniteLevelUpToSolvable_of_lt_prime
    (p : ℕ) [Fact p.Prime] (t : ℚ) (ht : 0 ≤ t) (htp : t < (p : ℚ)) :
    MixedFiniteLevelUpToSolvable.{u} p t := by
  refine IsDiscreteValuationRing.induction_on_level
    (P := MixedFiniteLevelUpToSolvable.{u} p) (mixedFiniteLevelUpToSolvable_zero p) ?_ ht htp
  intro x hx hxp ih
  have outer : MixedFiniteLevelUpToSolvable.{u} p
      (max 0 (max (x - 1) (2 * x - (p : ℚ)))) :=
    ih _ (le_max_left _ _) le_rfl
  intro A B C K L M
  intros
  rename_i hweak hepp hfin f P hP hfinite pi e he hne hpi hw hle
  exact mixedFiniteNumeratorUpToSolvable p x hx.le hxp outer
    (sInf (Stacks.DegreePExtensionLevel.extensionLevelNumerators B L M P pi))
    A B C K L M hweak hepp f P hP hfinite pi e he hne hpi hw rfl hle

/-- Every mixed-characteristic finite-level degree-`p` presentation is solvable.  The standard
cyclotomic uniformizer gives an extension level in `[0,p)`, where the outer recursion applies. -/
theorem exists_finite_extension_isWeakSolution_of_mixedFiniteLevel
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
    [Module.Finite L M]
    (f : CyclotomicRing p ℤ ℚ →+* B) (P : Polynomial B)
    (hP : intProp f P ∧ quotChar f P ∧ shapeProp f P ∧ funcEq f P)
    (hfinite : Stacks.DegreePExtensionLevel.IsDegreePExtensionOfFiniteLevel B L M p f P) :
    ∃ (K2 : Type u) (_ : Field K2) (_ : Algebra K K2) (_ : Algebra A K2)
      (_ : IsScalarTower A K K2) (_ : Module.Finite K K2),
      ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A C K M K2,
        D.IsWeakSolution := by
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  let : CharZero B := (algebraMap B L).charZero
  let : CharP (ResidueField B) p := charP_residueField_of_isExtension A B p
  obtain ⟨pi, e, hpi, he, hw⟩ := exists_irreducible_associated_pow_wElt B p f
  obtain ⟨hne, hl, hlp⟩ := exists_extensionLevel_mem_Ico B L M p f P pi e hfinite hpi he hw
  exact mixedFiniteLevelUpToSolvable_of_lt_prime p _ hl hlp
    A B C K L M hweak hepp f P hP hfinite pi e he hne hpi hw le_rfl

end Stacks.EppTheorem

end
