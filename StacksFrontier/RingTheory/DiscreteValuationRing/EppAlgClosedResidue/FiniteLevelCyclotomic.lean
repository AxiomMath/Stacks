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
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.IteratedPackages
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.TotallyRamifiedTensor

open Stacks.DegreePExtensionLevel
open Stacks.DiscreteValuationRing.EppLevelInduction

/-!
# Eliminating ramification: finite levels and the cyclotomic Galois case

The finite-level induction, the Galois case over a cyclotomic field, and normal field factors.

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

/-- The cyclotomic parameter has positive finite valuation in mixed characteristic. -/
theorem exists_irreducible_associated_pow_wElt
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [CharZero B]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField B) p]
    (f : CyclotomicRing p ℤ ℚ →+* B) :
    ∃ (π : B) (e : ℕ), Irreducible π ∧ 0 < e ∧ Associated (wElt f) (π ^ e) := by
  have hw : wElt f ≠ 0 := by
    intro h
    have hz : zetaA f = 1 := (sub_eq_zero.mp h).symm
    have hp := zetaA_geom_sum_eq_zero f
    simp only [hz, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hp
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hp
  have hpow : (zetaA f) ^ p = 1 := by
    dsimp [zetaA]
    rw [← map_pow]
    exact (congrArg f (IsCyclotomicExtension.zeta_spec p ℤ
      (CyclotomicRing p ℤ ℚ)).pow_eq_one).trans (map_one f)
  have hres : IsLocalRing.residue B (wElt f) = 0 := by
    have hpowRes : (IsLocalRing.residue B (zetaA f)) ^ p = 1 := by
      simpa only [map_pow, map_one] using congrArg (IsLocalRing.residue B) hpow
    have hzero : (IsLocalRing.residue B (zetaA f) - 1) ^ p = 0 := by
      rw [sub_pow_char, hpowRes, one_pow, sub_self]
    have hz : IsLocalRing.residue B (zetaA f) = 1 :=
      sub_eq_zero.mp (eq_zero_of_pow_eq_zero hzero)
    simp only [wElt, map_sub, map_one, hz, sub_self]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hw hπ
  refine ⟨π, e, hπ, Nat.pos_of_ne_zero ?_, he⟩
  intro he0
  have hu : IsUnit (wElt f) := he.isUnit_iff.mpr (by simp [he0])
  exact ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu) hres

/-- A field extension of a field of characteristic zero has characteristic zero. -/
private theorem charZero_of_algebra_field (K L : Type*) [Field K] [Field L] [Algebra K L]
    [CharZero K] : CharZero L :=
  charZero_of_injective_algebraMap (algebraMap K L).injective

/-- A field extension of a field of characteristic `p` has characteristic `p`. -/
private theorem charP_of_algebra_field (K L : Type*) [Field K] [Field L] [Algebra K L]
    (p : ℕ) [CharP K p] : CharP L p :=
  charP_of_injective_algebraMap (algebraMap K L).injective p

private abbrev FiniteLevelSolvable (p : ℕ) [Fact p.Prime] (l : ℚ) : Prop :=
  ∀ (A B C K L M : Type u)
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
    [CharZero K] [CharP (IsLocalRing.ResidueField A) p]
    [PerfectField (IsLocalRing.ResidueField A)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (_ : IsDiscreteValuationRing.IsWeaklyUnramified A B)
    [Module.Finite L M]
    (_ : ∀ x : IsLocalRing.ResidueField B,
      (∃ a : IsLocalRing.ResidueField A,
          algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) a = x) ↔
        ∀ n : ℕ, 1 ≤ n → ∃ y : IsLocalRing.ResidueField B, y ^ (p ^ n) = x)
    (f : CyclotomicRing p ℤ ℚ →+* B) (P : Polynomial B)
    (_ : intProp f P ∧ quotChar f P ∧ shapeProp f P ∧ funcEq f P)
    (_ : Stacks.DegreePExtensionLevel.IsDegreePExtensionOfFiniteLevel B L M p f P)
    (_ : ∃ (π : B) (e₁ : ℕ) (he₁ : 0 < e₁)
      (hne : (Stacks.DegreePExtensionLevel.extensionLevelNumerators B L M P π).Nonempty),
      Irreducible π ∧ Associated (wElt f) (π ^ e₁) ∧
        l = Stacks.DegreePExtensionLevel.extensionLevel B L M P π e₁ he₁ hne),
    ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{u,u,u,u,u,u,u,u} A C K M K₁,
        D.IsWeakSolution

/-- Iterating the finite-level reduction eliminates ramification in mixed characteristic. -/
private theorem finiteLevelSolvable (p : ℕ) [Fact p.Prime]
    (l : ℚ) (hl : 0 ≤ l) (hlp : l < (p : ℚ)) : FiniteLevelSolvable.{u} p l := by
  refine induction_on_level (P := FiniteLevelSolvable.{u} p) ?_ ?_ hl hlp
  · intro A B C K L M
    intros
    rename_i hweak hfin hresidue f P hP hfinite hlevel
    obtain ⟨π, e₁, he₁, hne, hπ, hw, hlevel⟩ := hlevel
    let : IsIntegralClosure C B M := isIntegralClosure_of_isAdicComplete B C L M
    let : CharZero L := charZero_of_algebra_field K L
    let : CharP (IsLocalRing.ResidueField B) p :=
      charP_of_algebra_field (IsLocalRing.ResidueField A) _ p
    have hBC : IsDiscreteValuationRing.IsWeaklyUnramified B C :=
      isWeaklyUnramified_of_extensionLevel_eq_zero B C L M p f P hP π hπ e₁ he₁ hne hlevel.symm
    obtain ⟨D⟩ := nonempty_integralClosureBaseChange A C K M K
    exact ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      D, isWeakSolution_self A C K M D (isWeaklyUnramified_trans A B C hweak hBC)⟩
  · intro l hl hlp ih A B C K L M
    intros
    rename_i hweak hfin hresidue f P hP hfinite hlevel
    obtain ⟨K₁, hK₁, hKK₁, hAK₁, htower, hfinK₁, hsep, htot, hnext⟩ :=
      exists_totallyRamified_isWeakSolution_or_extensionLevel_le
        A B C K L M p hweak f P hP hfinite l hlevel hl hresidue
    let := hK₁
    let := hKK₁
    let := hAK₁
    let := htower
    let := hfinK₁
    let := hsep
    rcases hnext with ⟨D, hD⟩ | hnext
    · exact ⟨K₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, D, hD⟩
    · obtain ⟨hL₁, hM₁, hB₁, hfrac, hfin₁, hfinite₁, π₁, e₁, he₁, hne₁, hπ₁, hw₁, hle⟩ := hnext
      apply exists_finite_extension_isWeakSolution_of_totallyRamified_tensorProduct
        A B C K L M K₁ p hweak hresidue htot hL₁ hM₁ hfin₁
      let := hL₁.toField
      let := hM₁.toField
      let : Algebra (L ⊗[K] K₁) (M ⊗[K] K₁) :=
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M)
          (AlgHom.id K K₁)).toRingHom.toAlgebra
      let : Algebra K₁ (L ⊗[K] K₁) := Algebra.TensorProduct.rightAlgebra
      let : Algebra K₁ (M ⊗[K] K₁) := Algebra.TensorProduct.rightAlgebra
      dsimp only
      intros
      rename_i hweak₁ hresidue₁
      let : Algebra (integralClosure A K₁) (L ⊗[K] K₁) :=
        ((algebraMap K₁ (L ⊗[K] K₁)).comp (algebraMap (integralClosure A K₁) K₁)).toAlgebra
      let : Algebra (integralClosure A K₁) (M ⊗[K] K₁) :=
        ((algebraMap K₁ (M ⊗[K] K₁)).comp (algebraMap (integralClosure A K₁) K₁)).toAlgebra
      let : Algebra (integralClosure B (L ⊗[K] K₁)) (M ⊗[K] K₁) :=
        ((algebraMap (L ⊗[K] K₁) (M ⊗[K] K₁)).comp
          (algebraMap (integralClosure B (L ⊗[K] K₁)) (L ⊗[K] K₁))).toAlgebra
      let : CharZero K₁ := charZero_of_algebra_field K K₁
      apply ih _ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hle
        (integralClosure A K₁) (integralClosure B (L ⊗[K] K₁))
        (integralClosure C (M ⊗[K] K₁)) K₁ (L ⊗[K] K₁) (M ⊗[K] K₁)
        hweak₁ hresidue₁ ((algebraMap B (integralClosure B (L ⊗[K] K₁))).comp f)
        (P.map (algebraMap B (integralClosure B (L ⊗[K] K₁))))
        (Stacks.DiscreteValuationRing.EppLevelInduction.cyclotomic_properties_map f P hP _)
        hfinite₁
      exact ⟨π₁, e₁, he₁, hne₁, hπ₁, hw₁, rfl⟩

/-- A mixed-characteristic degree-`p` extension of finite level is solvable once the
perfect-core residue condition required by the level-reduction step holds.  Unlike the original
09F8-local version, this recursion only requires the base residue field to be perfect. -/
theorem exists_finite_extension_isWeakSolution_of_finiteLevel_of_perfectResidue
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
    [CharZero K] [CharP (IsLocalRing.ResidueField A) p]
    [PerfectField (IsLocalRing.ResidueField A)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (hweak : IsDiscreteValuationRing.IsWeaklyUnramified A B)
    [Module.Finite L M]
    (hresidue : ∀ x : IsLocalRing.ResidueField B,
      (∃ a : IsLocalRing.ResidueField A,
          algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) a = x) ↔
        ∀ n : ℕ, 1 ≤ n → ∃ y : IsLocalRing.ResidueField B, y ^ (p ^ n) = x)
    (f : CyclotomicRing p ℤ ℚ →+* B) (P : Polynomial B)
    (hP : intProp f P ∧ quotChar f P ∧ shapeProp f P ∧ funcEq f P)
    (hfinite : Stacks.DegreePExtensionLevel.IsDegreePExtensionOfFiniteLevel B L M p f P) :
    ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{u,u,u,u,u,u,u,u} A C K M K₁,
        D.IsWeakSolution := by
  let : CharZero L := charZero_of_algebra_field K L
  let : CharZero B := (algebraMap B L).charZero
  let : CharP (IsLocalRing.ResidueField B) p :=
    charP_of_algebra_field (IsLocalRing.ResidueField A) _ p
  obtain ⟨π, e, hπ, he, hw⟩ := exists_irreducible_associated_pow_wElt B p f
  obtain ⟨hne, hl, hlp⟩ := exists_extensionLevel_mem_Ico B L M p f P π e hfinite hπ he hw
  exact finiteLevelSolvable p _ hl hlp A B C K L M hweak hresidue f P hP hfinite
    ⟨π, e, he, hne, hπ, hw, rfl⟩

/-- The cyclotomic entry point to the mixed-characteristic degree-`p` solver over a perfect
residue field, under the finite-level perfect-core residue condition. -/
theorem exists_finite_extension_isWeakSolution_of_isGalois_of_cyclotomic_of_perfectResidue
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
    [CharZero K] [CharP (IsLocalRing.ResidueField A) p]
    [PerfectField (IsLocalRing.ResidueField A)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (hweak : IsDiscreteValuationRing.IsWeaklyUnramified A B)
    [Module.Finite L M]
    (hresidue : ∀ x : IsLocalRing.ResidueField B,
      (∃ a : IsLocalRing.ResidueField A,
          algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) a = x) ↔
        ∀ n : ℕ, 1 ≤ n → ∃ y : IsLocalRing.ResidueField B, y ^ (p ^ n) = x)
    [IsGalois L M] (hdegree : Module.finrank L M = p)
    (f : CyclotomicRing p ℤ ℚ →+* B) :
    ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{u,u,u,u,u,u,u,u} A C K M K₁,
        D.IsWeakSolution := by
  obtain ⟨K₁, hK₁, hKK₁, hAK₁, htower, hfinK₁, htot, hnext⟩ :=
    exists_totallyRamified_galoisExtension_isWeakSolution_or_finiteLevel
      A B C K L M p hweak f hdegree
  let := hK₁
  let := hKK₁
  let := hAK₁
  let := htower
  let := hfinK₁
  rcases hnext with ⟨D, hD⟩ | hnext
  · exact ⟨K₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, D, hD⟩
  · obtain ⟨hL₁, hM₁, hB₁, hfrac, hfin₁, P, hint, hquot, hshape, hfunc, hfinite₁⟩ := hnext
    apply exists_finite_extension_isWeakSolution_of_totallyRamified_tensorProduct
      A B C K L M K₁ p hweak hresidue htot hL₁ hM₁ hfin₁
    let := hL₁.toField
    let := hM₁.toField
    let : Algebra (L ⊗[K] K₁) (M ⊗[K] K₁) :=
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M)
        (AlgHom.id K K₁)).toRingHom.toAlgebra
    let : Algebra K₁ (L ⊗[K] K₁) := Algebra.TensorProduct.rightAlgebra
    let : Algebra K₁ (M ⊗[K] K₁) := Algebra.TensorProduct.rightAlgebra
    dsimp only
    intros
    rename_i hweak₁ hresidue₁
    let : Algebra (integralClosure A K₁) (L ⊗[K] K₁) :=
      ((algebraMap K₁ (L ⊗[K] K₁)).comp (algebraMap (integralClosure A K₁) K₁)).toAlgebra
    let : Algebra (integralClosure A K₁) (M ⊗[K] K₁) :=
      ((algebraMap K₁ (M ⊗[K] K₁)).comp (algebraMap (integralClosure A K₁) K₁)).toAlgebra
    let : Algebra (integralClosure B (L ⊗[K] K₁)) (M ⊗[K] K₁) :=
      ((algebraMap (L ⊗[K] K₁) (M ⊗[K] K₁)).comp
        (algebraMap (integralClosure B (L ⊗[K] K₁)) (L ⊗[K] K₁))).toAlgebra
    let : CharZero K₁ := charZero_of_algebra_field K K₁
    exact exists_finite_extension_isWeakSolution_of_finiteLevel_of_perfectResidue p
      (integralClosure A K₁) (integralClosure B (L ⊗[K] K₁))
      (integralClosure C (M ⊗[K] K₁)) K₁ (L ⊗[K] K₁) (M ⊗[K] K₁)
      hweak₁ hresidue₁ ((algebraMap B (integralClosure B (L ⊗[K] K₁))).comp f)
      (P.map (algebraMap B (integralClosure B (L ⊗[K] K₁))))
      (Stacks.DiscreteValuationRing.EppLevelInduction.cyclotomic_properties_map f P
        ⟨hint, hquot, hshape, hfunc⟩ _) hfinite₁

/-- A map out of a finite product of algebras factors through one component. -/
theorem AlgHom.exists_comp_evalAlgHom_eq
    (R T : Type*) [CommRing R] [CommRing T] [IsDomain T] [Algebra R T]
    {ι : Type*} [Finite ι] (S : ι → Type*) [∀ i, CommRing (S i)]
    [∀ i, Algebra R (S i)] (f : (∀ i, S i) →ₐ[R] T) :
    ∃ (i : ι) (g : S i →ₐ[R] T), g.comp (Pi.evalAlgHom R S i) = f
 := by
  classical
  let q : PrimeSpectrum (∀ i, S i) := ⟨RingHom.ker f.toRingHom, RingHom.ker_isPrime _⟩
  obtain ⟨i, r, hr⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq q
  have hr' : r.asIdeal.comap (Pi.evalRingHom S i) = RingHom.ker f.toRingHom :=
    congrArg PrimeSpectrum.asIdeal hr
  have hker : RingHom.ker (Pi.evalAlgHom R S i).toRingHom ≤ RingHom.ker f.toRingHom := by
    rw [← hr']
    exact Ideal.comap_mono bot_le
  have hsurj : Function.Surjective (Pi.evalAlgHom R S i) :=
    Function.surjective_eval i
  exact ⟨i, (Pi.evalAlgHom R S i).liftOfSurjective hsurj f hker,
    (Pi.evalAlgHom R S i).liftOfSurjective_comp hsurj f hker⟩


/-- Normality and the degree bound transfer along a surjection out of a base-changed tensor
product. -/
theorem normal_and_finrank_le_of_surjective_tensorProduct
    (F E K L : Type*) [Field F] [Field E] [Field K] [Field L]
    [Algebra F E] [Algebra F K] [Algebra F L] [Algebra E L] [Algebra K L]
    [IsScalarTower F E L] [IsScalarTower F K L]
    [Module.Finite F E] [Normal F E]
    (hsurj : Function.Surjective
      ((AlgHom.liftEquiv F K E L) (IsScalarTower.toAlgHom F E L))) :
    Module.Finite K L ∧ Normal K L ∧ Module.finrank K L ≤ Module.finrank F E
 := by
  let φ := (AlgHom.liftEquiv F K E L) (IsScalarTower.toAlgHom F E L)
  let : Module.Finite K L := Module.Finite.of_surjective φ.toLinearMap hsurj
  have hbound : Module.finrank K L ≤ Module.finrank F E := by
    simpa only [Module.finrank_baseChange] using
      (LinearMap.finrank_le_finrank_of_surjective (f := φ.toLinearMap) hsurj)
  have hgen : IntermediateField.adjoin K (Set.range (algebraMap E L)) = ⊤ := by
    apply top_unique
    intro x hx
    clear hx
    obtain ⟨t, rfl⟩ := hsurj x
    induction t using TensorProduct.induction_on with
    | zero => simpa only [map_zero] using (IntermediateField.adjoin K _).zero_mem
    | tmul k e =>
      change φ (k ⊗ₜ[F] e) ∈ _
      rw [AlgHom.liftEquiv_tmul]
      exact (IntermediateField.adjoin K (Set.range (algebraMap E L))).smul_mem
        (IntermediateField.subset_adjoin K (Set.range (algebraMap E L)) ⟨e, rfl⟩)
    | add t₁ t₂ h₁ h₂ => simpa only [map_add] using (IntermediateField.adjoin K _).add_mem h₁ h₂
  refine ⟨inferInstance, normal_iff.mpr ?_, hbound⟩
  intro x
  refine ⟨IsIntegral.of_finite K x, IntermediateField.splits_of_mem_adjoin K L
    (S := Set.range (algebraMap E L)) ?_ ?_⟩
  · rintro y ⟨e, rfl⟩
    refine ⟨IsIntegral.of_finite K _, ?_⟩
    have hs := (Normal.splits' (F := F) e).map (algebraMap E L)
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at hs
    have hd := Polynomial.map_dvd (algebraMap K L)
      (minpoly.dvd_map_of_isScalarTower F K (algebraMap E L e))
    have hm : minpoly F (algebraMap E L e) = minpoly F e :=
      minpoly.algHom_eq (IsScalarTower.toAlgHom F E L)
        (IsScalarTower.toAlgHom F E L).injective e
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq, hm] at hd
    exact hs.of_dvd (Polynomial.map_ne_zero (minpoly.ne_zero (IsIntegral.of_finite F e))) hd
  · rw [hgen]
    trivial

/-- In a finite flat local extension of domains, the ramification index divides its rank.

At a member of a layer recursion whose upper layer has degree one this is what forces the
ramification index there to be one, with no hypothesis on the residue field at all. -/
theorem ramificationIdx_dvd_finrank_of_isLocalRing
    (R S : Type*) [CommRing R] [CommRing S] [IsDomain R]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Finite R S] [Module.Flat R S] :
    (IsLocalRing.maximalIdeal S).ramificationIdx R ∣ Module.finrank R S
 := by
  classical
  let p := IsLocalRing.maximalIdeal R
  let q := IsLocalRing.maximalIdeal S
  let : Unique (p.primesOver S) :=
    { default := Ideal.primesOver.mk p q
      uniq P := Subtype.ext (IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P.1 (by
          change (P.1.under R).IsMaximal
          rw [← Ideal.over_def P.1 p]
          infer_instance))) }
  have h := Ideal.sum_ramification_inertia_eq_finrank p S
  have heq : q.ramificationIdx R * q.inertiaDeg R = Module.finrank R S := by
    simp only [Finset.univ_unique, Finset.sum_singleton] at h
    rw [show (default : p.primesOver S) = Ideal.primesOver.mk p q from Subsingleton.elim _ _] at h
    exact h
  exact ⟨q.inertiaDeg R, heq.symm⟩

/-- **At a factor of the upper base change, the matching factor of the lower one, with
normality and a degree bound.**

This is what makes the layer recursion's re-entry possible: the new members are the factors `F`
of `(M ⊗[K] N)ᵣₑd` over the factors `H i` of `(L ⊗[K] N)ᵣₑd`, and
`Stacks.EppTheorem.FamilyTowerSolvable` requires each to be `Normal` and of bounded degree.

The bound is `≤ Module.finrank L M`, not `<`. A recursion gets its strict decrease from having
already absorbed a bottom layer — apply this with `L` the bottom layer's top — not from
here. -/
theorem exists_fieldFactor_normal_and_finrank_le
    (K L M N F : Type*) [Field K] [Field L] [Field M] [Field N] [Field F]
    [Algebra K L] [Algebra L M] [Algebra K M] [Algebra K N]
    [Algebra K F] [Algebra L F] [Algebra M F] [Algebra N F]
    [IsScalarTower K L M] [IsScalarTower K M F] [IsScalarTower K L F]
    [IsScalarTower L M F] [IsScalarTower K N F]
    [Module.Finite L M] [Normal L M]
    {ι : Type*} [Finite ι] (H : ι → Type*) [∀ i, Field (H i)]
    [∀ i, Algebra L (H i)] [∀ i, Algebra N (H i)] :
    letI : Algebra N (L ⊗[K] N) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra N (M ⊗[K] N) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra N (ReducedTensorTower.Reduction (L ⊗[K] N)) := Ideal.Quotient.algebra N
    ∀ (e : ReducedTensorTower.Reduction (L ⊗[K] N) ≃ₐ[N] ∀ i, H i)
      (_ : ∀ i l, e (Ideal.Quotient.mk _ (l ⊗ₜ[K] (1 : N))) i = algebraMap L (H i) l)
      (φ : (M ⊗[K] N) →ₐ[N] F)
      (_ : ∀ m n, φ (m ⊗ₜ[K] n) = algebraMap M F m * algebraMap N F n)
      (_ : Function.Surjective φ),
      ∃ (i : ι) (g : H i →ₐ[N] F),
        letI : Algebra (H i) F := g.toRingHom.toAlgebra
        IsScalarTower L (H i) F ∧ Module.Finite (H i) F ∧ Normal (H i) F ∧
          Module.finrank (H i) F ≤ Module.finrank L M
 := by
  let : Algebra N (L ⊗[K] N) := Algebra.TensorProduct.rightAlgebra
  let : Algebra N (M ⊗[K] N) := Algebra.TensorProduct.rightAlgebra
  let : Algebra N (ReducedTensorTower.Reduction (L ⊗[K] N)) := Ideal.Quotient.algebra N
  intro e he φ hφ hsurj
  let ι : (L ⊗[K] N) →ₐ[N] M ⊗[K] N :=
    { __ := (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M)
        (AlgHom.id K N)).toRingHom
      commutes' n := by
        change algebraMap L M 1 ⊗ₜ[K] n = (1 : M) ⊗ₜ[K] n
        rw [map_one] }
  have hι (l : L) (n : N) : ι (l ⊗ₜ[K] n) = algebraMap L M l ⊗ₜ[K] n := rfl
  let r : ReducedTensorTower.Reduction (L ⊗[K] N) →ₐ[N] F :=
    Ideal.Quotient.liftₐ _ (φ.comp ι) fun t ht =>
      ((mem_nilradical.mp ht).map (φ.comp ι)).eq_zero
  obtain ⟨i, g, hg⟩ := AlgHom.exists_comp_evalAlgHom_eq N F H (r.comp e.symm.toAlgHom)
  have hfactor (t : L ⊗[K] N) : g (e (Ideal.Quotient.mk _ t) i) = φ (ι t) := by
    have h := congrArg (fun f : (∀ i, H i) →ₐ[N] F => f (e (Ideal.Quotient.mk _ t))) hg
    change g (e (Ideal.Quotient.mk _ t) i) = r (e.symm (e (Ideal.Quotient.mk _ t))) at h
    rw [AlgEquiv.symm_apply_apply] at h
    exact h.trans (by
      change (Ideal.Quotient.lift _ (φ.comp ι).toRingHom _) (Ideal.Quotient.mk _ t) = _
      rw [Ideal.Quotient.lift_mk]
      rfl)
  let : Algebra (H i) F := g.toRingHom.toAlgebra
  let : IsScalarTower N (H i) F := IsScalarTower.of_algHom g
  let : IsScalarTower L (H i) F := IsScalarTower.of_algebraMap_eq fun l => by
    change algebraMap L F l = g (algebraMap L (H i) l)
    rw [← he i l, hfactor, hι, hφ, map_one, mul_one,
      ← IsScalarTower.algebraMap_apply L M F]
  let ψ := (AlgHom.liftEquiv L (H i) M F) (IsScalarTower.toAlgHom L M F)
  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨t, rfl⟩ := hsurj x
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
    | tmul m n =>
      refine ⟨algebraMap N (H i) n ⊗ₜ[L] m, ?_⟩
      rw [AlgHom.liftEquiv_tmul, Algebra.smul_def, hφ]
      change g (algebraMap N (H i) n) * algebraMap M F m = _
      rw [g.commutes, mul_comm]
    | add t₁ t₂ h₁ h₂ =>
      obtain ⟨x₁, hx₁⟩ := h₁
      obtain ⟨x₂, hx₂⟩ := h₂
      exact ⟨x₁ + x₂, by rw [map_add, hx₁, hx₂, map_add]⟩
  exact ⟨i, g, inferInstance, normal_and_finrank_le_of_surjective_tensorProduct L M (H i) F hψ⟩

abbrev NormalTowerSolvable (p : ℕ) [Fact p.Prime] (n : ℕ) : Prop :=
  ∀ (A B C K L M : Type u)
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
    (_ : IsDiscreteValuationRing.IsWeaklyUnramified A B)
    [Module.Finite L M]
    (_ : ∀ x : IsLocalRing.ResidueField B,
      (∃ a : IsLocalRing.ResidueField A,
          algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) a = x) ↔
        ∀ n : ℕ, 1 ≤ n → ∃ y : IsLocalRing.ResidueField B, y ^ (p ^ n) = x)
    [Normal L M]
    (_ : Module.finrank L M ≤ n)
    (_ : CharZero K → Nonempty (CyclotomicRing p ℤ ℚ →+* A)),
    ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{u,u,u,u,u,u,u,u} A C K M K₁,
        D.IsWeakSolution

theorem
    exists_finite_extension_isWeakSolution_of_normal_factor_induction_of_cyclotomic_extension
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
    (hsol : ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{u,u,u,u,u,u,u,u} A B K L K₁,
        D.IsWeakSolution ∧
          (CharZero K₁ → Nonempty (CyclotomicRing p ℤ ℚ →+* integralClosure A K₁)))
    (hnext : NormalTowerSolvable.{u} p (Module.finrank L M)) :
    ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{u,u,u,u,u,u,u,u} A C K M K₁,
        D.IsWeakSolution
 := by
  classical
  let : IsScalarTower A B M := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A C M, IsScalarTower.algebraMap_apply A B C,
      ← IsScalarTower.algebraMap_apply B C M]
  let : IsIntegralClosure C B M := isIntegralClosure_of_isAdicComplete B C L M
  let : Module.Finite B (integralClosure B M) :=
    (isDiscreteValuationRing_and_finite_integralClosure_of_isAdicComplete B L M).2
  let : Module.Finite B C := Module.Finite.equiv
    (IsIntegralClosure.equiv B (integralClosure B M) M C).toLinearEquiv
  let : IsAdicComplete (IsLocalRing.maximalIdeal C) C := isAdicComplete_of_finite B C
  obtain ⟨K₁, hK₁, hKK₁, hAK₁, htower, hfinK₁, D, hD, hcycloR⟩ := hsol
  let := hK₁
  let := hKK₁
  let := hAK₁
  let := htower
  let := hfinK₁
  obtain ⟨D'⟩ := nonempty_integralClosureBaseChange A C K M K₁
  obtain ⟨n, H, hH, hLH, hKH, hBH, hAH, hBLH, hABH, hAKH, hfinH, hn, eH, heH⟩ :=
    finiteFieldFactors_compatible A B K L K₁ D
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
    finiteFieldFactors_compatible A C K M K₁ D'
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
    ((algebraMap K₁ (H i)).comp (algebraMap K K₁)).toAlgebra
  let : ∀ i, Algebra K (F i) := fun i =>
    ((algebraMap K₁ (F i)).comp (algebraMap K K₁)).toAlgebra
  let : ∀ i, IsScalarTower K K₁ (H i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, IsScalarTower K K₁ (F i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra K₁ (L ⊗[K] K₁) := Algebra.TensorProduct.rightAlgebra
  let : Algebra K₁ (M ⊗[K] K₁) := Algebra.TensorProduct.rightAlgebra
  let : Algebra K₁ (ReducedTensorTower.Reduction (L ⊗[K] K₁)) := Ideal.Quotient.algebra K₁
  let : Algebra K₁ (ReducedTensorTower.Reduction (M ⊗[K] K₁)) := Ideal.Quotient.algebra K₁
  let eH' := reducedTensorFactorsEquiv K L K₁ D.L₁ H D.eL₁ eH D.eL₁_right heH
  let eF' := reducedTensorFactorsEquiv K M K₁ D'.L₁ F D'.eL₁ eF D'.eL₁_right heF
  let φ (i : Fin m) : (M ⊗[K] K₁) →ₐ[K₁] F i :=
    ((Pi.evalAlgHom K₁ F i).comp eF'.toAlgHom).comp (Ideal.Quotient.mkₐ K₁ _)
  have hφleft (i : Fin m) (x : M) : φ i (x ⊗ₜ[K] (1 : K₁)) = algebraMap M (F i) x :=
    reducedTensorFactorsEquiv_left K M K₁ D'.L₁ F D'.eL₁ eF D'.eL₁_right heF D'.eL₁_left x i
  have hφright (i : Fin m) (x : K₁) : φ i ((1 : M) ⊗ₜ[K] x) = algebraMap K₁ (F i) x :=
    (φ i).commutes x
  have hφ (i : Fin m) (x : M) (y : K₁) :
      φ i (x ⊗ₜ[K] y) = algebraMap M (F i) x * algebraMap K₁ (F i) y := by
    rw [show x ⊗ₜ[K] y = (x ⊗ₜ[K] (1 : K₁)) * ((1 : M) ⊗ₜ[K] y) by
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul],
      map_mul, hφleft, hφright]
  have hφsurj (i : Fin m) : Function.Surjective (φ i) := by
    have hev : Function.Surjective (Pi.evalAlgHom K₁ F i) :=
      Function.surjective_eval i
    exact hev.comp (eF'.surjective.comp Ideal.Quotient.mk_surjective)
  let : ∀ i, IsScalarTower K M (F i) := fun i => IsScalarTower.of_algebraMap_eq fun x => by
    have ht : (algebraMap K M x) ⊗ₜ[K] (1 : K₁) = (1 : M) ⊗ₜ[K] algebraMap K K₁ x := by
      change (Algebra.TensorProduct.includeLeft : M →ₐ[K] _) (algebraMap K M x) =
        (Algebra.TensorProduct.includeRight : K₁ →ₐ[K] _) (algebraMap K K₁ x)
      rw [AlgHom.commutes, AlgHom.commutes]
    have hx := congrArg (φ i) ht
    rw [hφleft, hφright] at hx
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
  have hfac (i : Fin m) := exists_fieldFactor_normal_and_finrank_le K L M K₁ (F i) H eH'
    (fun j x => reducedTensorFactorsEquiv_left K L K₁ D.L₁ H D.eL₁ eH
      D.eL₁_right heH D.eL₁_left x j) (φ i) (hφ i) (hφsurj i)
  choose j g hLHFin hfinHF hnormal hbound using hfac
  let : ∀ i, Algebra (H (j i)) (F i) := fun i => (g i).toRingHom.toAlgebra
  let : ∀ i, IsScalarTower L (H (j i)) (F i) := hLHFin
  let : ∀ i, IsScalarTower K₁ (H (j i)) (F i) := fun i => IsScalarTower.of_algHom (g i)
  let := hfinHF
  let := hnormal
  let : ∀ i, IsScalarTower B (H (j i)) (F i) := fun i => IsScalarTower.of_algebraMap_eq fun b => by
    rw [IsScalarTower.algebraMap_apply B L (F i),
      IsScalarTower.algebraMap_apply L (H (j i)) (F i),
      ← IsScalarTower.algebraMap_apply B L (H (j i))]
  let R := integralClosure A K₁
  let S (i : Fin m) := integralClosure B (H (j i))
  let T (i : Fin m) := integralClosure C (F i)
  obtain ⟨hR, hAR, hRfin, hRc, hRf⟩ := integralClosure_isCompleteDVR A K K₁
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
  let f (i : Fin m) := mapIntegralClosureOfTower A B K₁ (H (j i))
  let h (i : Fin m) := mapIntegralClosureOfTower A C K₁ (F i)
  let t (i : Fin m) := mapIntegralClosureOfTower B C (H (j i)) (F i)
  let : ∀ i, Algebra R (S i) := fun i => (f i).toRingHom.toAlgebra
  let : ∀ i, Algebra R (T i) := fun i => (h i).toRingHom.toAlgebra
  let : ∀ i, Algebra (S i) (T i) := fun i => (t i).toRingHom.toAlgebra
  let : ∀ i, Algebra R (H (j i)) := fun i =>
    ((algebraMap K₁ (H (j i))).comp (algebraMap R K₁)).toAlgebra
  let : ∀ i, Algebra R (F i) := fun i =>
    ((algebraMap K₁ (F i)).comp (algebraMap R K₁)).toAlgebra
  let : ∀ i, Algebra (S i) (F i) := fun i =>
    ((algebraMap (H (j i)) (F i)).comp (algebraMap (S i) (H (j i)))).toAlgebra
  let : ∀ i, @IsScalarTower R K₁ (H (j i))
      (inferInstance : Algebra R K₁).toSMul (inferInstance : Algebra K₁ (H (j i))).toSMul
      (inferInstance : Algebra R (H (j i))).toSMul := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, @IsScalarTower R K₁ (F i)
      (inferInstance : Algebra R K₁).toSMul (inferInstance : Algebra K₁ (F i)).toSMul
      (inferInstance : Algebra R (F i)).toSMul := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, @IsScalarTower (S i) (H (j i)) (F i)
      (inferInstance : Algebra (S i) (H (j i))).toSMul
      (inferInstance : Algebra (H (j i)) (F i)).toSMul
      (inferInstance : Algebra (S i) (F i)).toSMul := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, @IsScalarTower R (S i) (H (j i))
      (inferInstance : Algebra R (S i)).toSMul (inferInstance : Algebra (S i) (H (j i))).toSMul
      (inferInstance : Algebra R (H (j i))).toSMul :=
    fun _ => IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : ∀ i, @IsScalarTower (S i) (T i) (F i)
      (inferInstance : Algebra (S i) (T i)).toSMul (inferInstance : Algebra (T i) (F i)).toSMul
      (inferInstance : Algebra (S i) (F i)).toSMul :=
    fun _ => IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : ∀ i, @IsScalarTower R (T i) (F i)
      (inferInstance : Algebra R (T i)).toSMul (inferInstance : Algebra (T i) (F i)).toSMul
      (inferInstance : Algebra R (F i)).toSMul :=
    fun _ => IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : ∀ i, @IsScalarTower R (S i) (T i)
      (inferInstance : Algebra R (S i)).toSMul (inferInstance : Algebra (S i) (T i)).toSMul
      (inferInstance : Algebra R (T i)).toSMul := fun i =>
    IsScalarTower.of_algebraMap_eq fun a => by
      apply Subtype.ext
      exact IsScalarTower.algebraMap_apply K₁ (H (j i)) (F i) a.1
  let : ∀ i, IsScalarTower A R (S i) := fun i =>
    IsScalarTower.of_algebraMap_eq fun a => ((f i).commutes a).symm
  let : ∀ i, IsDiscreteValuationRing.IsExtension R (S i) := fun i =>
    (integralClosure_factor_isExtension A B K L K₁ (H (j i))).choose_spec.choose_spec.1
  let : ∀ i, IsDiscreteValuationRing.IsExtension R (T i) := fun i =>
    (integralClosure_factor_isExtension A C K M K₁ (F i)).choose_spec.choose_spec.1
  let : ∀ i, IsDiscreteValuationRing.IsExtension (S i) (T i) := fun i =>
    (integralClosure_factor_isExtension B C L M (H (j i)) (F i)).choose_spec.choose_spec.1
  let : IsAlgClosed (IsLocalRing.ResidueField R) := isAlgClosed_residueField_of_finite A R
  let : CharP (IsLocalRing.ResidueField R) p :=
    charP_of_algebra_field (IsLocalRing.ResidueField A) _ p
  have hweak (i : Fin m) : IsDiscreteValuationRing.IsWeaklyUnramified R (S i) :=
    (isWeaklyUnramified_iff_ramificationIdx_eq_one R (S i)).mpr
      (isWeakSolution_factor A B K L K₁ D H eH heH hD (j i)
        (IsLocalRing.maximalIdeal (S i)) (IsLocalRing.maximalIdeal.isMaximal _))
  let : ∀ i, IsLocalHom (algebraMap A (S i)) := fun i => by
    rw [IsScalarTower.algebraMap_eq A B (S i)]
    infer_instance
  have hres (i : Fin m) :=
    residueField_forall_exists_pow_iff_of_finite_square A B R (S i) p hresidue
  have hsol (i : Fin m) :
      ∃ (E : Type u) (_ : Field E) (_ : Algebra K₁ E) (_ : Algebra R E)
        (_ : @IsScalarTower R K₁ E
          (inferInstance : Algebra R K₁).toSMul (inferInstance : Algebra K₁ E).toSMul
          (inferInstance : Algebra R E).toSMul) (_ : Module.Finite K₁ E),
        ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{u,u,u,u,u,u,u,u}
          R (T i) K₁ (F i) E, D.IsWeakSolution :=
    hnext R (S i) (T i) K₁ (H (j i)) (F i) (hweak i) (hres i) (hbound i) hcycloR
  apply exists_finite_extension_isWeakSolution_of_factor_solutions A C K M K₁ R F (fun i => ↥(T i))
    ?_ ?_ ?_ hsol eF'
    (fun i x => reducedTensorFactorsEquiv_left K M K₁ D'.L₁ F D'.eL₁ eF
      D'.eL₁_right heF D'.eL₁_left x i)
  · intro a
    rw [← IsScalarTower.algebraMap_apply A K K₁, ← IsScalarTower.algebraMap_apply A R K₁]
  · intro i c
    rw [← IsScalarTower.algebraMap_apply C M (F i), ← IsScalarTower.algebraMap_apply C (T i) (F i)]
  · intro i a
    apply Subtype.ext
    change algebraMap C (F i) (algebraMap A C a) = algebraMap K₁ (F i) (algebraMap A K₁ a)
    rw [← IsScalarTower.algebraMap_apply A C (F i), ← IsScalarTower.algebraMap_apply A K₁ (F i)]

end IsDiscreteValuationRing
