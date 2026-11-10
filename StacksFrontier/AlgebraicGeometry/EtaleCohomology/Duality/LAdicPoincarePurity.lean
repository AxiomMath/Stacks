module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTowerSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusPoincarePairing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LAdicLevelPairing
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.PerfectTowerReduction

/-!
# Purity from perfect pairings of the finite levels

Let `F`, `F'` be ℓ-adic sheaves with flat levels whose complexes `RΓ_c(X_k̄, Fₙ)`,
`RΓ_c(X_k̄, F'ₙ)` are perfect (so that they form towers of perfect complexes, Tag 03V4).
Suppose that for every `n` there is a pairing
`εₙ : Hⁱ_c(X_k̄, Fₙ) × H^{2d-i}_c(X_k̄, F'ₙ) → ℤ/ℓⁿ⁺¹`, nondegenerate on both sides, under which
the canonical geometric Frobenius scales by `q^d`; this is Poincaré duality at finite level.
Then the Frobenius on `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` is pure of weight `i` as soon as it is mixed of
weight `≤ i` and the Frobenius on `H^{2d-i}_c(X_k̄, F' ⊗ ℚ_ℓ)` is mixed of weight `≤ 2d - i`.

This is the deduction of the last assertion of Tag 03VH from Poincaré duality: the finite
level pairings give a perfect `ℚ_ℓ`-pairing (by the tower facts of
`Stacks.InverseSystem.exists_eq_pow_smul_of_limit_π_eq_zero_and_pow_smul_mem_range` and
`Stacks.EtaleCohomology.LAdicPairing.exists_isPerfPair_extendScalars_of_levels`), to which
`Stacks.EtaleCohomology.isCharpolyPureOfWeight_of_isPerfPair` applies.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.isCharpolyPureOfWeight_of_levelPairing`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale
open Stacks.Frobenius Stacks.InverseSystem

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
  ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1] [Fact ℓ.Prime]

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **Purity from finite level Poincaré duality.**  If the levels of `F` and `F'` are flat with
perfect `RΓ_c(X_k̄, -)`, and for every `n` a pairing `εₙ` of `Hⁱ_c(X_k̄, Fₙ)` and
`H^{2d-i}_c(X_k̄, F'ₙ)` with values in `ℤ/ℓⁿ⁺¹` is nondegenerate on both sides and scaled by
`q^d` under the geometric Frobenius, then the Frobenius on `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` is pure of
weight `i`, given that it is mixed of weight `≤ i` and that on `H^{2d-i}_c(X_k̄, F' ⊗ ℚ_ℓ)` is
mixed of weight `≤ 2d - i`. -/
theorem LAdicSheaf.isCharpolyPureOfWeight_of_levelPairing (F F' : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F n))
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ F n))))
    (hF' : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F' n))
    (hP' : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ F' n))))
    (i : ℤ) (d : ℕ) (ι : ℚ_[ℓ] →+* ℂ)
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)]
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F' (2 * d - i))]
    (hwt : IsCharpolyMixedOfWeightLE (p ^ q) ι i
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F i).hom)
    (hwt' : IsCharpolyMixedOfWeightLE (p ^ q) ι (2 * d - i)
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F'
        (2 * d - i)).hom)
    (ε : ∀ n, (geometricCompactSupportPadicCohomology B X ℓ f j kbar i).obj
        (LAdicSheaf.padicLevel B X ℓ F n) →+
      (geometricCompactSupportPadicCohomology B X ℓ f j kbar (2 * d - i)).obj
        (LAdicSheaf.padicLevel B X ℓ F' n) →+ ZMod (ℓ ^ (n + 1)))
    (hl : ∀ n x, (∀ y, ε n x y = 0) → x = 0) (hr : ∀ n y, (∀ x, ε n x y = 0) → y = 0)
    (hε : ∀ n x y, ε n ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f j kbar p q hcard
        ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F n)) i).hom x)
      ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f j kbar p q hcard
        ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F' n))
          (2 * d - i)).hom y) = (((p ^ q) ^ d : ℕ) : ZMod (ℓ ^ (n + 1))) * ε n x y) :
    IsCharpolyPureOfWeight (p ^ q) ι i
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
        i).hom := by
  let e := LAdicSheaf.geometricLevelCohomologySystemIso B X ℓ f j kbar p q hcard F hF hP i
  let e' := LAdicSheaf.geometricLevelCohomologySystemIso B X ℓ f j kbar p q hcard F' hF' hP'
    (2 * d - i)
  have : Module.Finite ℤ_[ℓ]
      (LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar F i) :=
    Stacks.InverseSystem.finite_limit_of_iso _ i e
  have : Module.Finite ℤ_[ℓ]
      (LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar F' (2 * d - i)) :=
    Stacks.InverseSystem.finite_limit_of_iso _ (2 * d - i) e'
  obtain ⟨c₁, h₁⟩ :=
    Stacks.InverseSystem.exists_eq_pow_smul_of_limit_π_eq_zero_and_pow_smul_mem_range _ i e
  obtain ⟨c₂, h₂⟩ :=
    Stacks.InverseSystem.exists_eq_pow_smul_of_limit_π_eq_zero_and_pow_smul_mem_range _
      (2 * d - i) e'
  -- one exponent for both sides
  have hraise {N M : Type (u + 1)} [AddCommGroup N] [AddCommGroup M] (π : M →+ N) (c K : ℕ)
      (hcK : c ≤ K) (h : ∀ y, ∃ a, π a = (ℓ ^ c) • y) (y : N) : ∃ a, π a = (ℓ ^ K) • y := by
    obtain ⟨a, ha⟩ := h y
    refine ⟨(ℓ ^ (K - c)) • a, ?_⟩
    rw [map_nsmul, ha, smul_smul, ← pow_add, Nat.sub_add_cancel hcK]
  obtain ⟨Bp, hperf, hBp⟩ := LAdicPairing.exists_isPerfPair_extendScalars_of_levels
    (LAdicSheaf.geometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F i)
    (LAdicSheaf.geometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F' (2 * d - i))
    ((p ^ q) ^ d) (max c₁ c₂)
    (fun n => (LAdicSheaf.geometricCompactlySupportedCohomologyπ B X ℓ f j kbar F i
      n).hom.toAddMonoidHom)
    (fun n => (LAdicSheaf.geometricCompactlySupportedCohomologyπ B X ℓ f j kbar F'
      (2 * d - i) n).hom.toAddMonoidHom)
    (fun n => (canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f j kbar p q hcard
        ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F n))
          i).hom.toAddMonoidHom)
    (fun n => (canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f j kbar p q hcard
        ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F' n))
          (2 * d - i)).hom.toAddMonoidHom)
    (fun n a => congrArg (fun φ => φ.hom a)
      (LAdicSheaf.geometricCompactlySupportedFrobenius_π B X ℓ f j kbar p q hcard F i n))
    (fun n b => congrArg (fun φ => φ.hom b)
      (LAdicSheaf.geometricCompactlySupportedFrobenius_π B X ℓ f j kbar p q hcard F'
        (2 * d - i) n))
    (fun n => (h₁ n).1) (fun n => (h₂ n).1)
    (fun n => hraise _ c₁ _ (le_max_left _ _) (h₁ n).2)
    (fun n => hraise _ c₂ _ (le_max_right _ _) (h₂ n).2)
    ε hl hr hε
  let B' : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i →ₗ[ℚ_[ℓ]]
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F'
        (2 * d - i) →ₗ[ℚ_[ℓ]] ℚ_[ℓ] := Bp
  have : B'.IsPerfPair := hperf
  have hq : 1 < p ^ q := hcard ▸ Fintype.one_lt_card
  refine isCharpolyPureOfWeight_of_isPerfPair (d := d) hwt hwt' (B := B') (fun v w => ?_) hq
  have h := hBp v w
  rw [zpow_natCast, ← Nat.cast_pow]
  exact h

end Stacks.EtaleCohomology
