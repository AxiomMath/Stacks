module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LAdicFrobeniusLevel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LAdicTowerGram
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveExtWeilPairing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.FrobeniusBaseChangeDegree

/-!
# The Frobenius on `H¹(X_k̄, ℚ_ℓ)` of a curve preserves the Weil pairing up to `q`

Let `X` be a proper scheme over a finite field `k` with `q` elements whose base change `X_k̄` to an
algebraically closed extension is a smooth proper curve, and `ℓ` a prime invertible in `k̄`. On the
level `n` of `H¹(X_k̄, ℤ_ℓ)`, read as `Ext¹_{ℤ/ℓⁿ⁺¹}(ℤ/ℓⁿ⁺¹, ℤ/ℓⁿ⁺¹)` on `X_k̄` with the Frobenius
acting as restriction along `π̄ = π_X × id`
(`Stacks.EtaleCohomology.LAdicSheaf.exists_addEquiv_constantLevel_frobenius`), the Weil pairing
(`Stacks.Picard.exists_extPairing_of_comp_eq`) is left nondegenerate and multiplied by `q`, since
pullback along `π̄` multiplies degrees of line bundles by `q`
(`Stacks.Frobenius.picardDegree_schemePullbackClassHom_geometricFrobeniusBaseChange`).
Given that the levels form a tower looking free,
`Stacks.EtaleCohomology.TowerLimit.exists_isUnit_det_transpose_mul_mul_eq_smul`
turns this into the matrix identity `Aᵀ J A = q J` of [Tag 03V8](https://stacks.math.columbia.edu/tag/03V8)
for the matrix `A` of `π_X^*` on `H¹(X_k̄, ℚ_ℓ)` in any basis.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.exists_levelPairing_constant_one`: the pairings on the levels.
* `Stacks.EtaleCohomology.LAdicSheaf.exists_isUnit_det_transpose_mul_mul_eq_card_smul_of_tower`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius
open scoped Matrix

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
-- the structure projections of `Stacks.Models.RegularModelSituation` are global instances whose
-- conclusions (`Field ?k`, `QuasiCompact ?f`, ...) match every goal and send instance search
-- through `Submodule ?R ?R`; they are irrelevant here
attribute [-instance] Stacks.Models.RegularModelSituation.commRingR
  Stacks.Models.RegularModelSituation.isDomainR
  Stacks.Models.RegularModelSituation.isDiscreteValuationRingR
  Stacks.Models.RegularModelSituation.fieldK Stacks.Models.RegularModelSituation.algebraRK
  Stacks.Models.RegularModelSituation.isFractionRingRK Stacks.Models.RegularModelSituation.fieldk
  Stacks.Models.RegularModelSituation.algebraRk Stacks.Models.RegularModelSituation.isCurve
  Stacks.Models.RegularModelSituation.smooth Stacks.Models.RegularModelSituation.flat
  Stacks.Models.RegularModelSituation.locallyOfFiniteType
  Stacks.Models.RegularModelSituation.quasiCompact

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [IsProper f]
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

local instance : QuasiSeparatedSpace X.obj :=
  @AlgebraicGeometry.IsLocallyNoetherian.quasiSeparatedSpace X.1
    (inferInstance : AlgebraicGeometry.IsNoetherian X.1).toIsLocallyNoetherian

include hcard in
/-- **The levels of `H¹(X_k̄, ℤ_ℓ)` are killed by `ℓⁿ⁺¹`.** -/
theorem LAdicSheaf.pow_smul_constantLevel_eq_zero (i n : ℕ)
    (x : (geometricCompactSupportPadicCohomology B X ℓ f (CompactificationOf.ofProper f) kbar
        (i : ℤ)).obj
      (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)) :
    ((ℓ : ℤ_[ℓ]) ^ (n + 1) : ℤ_[ℓ]) • x = 0 := by
  obtain ⟨Φ, -⟩ := LAdicSheaf.exists_addEquiv_constantLevel_frobenius B X ℓ f kbar p q hcard i n
  apply Φ.injective
  rw [map_zero, show (ℓ : ℤ_[ℓ]) ^ (n + 1) = ((ℓ ^ (n + 1) : ℕ) : ℤ_[ℓ]) by push_cast; rfl,
    Nat.cast_smul_eq_nsmul, map_nsmul]
  exact LevelChange.nsmul_eq_zero_of_nsmul_id (LevelChange.nsmul_id_unitSheaf _) _

variable [IsAlgClosed kbar] [IsCurve kbar (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
  [Smooth (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
  [IsProper (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]

include hcard in
/-- **The levels of `H¹(X_k̄, ℤ_ℓ)` are finite.** -/
theorem LAdicSheaf.finite_constantLevel_one (hℓ : IsUnit (ℓ : kbar)) (n : ℕ) :
    Finite ((geometricCompactSupportPadicCohomology B X ℓ f (CompactificationOf.ofProper f) kbar
      ((1 : ℕ) : ℤ)).obj (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)) := by
  obtain ⟨Φ, -⟩ := LAdicSheaf.exists_addEquiv_constantLevel_frobenius B X ℓ f kbar p q hcard 1 n
  have := Stacks.Picard.finite_ext_one_unitSheaf
    (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) hℓ (n + 1)
  exact Finite.of_equiv _ Φ.symm.toEquiv

/-- **The Weil pairing on the level `n` of `H¹(X_k̄, ℤ_ℓ)`**: left nondegenerate, with values in
`ℤ/ℓⁿ⁺¹`, and multiplied by `q = #k` under the canonical geometric Frobenius. -/
theorem LAdicSheaf.exists_levelPairing_constant_one (hℓ : IsUnit (ℓ : kbar)) (n : ℕ) :
    ∃ e : (geometricCompactSupportPadicCohomology B X ℓ f (CompactificationOf.ofProper f) kbar
          ((1 : ℕ) : ℤ)).obj (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n) →+
        (geometricCompactSupportPadicCohomology B X ℓ f (CompactificationOf.ofProper f) kbar
          ((1 : ℕ) : ℤ)).obj (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n) →+
        ZMod (ℓ ^ (n + 1)),
      (∀ a, (∀ b, e a b = 0) → a = 0) ∧
        ∀ a b, e ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f
            (CompactificationOf.ofProper f) kbar p q hcard ((padicCoefficientComplex B X ℓ).obj
              (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n))
              ((1 : ℕ) : ℤ)).hom a)
          ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f
            (CompactificationOf.ofProper f) kbar p q hcard ((padicCoefficientComplex B X ℓ).obj
              (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n))
              ((1 : ℕ) : ℤ)).hom b) =
          (Fintype.card k : ZMod (ℓ ^ (n + 1))) * e a b := by
  obtain ⟨Φ, hΦ⟩ := LAdicSheaf.exists_addEquiv_constantLevel_frobenius B X ℓ f kbar p q hcard 1 n
  obtain ⟨e, he0, he⟩ := Stacks.Picard.exists_extPairing_of_comp_eq
    (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) hℓ
    (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard)
    (geometricFrobeniusBaseChange_comp_snd (Over.mk f) kbar p q hcard) (Fintype.card k : ℤ)
    (picardDegree_schemePullbackClassHom_geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard)
    (n + 1)
  refine ⟨(e.comp Φ.toAddMonoidHom).compl₂ Φ.toAddMonoidHom, fun a ha => ?_, fun a b => ?_⟩
  · exact Φ.injective ((he0 _ fun b => by
      simpa using ha (Φ.symm b)).trans (map_zero Φ).symm)
  · change e (Φ _) (Φ _) = _ * e (Φ a) (Φ b)
    rw [hΦ, hΦ, he, zsmul_eq_mul, Int.cast_natCast]

/-- **`Aᵀ J A = q J` for the Frobenius on `H¹(X_k̄, ℚ_ℓ)`, given the tower facts.** If the levels of
`H¹(X_k̄, ℤ_ℓ)` have surjective transitions with kernels `ℓⁿ⁺¹ H(n+1)`, and their `ℓᵏ⁺¹`-torsion is
divisible by `ℓⁿ⁺¹`, then every basis of `H¹(X_k̄, ℚ_ℓ)` gives a matrix `J` with unit determinant
and `Aᵀ J A = q J`, `A` the matrix of `π_X^*`. -/
theorem LAdicSheaf.exists_isUnit_det_transpose_mul_mul_eq_card_smul_of_tower
    (hℓ : IsUnit (ℓ : kbar))
    (hsurj : ∀ n, Function.Surjective (TowerLimit.tr
      (LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f
        (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ) ((1 : ℕ) : ℤ))
      (Nat.le_succ n)))
    (hker : ∀ n (x : (LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f
        (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ) ((1 : ℕ) : ℤ)).obj
          (op (n + 1))),
      TowerLimit.tr _ (Nat.le_succ n) x = 0 → ∃ y, x = ((ℓ : ℤ_[ℓ]) ^ (n + 1) : ℤ_[ℓ]) • y)
    (htors : ∀ n k' (x : (LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f
        (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ) ((1 : ℕ) : ℤ)).obj
          (op (n + k' + 1))),
      ((ℓ : ℤ_[ℓ]) ^ (k' + 1) : ℤ_[ℓ]) • x = 0 → ∃ y, x = ((ℓ : ℤ_[ℓ]) ^ (n + 1) : ℤ_[ℓ]) • y)
    {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    (bV : Module.Basis ι' ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
      (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ) ((1 : ℕ) : ℤ))) :
    ∃ J : Matrix ι' ι' ℚ_[ℓ], IsUnit J.det ∧
      (LinearMap.toMatrix bV bV (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
          (CompactificationOf.ofProper f) kbar p q hcard (LAdicSheaf.constantSystem B X ℓ)
            ((1 : ℕ) : ℤ)).hom)ᵀ * J *
        LinearMap.toMatrix bV bV (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
          (CompactificationOf.ofProper f) kbar p q hcard (LAdicSheaf.constantSystem B X ℓ)
            ((1 : ℕ) : ℤ)).hom =
      (Fintype.card k : ℚ_[ℓ]) • J :=
  TowerLimit.exists_isUnit_det_transpose_mul_mul_eq_smul
    (fun n x => LAdicSheaf.pow_smul_constantLevel_eq_zero B X ℓ f kbar p q hcard 1 n x)
    hsurj hker htors (fun n => LAdicSheaf.finite_constantLevel_one B X ℓ f kbar p q hcard hℓ n)
    (LAdicSheaf.geometricCompactlySupportedFrobenius B X ℓ f (CompactificationOf.ofProper f) kbar
      p q hcard (LAdicSheaf.constantSystem B X ℓ) ((1 : ℕ) : ℤ))
    (fun n => (canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f
      (CompactificationOf.ofProper f) kbar p q hcard ((padicCoefficientComplex B X ℓ).obj
        (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)) ((1 : ℕ) : ℤ)).hom)
    (fun n x => congrArg (fun g => g.hom x)
      (LAdicSheaf.geometricCompactlySupportedFrobenius_π B X ℓ f (CompactificationOf.ofProper f)
        kbar p q hcard (LAdicSheaf.constantSystem B X ℓ) ((1 : ℕ) : ℤ) n))
    (Fintype.card k)
    (fun n => LAdicSheaf.exists_levelPairing_constant_one B X ℓ f kbar p q hcard hℓ n)
    bV

end Stacks.EtaleCohomology

end
