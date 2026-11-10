module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LAdicCurveGram
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveExtTowerLimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantLevelExtComparison

/-!
# The Frobenius of a curve on `H¹(X_k̄, ℚ_ℓ)` is a similitude of a nondegenerate form

Let `X` be a proper scheme over a finite field `k` with `q` elements whose base change `X_k̄` to
an algebraic closure is a smooth proper curve, and `ℓ` a prime invertible in `k̄`.  For every basis
of `H¹(X_k̄, ℚ_ℓ)` the matrix `A` of `π_X^*` satisfies `Aᵀ J A = q J` for a matrix `J` with unit
determinant (`Stacks.EtaleCohomology.LAdicSheaf.exists_isUnit_det_transpose_mul_mul_eq_card_smul`).

This is `LAdicSheaf.exists_isUnit_det_transpose_mul_mul_eq_card_smul_of_tower` with its three tower
facts proved: the levels `Hⁱ_c(X_k̄, (ℤ_ℓ)ₙ)` are `Ext¹(ℤ/ℓⁿ⁺¹, ℤ/ℓⁿ⁺¹)` on `X_k̄`
(`LAdicSheaf.constantLevelCohomologyAddEquiv`), the transitions are, up to an automorphism of
`ℤ/ℓⁿ⁺¹`, the change of level on `Ext¹` (`LAdicSheaf.exists_constantLevelCohomology_transition`),
and on a curve these have the properties of the levels of a free `ℤ_ℓ`-module
(`TowerLimit.surjective_tr_of_ext` and its companions).  The pairing is the Weil pairing on the
levels; `J` is its Gram matrix.  By `norm_curveEigenvalue_eq_sqrt` this gives `|α_i| = √q` for the
eigenvalues of `π_X^*` on `H¹`, hence part (4) of [Tag 03V8](https://stacks.math.columbia.edu/tag/03V8).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius
open scoped Matrix

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
-- the structure projections of `Stacks.Models.RegularModelSituation` are global instances whose
-- conclusions match every goal and send instance search astray; they are irrelevant here
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
  [IsAlgClosed kbar] [IsCurve kbar (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
  [Smooth (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
  [IsProper (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]

local instance : QuasiSeparatedSpace X.obj :=
  @AlgebraicGeometry.IsLocallyNoetherian.quasiSeparatedSpace X.1
    (inferInstance : AlgebraicGeometry.IsNoetherian X.1).toIsLocallyNoetherian

/-- **`Aᵀ J A = q J` for the Frobenius on `H¹(X_k̄, ℚ_ℓ)` of a curve.** For `X` proper over a
finite field `k` with `X_k̄` a smooth proper curve and `ℓ` invertible in `k̄`, every basis of
`H¹(X_k̄, ℚ_ℓ)` gives a matrix `J` with unit determinant and `Aᵀ J A = #k · J`, `A` the matrix of
`π_X^*`. -/
theorem LAdicSheaf.exists_isUnit_det_transpose_mul_mul_eq_card_smul (hℓ : IsUnit (ℓ : kbar))
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
      (Fintype.card k : ℚ_[ℓ]) • J := by
  have h : ∀ n, ℓ ^ (n + 1) ∣ ℓ ^ (n + 1 + 1) := fun n => pow_dvd_pow ℓ (by omega)
  choose ψ hψ using fun n => LAdicSheaf.exists_constantLevelCohomology_transition B X ℓ f kbar 1 n
  let Φ := fun n => LAdicSheaf.constantLevelCohomologyAddEquiv B X ℓ f kbar 1 n
  let ψ' : ∀ n, (LevelChange.restrict (fieldBaseChange (Over.mk f) kbar) (h n)).obj
      (ExtensionTorsor.unitSheaf (ℓ ^ (n + 1))) ≅
      (LevelChange.restrict (fieldBaseChange (Over.mk f) kbar) (h n)).obj
      (ExtensionTorsor.unitSheaf (ℓ ^ (n + 1))) := fun n =>
    (LevelChange.restrict _ (h n)).mapIso (ψ n)
  let T := LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f
    (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ) ((1 : ℕ) : ℤ)
  have hsq : ∀ n x, LevelChange.extMap _ (h n) (ExtensionTorsor.unitSheaf (ℓ ^ (n + 1))) 1
      (Φ n (TowerLimit.tr T (Nat.le_succ n) x)) =
      (Φ (n + 1) x).comp (Ext.mk₀ (LevelChange.reduction _ (h n) ≫ (ψ' n).hom)) (add_zero 1) :=
    fun n x => by
      have e := hψ n
      have hx : TowerLimit.tr T (Nat.le_succ n) x = (T.map (homOfLE (n.le_add_right 1)).op).hom x :=
        rfl
      rw [hx]
      convert e x using 2
      rfl
  exact LAdicSheaf.exists_isUnit_det_transpose_mul_mul_eq_card_smul_of_tower B X ℓ f kbar p q hcard
    hℓ (TowerLimit.surjective_tr_of_ext (F := T)
      (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) hℓ Φ h ψ' hsq)
    (TowerLimit.exists_eq_smul_of_tr_eq_zero_of_ext (F := T)
      (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) hℓ Φ h ψ' hsq)
    (TowerLimit.exists_eq_smul_of_smul_eq_zero_of_ext (F := T)
      (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) hℓ Φ) bV

end Stacks.EtaleCohomology

end
