module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantCurveCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantCurvePointCount
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantCurveFrobeniusGram
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LAdicTowerTrace
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionSmoothProjectiveCurve.Unconditional
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The traces of the Frobenius on `H¹(X_k̄, ℚ_ℓ)` of a curve, and its dimension

Let `X` be a proper scheme over a finite field `k` with `q` elements, `k̄` an algebraic closure
of `k` such that `X_k̄` is a smooth proper curve, and `ℓ` a prime invertible in `k̄`. Write
`M = H¹(X_k̄, ℤ_ℓ)`, `V = H¹(X_k̄, ℚ_ℓ) = M ⊗ ℚ_ℓ` and `π_X^*` for the geometric Frobenius.

* The levels of `M` are `Pic(X_k̄)[ℓⁿ⁺¹]` with `(π_X^*)^m` acting as pullback along `π̄^m`
  (`Stacks.EtaleCohomology.LAdicSheaf.exists_addEquiv_constantLevel_one_torsionBy`), so
  Weil's formula (`Stacks.EtaleCohomology.natCast_natCard_fixedSections_geometricFrobeniusBaseChangePow`)
  and the trace on the limit of the tower
  (`Stacks.EtaleCohomology.TowerLimit.trace_toZModLinearMap_eq_toZModPow_trace`) give
  `#Fix(π̄^m) = 1 - Tr((π_X^*)^m | M) + q^m` in `ℤ_ℓ`, hence in `ℚ_ℓ` on `V`
  (`Stacks.EtaleCohomology.LAdicSheaf.natCast_natCard_fixedSections_eq_one_sub_trace_rationalFrobenius_pow_add`).
* `dim V = 2g`, `g` the genus of `X_k̄`: `#M/ℓM = #Pic(X_k̄)[ℓ] = ℓ^{2g}` by
  [Stacks, Tag 0C1Z] (`Stacks.EtaleCohomology.LAdicSheaf.finrank_rationalGeometricCompactlySupportedCohomology_constant_one`).

These are the trace identity and the rank used in the proof of [Stacks, Tag 03V8], obtained
from Weil's formula rather than from the trace formula of Tag 03V2.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

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
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [IsProper f]
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)
  [IsAlgClosed kbar] [IsCurve kbar (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
  [Smooth (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
  [IsProper (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]

local instance : QuasiSeparatedSpace X.obj :=
  @AlgebraicGeometry.IsLocallyNoetherian.quasiSeparatedSpace X.1
    (inferInstance : AlgebraicGeometry.IsNoetherian X.1).toIsLocallyNoetherian

/-- **The tower `n ↦ H¹(X_k̄, ℤ/ℓⁿ⁺¹)` of a curve looks free**: its transitions are onto with
kernel `ℓⁿ⁺¹`, and its `ℓᵏ⁺¹`-torsion is divisible by `ℓⁿ⁺¹`. -/
theorem LAdicSheaf.towerFacts_constant_one (hℓ : IsUnit (ℓ : kbar)) :
    (∀ n, Function.Surjective (TowerLimit.tr
      (LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f
        (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ) ((1 : ℕ) : ℤ))
      (Nat.le_succ n))) ∧
    (∀ n (x : (LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f
        (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ) ((1 : ℕ) : ℤ)).obj
          (op (n + 1))),
      TowerLimit.tr _ (Nat.le_succ n) x = 0 → ∃ y, x = ((ℓ : ℤ_[ℓ]) ^ (n + 1) : ℤ_[ℓ]) • y) ∧
    (∀ n k' (x : (LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f
        (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ) ((1 : ℕ) : ℤ)).obj
          (op (n + k' + 1))),
      ((ℓ : ℤ_[ℓ]) ^ (k' + 1) : ℤ_[ℓ]) • x = 0 → ∃ y, x = ((ℓ : ℤ_[ℓ]) ^ (n + 1) : ℤ_[ℓ]) • y) := by
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
  exact ⟨TowerLimit.surjective_tr_of_ext (F := T)
      (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) hℓ Φ h ψ' hsq,
    TowerLimit.exists_eq_smul_of_tr_eq_zero_of_ext (F := T)
      (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) hℓ Φ h ψ' hsq,
    TowerLimit.exists_eq_smul_of_smul_eq_zero_of_ext (F := T)
      (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) hℓ Φ⟩

include hcard in
/-- `H¹(X_k̄, ℤ_ℓ)` of a curve is a free `ℤ_ℓ`-module of finite rank. -/
theorem LAdicSheaf.free_finite_constant_one (hℓ : IsUnit (ℓ : kbar)) :
    Module.Free ℤ_[ℓ] (LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f
        (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ) ((1 : ℕ) : ℤ)) ∧
      Module.Finite ℤ_[ℓ] (LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f
        (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ) ((1 : ℕ) : ℤ)) := by
  obtain ⟨hsurj, hker, htors⟩ := LAdicSheaf.towerFacts_constant_one B X ℓ f kbar hℓ
  have hkill := fun n => LAdicSheaf.pow_smul_constantLevel_eq_zero B X ℓ f kbar p q hcard 1 n
  have hfin := fun n => LAdicSheaf.finite_constantLevel_one B X ℓ f kbar p q hcard hℓ n
  exact ⟨TowerLimit.free hkill hsurj hker htors hfin, TowerLimit.finite hkill hsurj hker htors hfin⟩

/-- Pullback of line bundles along `π̄^m` is the `m`-th iterate of pullback along `π̄`, on the
`c`-torsion. -/
theorem torsionByRestrict_geometricFrobeniusBaseChangePow {k : Type u} [Field k] [Fintype k]
    (Y : Over (Spec (.of k))) (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ)
    [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q) (c : ℤ) (m : ℕ)
    (y : Submodule.torsionBy ℤ (Stacks.Picard.ofScheme (fieldBaseChange Y kbar)) c) :
    (Stacks.Picard.torsionByRestrict (A := Stacks.Picard.ofScheme (fieldBaseChange Y kbar))
        (Stacks.Picard.schemePullbackClassHom (geometricFrobeniusBaseChange Y kbar p q hcard)) c)^[m]
        y =
      Stacks.Picard.torsionByRestrict (A := Stacks.Picard.ofScheme (fieldBaseChange Y kbar))
        (Stacks.Picard.schemePullbackClassHom (geometricFrobeniusBaseChangePow Y kbar p q hcard m))
        c y := by
  induction m with
  | zero =>
      refine Subtype.ext ?_
      rw [Function.iterate_zero_apply, Stacks.Picard.torsionByRestrict_apply]
      exact (Stacks.Picard.schemePullbackClass_id _ _).symm
  | succ m ih =>
      refine Subtype.ext ?_
      rw [Function.iterate_succ_apply', ih, Stacks.Picard.torsionByRestrict_apply,
        Stacks.Picard.torsionByRestrict_apply, Stacks.Picard.torsionByRestrict_apply,
        geometricFrobeniusBaseChangePow_succ]
      exact Stacks.Picard.schemePullbackClass_comp _ _ _

variable [Algebra.IsAlgebraic k kbar]

include hcard in
/-- **The Lefschetz identity for the powers of the Frobenius on `H¹(X_k̄, ℤ_ℓ)` of a curve**:
`#Fix(π̄^m) = 1 - Tr((π_X^*)^m | H¹(X_k̄, ℤ_ℓ)) + q^m` for `m ≥ 1`. Modulo `ℓⁿ⁺¹` this is Weil's
formula on `Pic(X_k̄)[ℓⁿ⁺¹]`, the level `n` of `H¹(X_k̄, ℤ_ℓ)`. -/
@[sga "5 IIIB 1.3.1" "special case"]
theorem LAdicSheaf.natCast_natCard_fixedSections_eq_one_sub_trace_pow_add
    (hℓ : IsUnit (ℓ : kbar)) (m : ℕ) (hm : m ≠ 0) :
    ((Nat.card (fixedSections (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))
        (geometricFrobeniusBaseChangePow (Over.mk f) kbar p q hcard m)) : ℕ) : ℤ_[ℓ]) =
      1 - LinearMap.trace ℤ_[ℓ] _
          ((LAdicSheaf.geometricCompactlySupportedFrobenius B X ℓ f (CompactificationOf.ofProper f)
            kbar p q hcard (LAdicSheaf.constantSystem B X ℓ) ((1 : ℕ) : ℤ)).hom ^ m) +
        (Fintype.card k : ℤ_[ℓ]) ^ m := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  obtain ⟨hsurj, hker, htors⟩ := LAdicSheaf.towerFacts_constant_one B X ℓ f kbar hℓ
  have hkill := fun n => LAdicSheaf.pow_smul_constantLevel_eq_zero B X ℓ f kbar p q hcard 1 n
  have hfin := fun n => LAdicSheaf.finite_constantLevel_one B X ℓ f kbar p q hcard hℓ n
  set φ := LAdicSheaf.geometricCompactlySupportedFrobenius B X ℓ f (CompactificationOf.ofProper f)
    kbar p q hcard (LAdicSheaf.constantSystem B X ℓ) ((1 : ℕ) : ℤ) with hφ
  set N := Nat.card (fixedSections (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))
    (geometricFrobeniusBaseChangePow (Over.mk f) kbar p q hcard m))
  rw [← sub_eq_zero]
  refine PadicInt.ext_of_toZModPow.1 fun n => ?_
  rcases n with _ | n
  · exact @Subsingleton.elim (ZMod 1) (ZMod.subsingleton_iff.2 rfl) _ _
  rw [map_zero]
  obtain ⟨e, he⟩ := LAdicSheaf.exists_addEquiv_constantLevel_one_torsionBy B X ℓ f kbar p q hcard hℓ n
  -- `(π_X^*)^m` on the level `n` is pullback along `π̄^m`
  have hπ : ∀ x : ↑(LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f
      (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ) ((1 : ℕ) : ℤ)),
      (LAdicSheaf.geometricCompactlySupportedCohomologyπ B X ℓ f (CompactificationOf.ofProper f)
        kbar (LAdicSheaf.constantSystem B X ℓ) ((1 : ℕ) : ℤ) n).hom (φ.hom x) =
      (canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f (CompactificationOf.ofProper f)
          kbar p q hcard ((padicCoefficientComplex B X ℓ).obj
            (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)) ((1 : ℕ) : ℤ)).hom
        ((LAdicSheaf.geometricCompactlySupportedCohomologyπ B X ℓ f (CompactificationOf.ofProper f)
          kbar (LAdicSheaf.constantSystem B X ℓ) ((1 : ℕ) : ℤ) n).hom x) := fun x =>
    congrArg (fun g => g.hom x) (LAdicSheaf.geometricCompactlySupportedFrobenius_π B X ℓ f
      (CompactificationOf.ofProper f) kbar p q hcard (LAdicSheaf.constantSystem B X ℓ)
      ((1 : ℕ) : ℤ) n)
  have hσ : ∀ x, e.symm (Stacks.Picard.torsionByRestrict
        (A := Stacks.Picard.ofScheme (fieldBaseChange (Over.mk f) kbar))
        (Stacks.Picard.schemePullbackClassHom
        (geometricFrobeniusBaseChangePow (Over.mk f) kbar p q hcard m)) ((ℓ : ℤ) ^ (n + 1))
        (e ((LAdicSheaf.geometricCompactlySupportedCohomologyπ B X ℓ f
          (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ)
            ((1 : ℕ) : ℤ) n).hom x))) =
      (LAdicSheaf.geometricCompactlySupportedCohomologyπ B X ℓ f (CompactificationOf.ofProper f)
        kbar (LAdicSheaf.constantSystem B X ℓ) ((1 : ℕ) : ℤ) n).hom ((φ.hom ^ m) x) := by
    intro x
    rw [Module.End.pow_apply, (Function.Semiconj.iterate_right hπ m) x, e.symm_apply_eq]
    exact ((Function.Semiconj.iterate_right he m _).trans
      (torsionByRestrict_geometricFrobeniusBaseChangePow (Over.mk f) kbar p q hcard _ m _)).symm
  have htr := TowerLimit.trace_toZModLinearMap_eq_toZModPow_trace hkill hsurj hker htors hfin
    (ModuleCat.ofHom (φ.hom ^ m)) n e.symm _ hσ
  have hW := natCast_natCard_fixedSections_geometricFrobeniusBaseChangePow (Over.mk f) kbar p q
    hcard m hm ℓ hℓ.ne_zero (n + 1) (by omega)
  rw [show picardTorsionTrace (fieldBaseChange (Over.mk f) kbar)
      (Stacks.Picard.schemePullbackClassHom
        (geometricFrobeniusBaseChangePow (Over.mk f) kbar p q hcard m)) ℓ (n + 1) =
      PadicInt.toZModPow (n + 1) (LinearMap.trace ℤ_[ℓ] _ (φ.hom ^ m)) from htr] at hW
  rw [map_sub, map_add, map_sub, map_one, map_pow (PadicInt.toZModPow (n + 1)), map_natCast,
    map_natCast]
  rw [Int.cast_natCast] at hW
  rw [hW]
  push_cast
  ring

include hcard in
/-- **The trace of `(π_X^*)^m` on `H¹(X_k̄, ℚ_ℓ)` is that on `H¹(X_k̄, ℤ_ℓ)`**, the latter being
free of finite rank. -/
theorem LAdicSheaf.trace_rationalFrobenius_pow_constant_one (hℓ : IsUnit (ℓ : kbar)) (m : ℕ) :
    LinearMap.trace ℚ_[ℓ] _
        ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
          (CompactificationOf.ofProper f) kbar p q hcard (LAdicSheaf.constantSystem B X ℓ)
            ((1 : ℕ) : ℤ)).hom ^ m) =
      algebraMap ℤ_[ℓ] ℚ_[ℓ] (LinearMap.trace ℤ_[ℓ] _
        ((LAdicSheaf.geometricCompactlySupportedFrobenius B X ℓ f (CompactificationOf.ofProper f)
          kbar p q hcard (LAdicSheaf.constantSystem B X ℓ) ((1 : ℕ) : ℤ)).hom ^ m)) := by
  obtain ⟨h1, h2⟩ := LAdicSheaf.free_finite_constant_one B X ℓ f kbar p q hcard hℓ
  change LinearMap.trace ℚ_[ℓ] _
      (((LAdicSheaf.geometricCompactlySupportedFrobenius B X ℓ f (CompactificationOf.ofProper f)
        kbar p q hcard (LAdicSheaf.constantSystem B X ℓ) ((1 : ℕ) : ℤ)).hom.baseChange ℚ_[ℓ]) ^ m) = _
  rw [← LinearMap.baseChange_pow, LinearMap.trace_baseChange]

include hcard in
/-- **`dim H¹(X_k̄, ℚ_ℓ) = 2g`** for a smooth proper curve `X_k̄` of genus `g`: the rank `r` of
`H¹(X_k̄, ℤ_ℓ)` satisfies `ℓ^r = #H¹(X_k̄, ℤ/ℓ) = #Pic(X_k̄)[ℓ] = ℓ^{2g}` ([Stacks, Tag 0C1Z]). -/
theorem LAdicSheaf.finrank_rationalGeometricCompactlySupportedCohomology_constant_one
    (hℓ : IsUnit (ℓ : kbar)) :
    Module.finrank ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
        (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ) ((1 : ℕ) : ℤ)) =
      2 * genus (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  haveI : IsProjectiveVariety kbar (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) :=
    { isProjective := isProjectiveMorphism_of_isProper_of_isCurve kbar _ }
  obtain ⟨hsurj, hker, htors⟩ := LAdicSheaf.towerFacts_constant_one B X ℓ f kbar hℓ
  have hkill := fun n => LAdicSheaf.pow_smul_constantLevel_eq_zero B X ℓ f kbar p q hcard 1 n
  have hfin := fun n => LAdicSheaf.finite_constantLevel_one B X ℓ f kbar p q hcard hℓ n
  have h0 := TowerLimit.natCard_obj_zero hkill hsurj hker htors hfin
  obtain ⟨e, -⟩ := LAdicSheaf.exists_addEquiv_constantLevel_one_torsionBy B X ℓ f kbar p q hcard hℓ 0
  obtain ⟨E⟩ := Stacks.Picard.nonempty_torsionBy_addEquiv_pi_zmod_of_smoothProjectiveCurve kbar
    (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) ℓ (Fact.out : ℓ.Prime).one_lt.le hℓ
  have hP : Nat.card (Submodule.torsionBy ℤ
      (Stacks.Picard.ofScheme (fieldBaseChange (Over.mk f) kbar)) ((ℓ : ℤ) ^ (0 + 1))) =
      ℓ ^ (2 * genus (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))) := by
    rw [zero_add, pow_one, Nat.card_congr E.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  rw [← Nat.card_congr e.toEquiv] at hP
  obtain ⟨h1, -⟩ := LAdicSheaf.free_finite_constant_one B X ℓ f kbar p q hcard hℓ
  change Module.finrank ℚ_[ℓ] (TensorProduct ℤ_[ℓ] ℚ_[ℓ] _) = _
  rw [Module.finrank_baseChange]
  exact Nat.pow_right_injective (Fact.out : ℓ.Prime).two_le (h0.symm.trans hP)

end Stacks.EtaleCohomology

end
