module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicPointTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTorsionFree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LFunctionRationalSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.FlatStalkTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicVanishingInputs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The trace formula for a `ℚ_ℓ`-sheaf from the trace formula at finite level

The trace formula of [Stacks, Tag 03V2] for an ℓ-adic sheaf `F = F' ⊗ ℚ_ℓ`, with `F'` its
torsion-free model, from the trace formula of [Stacks, Tag 03V3] for the levels `F'ₙ`: if the
complexes `Kₙ = RΓ_c(X_k̄, F'ₙ)` are perfect and satisfy the trace formula at every level, then the
alternating trace of `π_X^*` on `Hⁱ_c(X_k̄, F)` is the sum, over the closed points of degree one,
of the traces of the geometric Frobenius on the rational stalks of `F`.

## Main results

* `LAdicSheaf.isPerfect_rationalPointStalkComplex_torsionFreeModel`: the local terms are defined.
* `LAdicSheaf.alternating_trace_eq_sum_rationalStalkFrobenius_of_levelTraceFormula`: the trace
  formula for `F`, from the level-wise trace formula for the tower of the model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale
open Stacks.Frobenius Stacks.InverseSystem CategoryTheory.FilteredDerived Stacks.Trace

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
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
  [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p]
  (hcard : Fintype.card k = p ^ q)

/-- The torsion-free model `F'` of an ℓ-adic sheaf, `ℓᴺ F` for `N` its torsion bound. -/
local notation "model" F => LAdicSheaf.torsionFreeModel F (LAdicSheaf.torsionBound F)

omit [IsAlgClosed kbar] [CharP kbar p] in
include p q hcard in
/-- **`Hⁱ_c(X_k̄, F ⊗ Q_ℓ)` vanishes above `b`** as soon as the complexes `RΓ_c(X_k̄, F'ₙ)` of the
levels of the torsion-free model are perfect and the reductions modulo `ℓ` of those levels have
cohomology on `X̄_k̄` vanishing above `b`. -/
theorem LAdicSheaf.isZero_rationalGeometricCompactlySupportedCohomology_of_perfect_of_reduction
    (F : LAdicSheaf B X ℓ)
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ (model F) n)))) (b : ℤ)
    (hb : (∀ n i, b < i → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod ℓ)) i).obj
      (derivedDirectImageSections (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
        (ZMod ℓ) ((etaleModuleCoextendScalars (torsionCoeff ℓ (n + 1)) _).obj
          ((etaleModuleInverseImage.{u, 0} _ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} _ j.immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ (model F) n))))))))
    (i : ℤ) (hi : b < i) :
    IsZero (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i) := by
  let M := model F
  have hM := LAdicSheaf.powExact_etaleLevel_torsionFreeModel B X ℓ F
    (le_refl (LAdicSheaf.torsionBound F))
  have hlev : ∀ n : ℕ, IsZero
      ((LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar M i).obj
        (Opposite.op n)) := fun n => by
    have h := isZero_homology_compactSupportFrobeniusCohomology_single_of_reduction f j kbar ℓ
      (n + 1) (LAdicSheaf.etaleLevel B X ℓ M n) (hM n) b (hb n) i hi
    have hs := ModuleCat.subsingleton_of_isZero h
    have h' : IsZero ((levelCohomologySystem
        (LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard M hM hP) i).obj
          (Opposite.op n)) := @ModuleCat.isZero_of_subsingleton _ _ _ hs
    exact h'.of_iso (LAdicSheaf.geometricLevelCohomologyIso B X ℓ f j kbar p q hcard M hM hP i n)
  have hlim : IsZero (LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar M i) := by
    rw [IsZero.iff_id_eq_zero]
    exact limit.hom_ext fun n => (hlev n.unop).eq_of_tgt _ _
  have hrat :
      IsZero (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar M i) :=
    (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map_isZero hlim
  exact hrat.of_iso (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso B X ℓ f j
    kbar (LAdicSheaf.toTorsionFreeModel F (LAdicSheaf.torsionBound F))
    (LAdicSheaf.fromTorsionFreeModel F (LAdicSheaf.torsionBound F)) (LAdicSheaf.torsionBound F)
    (LAdicSheaf.toTorsionFreeModel_comp_fromTorsionFreeModel F (LAdicSheaf.torsionBound F))
    (LAdicSheaf.fromTorsionFreeModel_comp_toTorsionFreeModel F (LAdicSheaf.torsionBound F)) i)

omit [CharP kbar p] in
include p q hcard in
/-- **`Hⁱ_c(X_k̄, F ⊗ Q_ℓ)` vanishes above `2n`** when the base change `X̄_k̄` of the
compactification has dimension at most `n`, given the perfectness of the complexes
`RΓ_c(X_k̄, F'ₙ)` of the torsion-free model and the absolute case of [Stacks, Tag 095U] over the
separably closed field `k̄` (`ProperSeparablyClosedVanishingStatement`), applied to the reductions
modulo `ℓ` of the levels of the model on `X̄_k̄`. -/
theorem LAdicSheaf.isZero_rationalGeometricCompactlySupportedCohomology_of_dim_le
    (h095U : ProperSeparablyClosedVanishingStatement.{u}) (F : LAdicSheaf B X ℓ)
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ (model F) n)))) (d : ℕ)
    (hdim : topologicalKrullDim
      (pullback (Over.mk j.toBase).hom (specAlgebraMap k kbar) : Scheme.{u}) ≤ d)
    (i : ℤ) (hi : 2 * (d : ℤ) < i) :
    IsZero (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have : IsProper (Over.mk j.toBase).hom := j.property.2
  exact LAdicSheaf.isZero_rationalGeometricCompactlySupportedCohomology_of_perfect_of_reduction
    B X ℓ f j kbar p q hcard F hP (2 * d) (fun n i' hi' => h095U kbar _ d hdim ℓ _ i' hi') i hi

omit [Fintype k] [AlgebraicGeometry.IsNoetherian X.1] [QuasiCompact f] [IsSeparated f] in
/-- The closed point of degree one hit by a rational point has finite residue field. -/
theorem finite_residueField_rationalPoint [Finite k] (y : rationalPoints f) :
    Finite (X.1.residueField (rationalPointsEquivDegreeOne f y).1.1) :=
  finite_residueField f _ (rationalPointsEquivDegreeOne f y).1.2

/-- The level-`n` stalk of the torsion-free model at the geometric point at a closed point is
finite free over `ℤ/ℓⁿ⁺¹ℤ`: it has a basis, lifted level by level from the level-`0` stalk. -/
theorem LAdicSheaf.free_finite_finiteLevelStalk_torsionFreeModel (F : LAdicSheaf.{u, u + 1} B X ℓ)
    (x : X.1) (n : ℕ) :
    Module.Free (ZMod (ℓ ^ (n + 1))) (finiteLevelStalk B X ℓ (model F) (geometricPointAt X.1 x) n) ∧
      Module.Finite (ZMod (ℓ ^ (n + 1)))
        (finiteLevelStalk B X ℓ (model F) (geometricPointAt X.1 x) n) := by
  let b := LAdicSheaf.flatLevelBasis (model F) (geometricPointAt X.1 x)
    (fun m => LAdicSheaf.isPowExact_finiteLevelStalk _ _ m
      (LAdicSheaf.powExact_torsionFreeModel_level F le_rfl m)) n
  exact ⟨Module.Free.of_basis b, Module.Finite.of_basis b⟩

omit [Fintype k] [QuasiCompact f] [IsSeparated f] in
/-- **The stalk complexes of the levels of the torsion-free model at the rational points are
perfect**: the stalk there is isomorphic to the finite-level stalk at the closed point it hits,
which is finite free. -/
theorem LAdicSheaf.isPerfect_rationalPointStalkComplex_torsionFreeModel [Finite k]
    (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) (y : rationalPoints f) :
    StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, 0} (ZMod (ℓ ^ (n + 1))) kbar y.1
        (LAdicSheaf.levelComplex B X ℓ (model F) n))) := by
  have := finite_residueField_rationalPoint B X f y
  obtain ⟨hfree, hfin⟩ := LAdicSheaf.free_finite_finiteLevelStalk_torsionFreeModel B X ℓ F
    (rationalPointsEquivDegreeOne f y).1.1 n
  let e := finiteLevelStalkRationalPointIso B X ℓ (rationalPointsEquivDegreeOne f y).1.1 kbar
    (model F) n y.1 (rationalGeometricPointHom kbar y.1)
  have := Module.Free.of_equiv e.toLinearEquiv
  have := Module.Finite.equiv e.toLinearEquiv
  exact isPerfect_rationalPointStalkComplex_single kbar _ y.1 _

/-- **The trace formula for a `ℚ_ℓ`-sheaf, from the trace formula at finite level.**  Let `F` be an
ℓ-adic sheaf on a separated scheme `X` of finite type over a finite field `k`, with torsion-free
model `F'`, and suppose that the complexes `Kₙ = RΓ_c(X_k̄, F'ₙ)` are perfect and satisfy the trace
formula of [Stacks, Tag 03V3]: the trace of `π_X^*` on `Kₙ` is the sum over `X(k)` of the traces
of the geometric Frobenius on the stalks of `F'ₙ`.  Then

`∑ᵢ (-1)ⁱ Tr(π_X^* | Hⁱ_c(X_k̄, F)) = ∑_{x closed, deg x = 1} Tr(π_x | F_x̄)`. -/
@[sga "4½ Rapport 4.13" "partial"]
theorem LAdicSheaf.alternating_trace_eq_sum_rationalStalkFrobenius_of_levelTraceFormula
    (F : LAdicSheaf.{u, u + 1} B X ℓ)
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ (model F) n))))
    [Fintype (rationalPoints f)]
    (hT : ∀ n, traceAtLevel (LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard (model F)
        (LAdicSheaf.powExact_etaleLevel_torsionFreeModel B X ℓ F le_rfl) hP) n =
      ∑ y : rationalPoints f, commutativeAdditiveCommutatorQuotientEval (ZMod (ℓ ^ (n + 1)))
        (perfectDerivedTrace (ZMod (ℓ ^ (n + 1))) ⟨_,
          LAdicSheaf.isPerfect_rationalPointStalkComplex_torsionFreeModel B X ℓ f kbar F n y⟩
          (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} (ZMod (ℓ ^ (n + 1))) kbar p q
            hcard y.1 (LAdicSheaf.levelComplex B X ℓ (model F) n))))) :
    ∑ᶠ i : ℤ, (if Even i then (1 : ℚ_[ℓ]) else -1) *
        LinearMap.trace ℚ_[ℓ]
          (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)
          (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyPullback B X ℓ f j kbar F i
            (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard)).hom =
      ∑ᶠ (x : closedPoints X.1) (_ : residueDegree f x.1 = 1),
        LinearMap.trace ℚ_[ℓ] _
          (LAdicSheaf.rationalStalkFrobenius B X ℓ F x.1 (finite_residueField f x.1 x.2)) := by
  rw [LAdicSheaf.alternating_trace_rationalGeometricCompactlySupportedFrobenius_of_perfect B X ℓ f j
    kbar p q hcard F hP, finsum_residueDegree_eq_one_eq_sum f]
  have hex := fun y : rationalPoints f =>
    have := finite_residueField_rationalPoint B X f y
    LAdicSheaf.exists_trace_rationalStalkEnd_torsionFreeModel F
      (frobeniusPointHom X.1 (rationalPointsEquivDegreeOne f y).1.1)
  choose t ht htn using hex
  have hpadic : padicTrace (LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard (model F)
      (LAdicSheaf.powExact_etaleLevel_torsionFreeModel B X ℓ F le_rfl) hP) = ∑ y, t y := by
    refine eq_of_toZModPow_succ_eq fun n => ?_
    rw [toZModPow_padicTrace, hT n, map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have := finite_residueField_rationalPoint B X f y
    obtain ⟨hfree, hfin⟩ := LAdicSheaf.free_finite_finiteLevelStalk_torsionFreeModel B X ℓ F
      (rationalPointsEquivDegreeOne f y).1.1 n
    rw [htn y n]
    exact (trace_finiteLevelStalkEnd_eq_eval_localTerm B X ℓ (rationalPointsEquivDegreeOne f y).1.1
      kbar p q hcard f (model F) n y.1 rfl
      (rationalPointsEquivDegreeOne f y).2 _).symm
  rw [hpadic, PadicInt.coe_sum]
  exact Finset.sum_congr rfl fun y _ => (ht y).symm

end Stacks.EtaleCohomology
