module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTraceFormulaConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTraceFormulaOfCore
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatOfFlatStalks
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.FlatStalkTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTheorem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportPerfectCurveFinite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DimensionZeroWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicVanishingAbsolute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperBaseChangeTheoremUnconditional

/-!
# The trace formula at the finite levels of an ℓ-adic sheaf on a curve

Let `X` be a separated scheme of finite type and of dimension at most one over a finite field `k`
and `F` an ℓ-adic sheaf on `X`, with torsion-free model `F'`. The levels `F'ₙ` are constructible
flat sheaves of `ℤ/ℓⁿ⁺¹`-modules, so the trace formula of [Stacks, Tag 03UG] for curves
(`cohomologicalTraceFormula_extensionByZero_of_curveTraceCore_of_isConstructibleFlat`)
applies to them: `Tr(π_X^* | RΓ_c(X_k̄, F'ₙ)) = ∑_{x ∈ X(k)} Tr(π_x | (F'ₙ)_x̄)`, item (3) of the
proof of [Stacks, Tag 03V2], in the shape consumed by
`Stacks.EtaleCohomology.LAdicSheaf.traceFormula_of_levelTraceFormula`.

The core of the proof of Tag 03UG over the rings `ℤ/ℓⁿ⁺¹` is the hypothesis `hcore` here.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.isConstructibleFlatEtaleModule_etaleLevel_torsionFreeModel`
* `Stacks.EtaleCohomology.LAdicSheaf.levelTraceFormula_of_topologicalKrullDim_le_one`
* `Stacks.EtaleCohomology.LAdicSheaf.traceFormula_of_topologicalKrullDim_le_one`: Tag 03V2 in
  dimension at most one, from the core.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale
open Stacks.Frobenius Stacks.InverseSystem CategoryTheory.FilteredDerived Stacks.Trace
open Stacks.ZModPrimePower

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

local notation "model" F => LAdicSheaf.torsionFreeModel F (LAdicSheaf.torsionBound F)

/-- **The levels of the torsion-free model of an ℓ-adic sheaf are constructible flat** on
Mathlib's small étale site: they are constructible, and their stalks are pow-exact, hence flat
over `ℤ/ℓⁿ⁺¹`. -/
theorem LAdicSheaf.isConstructibleFlatEtaleModule_etaleLevel_torsionFreeModel
    (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    IsConstructibleFlatEtaleModule B X (ZMod (ℓ ^ (n + 1)))
      (LAdicSheaf.etaleLevel B X ℓ (model F) n) := by
  have h0 : IsConstructibleFlatModuleSheaf B X (ZMod (ℓ ^ (n + 1))) ((model F).level n) :=
    isConstructibleFlatModuleSheaf_of_flat_etaleModuleStalk B X _ _ ((model F).constructible n)
      (fun s => flat_of_isPowExact (LAdicSheaf.isPowExact_finiteLevelStalk (model F) s n
        (LAdicSheaf.powExact_torsionFreeModel_level F le_rfl n)))
  exact isConstructibleFlatModuleSheaf_congr B X _
    ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).unitIso.app
      ((model F).level n)) h0

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
  [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p]
  (hcard : Fintype.card k = p ^ q)

/-- **The trace formula at the finite levels of an ℓ-adic sheaf on a curve** (item (3) of the
proof of [Stacks, Tag 03V2] in dimension at most one, from [Stacks, Tag 03UG]): for `ℓ ≠ p`, the
trace of `π_X^*` on `Kₙ = RΓ_c(X_k̄, F'ₙ)` is the sum over the rational points of the traces of
the geometric Frobenius on the stalks of `F'ₙ`, granted (`hcore`) the core of the proof of
Tag 03UG over the rings `ℤ/ℓⁿ⁺¹`. -/
theorem LAdicSheaf.levelTraceFormula_of_topologicalKrullDim_le_one [Algebra.IsAlgebraic k kbar]
    (hℓp : ℓ ≠ p)
    (hcore : ∀ (n : ℕ) (hΛ : (Nat.card (ZMod (ℓ ^ (n + 1))) : k) ≠ 0),
      CurveTraceCore (ZMod (ℓ ^ (n + 1))) k hΛ kbar p q hcard)
    (hdim : topologicalKrullDim X.1 ≤ 1) (F : LAdicSheaf.{u, u + 1} B X ℓ)
    [Fintype (rationalPoints f)] (n : ℕ) :
    traceAtLevel (LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard (model F)
        (LAdicSheaf.powExact_etaleLevel_torsionFreeModel B X ℓ F le_rfl)
        (isPerfect_compactSupportFrobeniusCohomology_levelComplex_of_topologicalKrullDim_le_one
          B X ℓ f j kbar hdim F)) n =
      ∑ y : rationalPoints f, commutativeAdditiveCommutatorQuotientEval (ZMod (ℓ ^ (n + 1)))
        (perfectDerivedTrace (ZMod (ℓ ^ (n + 1))) ⟨_,
          LAdicSheaf.isPerfect_rationalPointStalkComplex_torsionFreeModel B X ℓ f kbar F n y⟩
          (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} (ZMod (ℓ ^ (n + 1))) kbar p
            q hcard y.1 (LAdicSheaf.levelComplex B X ℓ (model F) n)))) := by
  have hΛ : (Nat.card (ZMod (ℓ ^ (n + 1))) : k) ≠ 0 := by
    rw [Nat.card_zmod, Nat.cast_pow]
    refine pow_ne_zero _ ?_
    rw [Ne, CharP.cast_eq_zero_iff k p]
    intro hdvd
    exact hℓp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : ℓ.Prime)).1 hdvd).symm
  let G := LAdicSheaf.etaleLevel B X ℓ (model F) n
  have hFs : HasPerfectStalks (ZMod (ℓ ^ (n + 1)))
      ⟨(CochainComplex.singleFunctor _ 0).obj G, CochainComplex.plus_singleFunctor_obj G⟩ :=
    LAdicSheaf.isPerfect_stalk_levelComplex_torsionFreeModel B X ℓ F n
  obtain ⟨hperf, htr⟩ :=
    perfectDerivedTrace_canonicalCompactSupportFrobenius_eq_sum_of_cohomologicalTraceFormula
      (ZMod (ℓ ^ (n + 1))) kbar p q hcard f j _ hFs
      (cohomologicalTraceFormula_extensionByZero_of_curveTraceCore_of_isConstructibleFlat
        (ZMod (ℓ ^ (n + 1))) kbar p q hcard (hcore n hΛ) B X f hdim j G
        (LAdicSheaf.isConstructibleFlatEtaleModule_etaleLevel_torsionFreeModel B X ℓ F n) hFs)
  exact (congrArg (commutativeAdditiveCommutatorQuotientEval (ZMod (ℓ ^ (n + 1)))) htr).trans
    (map_sum _ _ _)

/-- **[Stacks, Tag 03V2] in dimension at most one, from the core of Tag 03UG.** For `ℓ ≠ p`, an
ℓ-adic sheaf `F` on a separated scheme `X` of finite type and of dimension at most one over a
finite field `k` and an algebraic closure `k̄` of `k`, the groups `Hⁱ_c(X_k̄, F)` are finite
dimensional over `ℚ_ℓ`, nonzero only for `0 ≤ i ≤ 2 dim X`, and the trace formula holds, granted
(`hcore`) the core of the proof of Tag 03UG over the rings `ℤ/ℓⁿ⁺¹`. -/
theorem LAdicSheaf.traceFormula_of_topologicalKrullDim_le_one [Algebra.IsAlgebraic k kbar]
    (hℓp : ℓ ≠ p)
    (hcore : ∀ (n : ℕ) (hΛ : (Nat.card (ZMod (ℓ ^ (n + 1))) : k) ≠ 0),
      CurveTraceCore (ZMod (ℓ ^ (n + 1))) k hΛ kbar p q hcard)
    (hdim : topologicalKrullDim X.1 ≤ 1) (F : LAdicSheaf.{u, u + 1} B X ℓ) :
    (∀ i : ℤ, Module.Finite ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)) ∧
    (∀ i : ℤ, Nontrivial
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i) →
      0 ≤ i ∧ ∃ d : ℕ, topologicalKrullDim X.1 = d ∧ i ≤ 2 * (d : ℤ)) ∧
    ∑ᶠ (x : closedPoints X.1) (_ : residueDegree f x.1 = 1),
        LinearMap.trace ℚ_[ℓ] _
          (LAdicSheaf.rationalStalkFrobenius B X ℓ F x.1 (finite_residueField f x.1 x.2)) =
      ∑ᶠ i : ℤ, (if Even i then (1 : ℚ_[ℓ]) else -1) *
        LinearMap.trace ℚ_[ℓ]
          (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)
          (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
            i).hom := by
  let : Fintype (rationalPoints f) := @Fintype.ofFinite _ (finite_rationalPoints f)
  exact LAdicSheaf.traceFormula_of_levelTraceFormula B X ℓ f j kbar p q hcard
    (properSeparablyClosedSheafHVanishingStatement_of_properDirectImageVanishingStatement
      properDirectImageVanishingStatement) F
    (isPerfect_compactSupportFrobeniusCohomology_levelComplex_of_topologicalKrullDim_le_one
      B X ℓ f j kbar hdim F)
    (LAdicSheaf.levelTraceFormula_of_topologicalKrullDim_le_one B X ℓ f j kbar p q hcard hℓp
      hcore hdim F)

end Stacks.EtaleCohomology

end
