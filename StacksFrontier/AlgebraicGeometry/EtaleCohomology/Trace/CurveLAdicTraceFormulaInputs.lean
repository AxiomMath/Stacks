module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveLAdicLevelTraceFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTraceFormulaPow
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafTracePow
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseCurveTraceFormulaInput

/-!
# The trace formula on a smooth curve over the extensions of the base field

For a smooth separated curve `U` over a finite field `k`, an algebraic closure `k̄` of `k`, an
ℓ-adic sheaf `F` on `U` (`ℓ ≠ p`) and `N ≥ 1`,

```
∑_{deg y ∣ N} deg y · Tr((π_y^*)^{N / deg y} | F_ȳ)
  = ∑_{i < 3} (-1)ⁱ Tr((π_U^*)^N | Hⁱ_c(U_k̄, F))
```

[Stacks, Tag 03V2] for the curves `U ×_k k_N`, rewritten over `U` as in the proof of
[Stacks, Tag 03V0]. This gives the propositions
`Stacks.EtaleCohomology.LisseCurveTraceFormulaInput` and
`Stacks.EtaleCohomology.CurveTraceFormulaInput`, granted (`hcore`) the core of the proof of
[Stacks, Tag 03UG] (`Stacks.EtaleCohomology.CurveTraceCore`) over every finite field.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.curveTraceFormula_pow_of_curveTraceCore`
* `Stacks.EtaleCohomology.lisseCurveTraceFormulaInput_of_curveTraceCore`
* `Stacks.EtaleCohomology.curveTraceFormulaInput_of_curveTraceCore`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

/-- **The trace formula for `(π_U^*)^N` on a smooth curve**, from the core of the proof of
[Stacks, Tag 03UG] over every finite field (`hcore`). -/
theorem LAdicSheaf.curveTraceFormula_pow_of_curveTraceCore
    (hcore : ∀ (Λ : Type) [Ring Λ] [Finite Λ] (k : Type u) [Field k] [Fintype k]
      (hΛ : (Nat.card Λ : k) ≠ 0) (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar]
      [Algebra.IsAlgebraic k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p]
      (hcard : Fintype.card k = p ^ q), CurveTraceCore Λ k hΛ kbar p q hcard)
    (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B U.1 U.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [IsNoetherian U.1] [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fintype k] (f : U.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar]
    (p n : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n) (hℓp : ℓ ≠ p)
    (F : LAdicSheaf.{u, u + 1} B U ℓ) (N : ℕ) (hN : 0 < N) :
    ∑ᶠ (y : closedPoints U.1) (_ : residueDegree f y.1 ∣ N), (residueDegree f y.1 : ℚ_[ℓ]) *
        LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B U ℓ F y.1
          (finite_residueField f y.1 y.2) ^ (N / residueDegree f y.1)) =
      ∑ i ∈ Finset.range 3, (-1 : ℚ_[ℓ]) ^ i * LinearMap.trace ℚ_[ℓ]
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar F (i : ℤ))
        ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ f j kbar p n hcard F
          (i : ℤ)).hom ^ N) := by
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  have hU : topologicalKrullDim U.1 ≤ ((1 : ℕ) : WithBot ℕ∞) := by
    rcases isEmpty_or_nonempty U.1 with hX | hX
    · rw [(topologicalKrullDim_eq_bot_iff_isEmpty _).2 hX]
      exact bot_le
    · exact (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 f).le
  rw [LAdicSheaf.finsum_trace_pow_eq_of_traceFormula B U ℓ f j kbar p n hcard F ?_ N hN.ne']
  · exact LAdicSheaf.finsum_trace_pow_eq_sum_range_three B U ℓ f j kbar p n hcard F N
  · intro k' _ _ _ _ _ _ _ _ q' hcard'
    have : Algebra.IsAlgebraic k' kbar := Algebra.IsAlgebraic.tower_top (K := k) k'
    have hdim' : topologicalKrullDim (fieldExtensionScheme B U f k').1 ≤ 1 := by
      have h := topologicalKrullDim_pullback_le_of_fiber f ((1 : ℕ) : WithBot ℕ∞)
        (fun y ↦ (topologicalKrullDim_fiber_of_spec_field k f y).le.trans hU)
        (specAlgebraMap k k')
      exact_mod_cast h
    exact (LAdicSheaf.traceFormula_of_topologicalKrullDim_le_one B (fieldExtensionScheme B U f k')
      ℓ (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f j k') kbar p q'
      hcard' hℓp (fun m hΛ => hcore _ k' hΛ kbar p q' hcard') hdim'
      (LAdicSheaf.inverseImage (fieldExtensionProj B U f k') F)).2.2

/-- **`Stacks.EtaleCohomology.LisseCurveTraceFormulaInput` from the core of the proof of
[Stacks, Tag 03UG]** over every finite field. -/
theorem lisseCurveTraceFormulaInput_of_curveTraceCore
    (hcore : ∀ (Λ : Type) [Ring Λ] [Finite Λ] (k : Type u) [Field k] [Fintype k]
      (hΛ : (Nat.card Λ : k) ≠ 0) (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar]
      [Algebra.IsAlgebraic k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p]
      (hcard : Fintype.card k = p ^ q), CurveTraceCore Λ k hΛ kbar p q hcard) :
    LisseCurveTraceFormulaInput.{u} :=
  fun B U ℓ _ _ _ _ _ k _ _ f _ _ _ _ j kbar _ _ _ p n _ _ hcard hℓp F _ N hN =>
    LAdicSheaf.curveTraceFormula_pow_of_curveTraceCore hcore B U ℓ k f j kbar p n hcard hℓp F N hN

/-- **`Stacks.EtaleCohomology.CurveTraceFormulaInput` from the core of the proof of
[Stacks, Tag 03UG]** over every finite field: the trace formula for `(π_U^*)^N` applied to the
sheaf `ℱ_τ`, with `Tr((π_y^*)^m | (ℱ_τ)_ȳ) = Tr(τ(F_y)^m)`. -/
theorem curveTraceFormulaInput_of_curveTraceCore
    (hcore : ∀ (Λ : Type) [Ring Λ] [Finite Λ] (k : Type u) [Field k] [Fintype k]
      (hΛ : (Nat.card Λ : k) ≠ 0) (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar]
      [Algebra.IsAlgebraic k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p]
      (hcard : Fintype.card k = p ^ q), CurveTraceCore Λ k hΛ kbar p q hcard) :
    CurveTraceFormulaInput.{u} := by
  intro B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ j kbar _ _ _ _ p n _ _ hcard hℓp x m τ hτ N hN
  refine Eq.trans ?_ (LAdicSheaf.curveTraceFormula_pow_of_curveTraceCore hcore B U ℓ k f j kbar
    p n hcard hℓp (LAdicSheaf.representationSheaf B U x τ hτ) N hN)
  refine finsum_congr fun y => finsum_congr fun _ => ?_
  rw [trace_rationalStalkFrobenius_representationSheaf_pow B U x f τ hτ y]

end Stacks.EtaleCohomology

end
