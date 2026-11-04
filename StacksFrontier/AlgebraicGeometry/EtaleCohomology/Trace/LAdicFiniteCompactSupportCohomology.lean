module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicTraceFormulaFinal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIDimensionStepInputs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicLowerShriekTower

/-!
# Finiteness of compactly supported ℓ-adic cohomology in every dimension

For `X` separated of finite type over a finite field `k` of characteristic `p ≠ ℓ`, `k̄` an
algebraic closure of `k`, any compactification of `X` and any ℓ-adic sheaf `F` on `X`:
`Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` is finite dimensional (part (1) of Tag 03V2,
`Stacks.EtaleCohomology.LAdicSheaf.traceFormula`), and `Hⁱ_c(X_k̄, Fₙ)` is finite at every level
(`Stacks.EtaleCohomology.LAdicSheaf.torsionCompactSupportFinitenessInput`, the levels being
constructible ℓ-power torsion sheaves of `ℤ_ℓ`-modules). This is
`Stacks.EtaleCohomology.LAdicSheaf.FiniteCompactSupportCohomologyInput`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.finiteCompactSupportCohomologyInput`:
  `Stacks.EtaleCohomology.LAdicSheaf.FiniteCompactSupportCohomologyInput` holds.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- **`Stacks.EtaleCohomology.LAdicSheaf.FiniteCompactSupportCohomologyInput` holds**: for `X`
separated of finite type over a finite field `k` of characteristic `p ≠ ℓ`, `k̄` an algebraic
closure of `k`, every compactification of `X` and every ℓ-adic sheaf `F` on `X`,
`Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` is finite dimensional over `ℚ_ℓ` (Tag 03V2) and every `Hⁱ_c(X_k̄, Fₙ)` is
finite. -/
theorem LAdicSheaf.finiteCompactSupportCohomologyInput :
    LAdicSheaf.FiniteCompactSupportCohomologyInput B ℓ := by
  intro k _ _ kbar _ _ _ p q _ _ hcard hℓp X _ f _ _ _ j F i
  exact ⟨(LAdicSheaf.traceFormula B X ℓ f j kbar p q hcard hℓp F).1 i, fun n =>
    LAdicSheaf.torsionCompactSupportFinitenessInput B ℓ k kbar p q hcard hℓp X f j _
      (LAdicSheaf.isConstructibleEtaleModule_padicTower F n.unop)
      ⟨n.unop + 1, LAdicSheaf.padicTower_annihilated B X ℓ F n.unop⟩ i⟩

end Stacks.EtaleCohomology

end
