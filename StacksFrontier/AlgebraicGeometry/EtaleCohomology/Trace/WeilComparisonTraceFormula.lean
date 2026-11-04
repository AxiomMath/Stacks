module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilComparisonConstantCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaCtf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilTraceFormulaCurve
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The trace formula with constant coefficients and Weil's formula

[Stacks, Tag 03UJ]: let `X` be a smooth projective curve over a finite field `k` and `ℓ ≠ p` a
prime. The trace formula (Tag 03UG) with `Λ = ℤ/ℓⁿ` gives

`#X(k) = ∑ᵢ (-1)ⁱ Tr(π_X^* | Hⁱ(X_k̄, ℤ/ℓⁿ))`,

and the number `#X(k)` agrees with the one computed by Weil's trace formula (Tag 03U1) for the
geometric Frobenius `π̄ = π_X × id` of `X_k̄`: `#X(k) = V(π̄) = 1 - Tr(π̄ | T_ℓ J) + deg π̄`.

## Main results

* `Stacks.EtaleCohomology.canonicalTraceFormula_constantCoefficients`: Tag 03UG for the constant
  sheaf `ℤ/ℓⁿ` on a smooth projective curve.
* `Stacks.EtaleCohomology.traceFormula_constantCoefficients_eq_weil`: [Stacks, Tag 03UJ].

## References

* [Stacks Project, Tag 03UJ](https://stacks.math.columbia.edu/tag/03UJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius CategoryTheory.FilteredDerived

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) {k : Type u} [Field k] [Fintype k] {p q : ℕ} [Fact p.Prime]
  [CharP k p] (hcard : Fintype.card k = p ^ q) {X : B.Scheme} (f : X.obj ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [IsProper f] (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
  [Algebra k kbar] [Algebra.IsAlgebraic k kbar] (ℓ n : ℕ) [Fact ℓ.Prime]

omit [Smooth f] in
/-- **[Stacks, Tag 03UG] for constant coefficients `ℤ/ℓⁿ`** on a proper curve over `k`, computed
through the compactification `id : X ⟶ X`. -/
theorem canonicalTraceFormula_constantCoefficients (hℓ : ℓ ≠ p) :
    haveI : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
    CanonicalTraceFormula (ZMod (ℓ ^ n)) kbar p q hcard f (CompactificationOf.ofProper f)
      (constantCoefficients (ZMod (ℓ ^ n)) X.obj) := by
  have : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  have : NeZero (ℓ ^ n) := ⟨pow_ne_zero n (Fact.out : ℓ.Prime).ne_zero⟩
  have hcop : Nat.Coprime (Nat.card (ZMod (ℓ ^ n))) (Fintype.card k) := by
    rw [Nat.card_zmod, hcard]
    exact Nat.Coprime.pow n q ((Nat.coprime_primes Fact.out Fact.out).2 hℓ)
  have hdim : topologicalKrullDim X.obj ≤ ((1 : ℕ) : WithBot ℕ∞) := by
    rw [IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)]
    rfl
  exact traceFormulaUpToDim_one B (ZMod (ℓ ^ n)) kbar p q hcard hcop X f hdim
    (CompactificationOf.ofProper f) _ (isCtf_constantCoefficients B (ZMod (ℓ ^ n)) X)

/-- **[Stacks, Tag 03UJ]: the trace formula with constant coefficients recovers Weil's
formula.** Let `X` be a smooth projective curve over a finite field `k` with `#k = p ^ q`, which
stays a curve over an algebraic closure `k̄` (the setting of Weil's formula, Tag 03U1, on `X_k̄`),
and let `ℓ ≠ p` be a prime. Let `π̄ = π_X × id` be the geometric Frobenius of `X_k̄`. Then

* the trace formula (Tag 03UG) for `Λ = ℤ/ℓⁿ` gives `Tr(π_X^* | RΓ(X_k̄, ℤ/ℓⁿ)) = #X(k)`;
* this Lefschetz number is `∑ᵢ (-1)ⁱ Tr(π̄^* | Hⁱ(X_k̄, ℤ/ℓⁿ))`;
* the intersection number `V(π̄) = (Δ · Γ_π̄)` is `#X(k)` (the fixed points of `π̄` are simple);
* hence Weil's formula (Tag 03U1) for `π̄` reads `#X(k) = 1 - Tr(π̄ | T_ℓ J) + deg π̄` in `ℤ_ℓ`.

So both formulas count the same number `#X(k)`. -/
@[stacks 03UJ, sga "4½ Rapport 3.2" "special case"]
theorem traceFormula_constantCoefficients_eq_weil
    [IsCurve kbar (pullback.snd f (specAlgebraMap k kbar))] (hℓ : ℓ ≠ p) :
    canonicalCompactSupportLefschetzNumber.{u, 0} (ZMod (ℓ ^ n)) f (CompactificationOf.ofProper f)
        kbar p q hcard (constantCoefficients (ZMod (ℓ ^ n)) X.obj)
        (isPerfect_compactSupportFrobeniusCohomology_constantCoefficients B (ZMod (ℓ ^ n)) f
          (isProjective_of_isProper_of_isCurve f) kbar) =
      (Nat.card (rationalPoints f) : ℤ) • additiveCommutatorQuotientMk (ZMod (ℓ ^ n)) 1 ∧
    canonicalCompactSupportLefschetzNumber.{u, 0} (ZMod (ℓ ^ n)) f (CompactificationOf.ofProper f)
        kbar p q hcard (constantCoefficients (ZMod (ℓ ^ n)) X.obj)
        (isPerfect_compactSupportFrobeniusCohomology_constantCoefficients B (ZMod (ℓ ^ n)) f
          (isProjective_of_isProper_of_isCurve f) kbar) =
      additiveCommutatorQuotientMk (ZMod (ℓ ^ n))
        (∑ i ∈ Finset.range 3, (-1 : ZMod (ℓ ^ n)) ^ i * LinearMap.trace (ZMod (ℓ ^ n)) _
          ((etaleConstantCohomologyPullback
            (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard)
            (ZMod (ℓ ^ n)) i).toZModLinearMap (ℓ ^ n))) ∧
    AlgebraicGeometry.CurveGraph.fixedPointIntersection (pullback.snd f (specAlgebraMap k kbar))
        (IsCurve.topologicalKrullDim_eq_one (k := kbar)
          (f := pullback.snd f (specAlgebraMap k kbar))).le
        (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard)
          (geometricFrobeniusBaseChange_comp_toBase (Over.mk f) kbar p q hcard) =
      Nat.card (rationalPoints f) ∧
    (((Nat.card (rationalPoints f) : ℤ)) : ℤ_[ℓ]) =
      1 - AlgebraicGeometry.CurveGraph.jacobianTateTrace (pullback.snd f (specAlgebraMap k kbar))
        (IsCurve.topologicalKrullDim_eq_one (k := kbar)
          (f := pullback.snd f (specAlgebraMap k kbar))).le
        (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard)
          (geometricFrobeniusBaseChange_comp_toBase (Over.mk f) kbar p q hcard) ℓ +
        (AlgebraicGeometry.CurveGraph.curveMapDegree (pullback.snd f (specAlgebraMap k kbar))
          (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard)
          (geometricFrobeniusBaseChange_comp_toBase (Over.mk f) kbar p q hcard) : ℤ_[ℓ]) := by
  have : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  exact traceFormula_constantCoefficients_weil_of B hcard f kbar ℓ n hℓ
    (canonicalTraceFormula_constantCoefficients B hcard f kbar ℓ n hℓ)
    (AlgebraicGeometry.CurveGraph.fixedPointIntersection_eq _ _ _ _
      (geometricFrobeniusBaseChange_ne_id B hcard f kbar) ℓ (isUnit_natCast_of_ne_char kbar p ℓ hℓ))

end Stacks.EtaleCohomology

end
