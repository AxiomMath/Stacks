module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveConstantCoefficientTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilTraceFormulaCurve
public import StacksCore.Tactic.StacksAttribute

/-!
# Weil's trace formula in the étale cohomology of a curve, modulo `ℓ^n`

Let `C` be a nonsingular projective curve over an algebraically closed field `k`, let
`φ : C → C` be a `k`-endomorphism of `C` distinct from the identity, and let `ℓ` be a prime
invertible in `k`. Then each `H^i(C, ℤ/ℓ^n)` is a free `ℤ/ℓ^n`-module of finite rank and

  `∑_{i=0}^{2} (-1)^i Tr(φ^* | H^i(C, ℤ/ℓ^n)) = V(φ) mod ℓ^n`,

where `V(φ) = Δ_C · Γ_φ` is the intersection number on `C × C`.

Here `H^i(C, ℤ/ℓ^n)` is the étale cohomology of the constant sheaf `ℤ/ℓ^n` on `C_étale`, and `φ^*`
is restriction along `φ` followed by the canonical identification `φ^{-1}(ℤ/ℓ^n) ≅ ℤ/ℓ^n`. The
traces are computed degree by degree in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveConstantCoefficientTrace` (`1`,
`Tr_J(φ^*) mod ℓ^n` and `deg φ`), and the alternating sum is `V(φ)` by Weil's formula
[Stacks, Tag 03U1].

## References

* [Stacks Project, Tag 03U3](https://stacks.math.columbia.edu/tag/03U3)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- **Weil's trace formula modulo `ℓ^n` (Stacks 03U3).** Let `C` be a nonsingular projective curve
over an algebraically closed field `k`, let `φ : C → C` be a `k`-endomorphism of `C` distinct from
the identity, and let `ℓ` be a prime invertible in `k`. Then every étale cohomology module
`H^i(C, ℤ/ℓ^n)` of the constant sheaf is free of finite rank over `ℤ/ℓ^n`, and

  `∑_{i=0}^{2} (-1)^i Tr(φ^* | H^i(C, ℤ/ℓ^n)) = V(φ) mod ℓ^n`,

with `V(φ) = Δ_C · Γ_φ` the intersection number on `C ×_k C`
(`AlgebraicGeometry.CurveGraph.fixedPointIntersection`), and `φ^*` the pullback on étale
cohomology: restriction along `φ` followed by the canonical identification `φ^{-1}(ℤ/ℓ^n) ≅ ℤ/ℓ^n`.

The degreewise traces are `1`, `Tr_J(φ^*) mod ℓ^n` and `deg φ`
(`Stacks.EtaleCohomology.sum_trace_etaleConstantCohomologyPullback_eq_toZModPow`), and Weil's
formula `V(φ) = 1 - Tr_J(φ^*) + deg φ` ([Stacks, Tag 03U1],
`AlgebraicGeometry.CurveGraph.fixedPointIntersection_eq`) concludes. -/
@[stacks 03U3]
theorem sum_trace_etaleConstantCohomologyPullback_eq_fixedPointIntersection
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [IsCurve k f] [Smooth f] [IsProper f] (φ : C ⟶ C) (w : φ ≫ f = f)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : k)) (n : ℕ) :
    (∀ i : ℕ, Module.Free (ZMod (ℓ ^ n))
        (Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} C (ZMod (ℓ ^ n))) i) ∧
      Module.Finite (ZMod (ℓ ^ n))
        (Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} C (ZMod (ℓ ^ n))) i)) ∧
    ∑ i ∈ Finset.range 3, (-1 : ZMod (ℓ ^ n)) ^ i * LinearMap.trace (ZMod (ℓ ^ n)) _
        ((etaleConstantCohomologyPullback φ (ZMod (ℓ ^ n)) i).toZModLinearMap (ℓ ^ n)) =
      (CurveGraph.fixedPointIntersection f (IsCurve.topologicalKrullDim_eq_one (f := f)).le φ w :
        ZMod (ℓ ^ n)) := by
  refine ⟨module_free_finite_sheafH_etaleConstantSheaf f ℓ n hℓ, ?_⟩
  rw [sum_trace_etaleConstantCohomologyPullback_eq_toZModPow f φ w ℓ n hℓ,
    ← CurveGraph.fixedPointIntersection_eq f _ φ w ℓ hℓ, map_intCast]

end Stacks.EtaleCohomology
