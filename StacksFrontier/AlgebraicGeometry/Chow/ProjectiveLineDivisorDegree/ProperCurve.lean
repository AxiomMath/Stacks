module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveLineDivisorDegree.Degree
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.DominanceCases

/-!
# The degree of a principal divisor on a proper curve over a field

Let `C = (S, δ)` be a Chow situation whose base is the spectrum of a field `k` and whose dimension
function vanishes identically, and let `c : X ⟶ S` be proper with `X` integral of delta-dimension
one — a proper curve over `k`. For every invertible rational function `f` on `X` the proper
pushforward of the principal divisor of `f` to the base vanishes.

## Main results

* `Stacks.Chow.properPushforward_principalDivisorCycle_eq_zero` — the degree of a principal
  divisor on a proper integral curve over a field vanishes.
* `Stacks.Chow.principalDivisorDegree_eq_zero_of_isProper` — the same statement in the
  displayed-sum form `∑_x ord_x(f) · [κ(x) : k] = 0`.

## References

* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
* [Stacks Project, Tag 02RQ](https://stacks.math.columbia.edu/tag/02RQ)
* [Stacks Project, Tag 02RT](https://stacks.math.columbia.edu/tag/02RT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Order TopologicalSpace

universe u

namespace Stacks.Chow

/-- **The degree of a principal divisor on a proper curve over a field vanishes.** For a Chow
situation whose base is the spectrum of a field with vanishing dimension function, a proper
integral `X` of delta-dimension one over that base, and an invertible rational function `f` on `X`,
the proper pushforward of `div(f)` to the base is zero. -/
@[stacks 02RU "pushforward of the principal divisor"]
theorem properPushforward_principalDivisorCycle_eq_zero
    (k : Type u) [Field k] (C : ChowSituation.{u})
    (hS : C.S = AlgebraicGeometry.Spec (.of k))
    (hδ : ∀ p : C.S, C.dimensionFunction p = 0)
    {X : Scheme.{u}} (c : X ⟶ C.S) [IsProper c] [IsIntegral X]
    (hdim : schemeDeltaDimension C c = (1 : EInt))
    (f : (rationalFunctions X)ˣ) :
    properPushforward C c (𝟙 C.S) c (by simp) 0
      (principalDivisorCycle C c hdim ((rationalFunctionsEquivFunctionField X).1 ↑f)) = 0 := by
  cases C with
  | mk S hUC δ =>
    subst hS
    exact properPushforward_principalDivisorCycle_eq_zero_of_projectiveLine k _ rfl hδ c hdim
      (fun h hne => principalDivisorDegree_lineOver_eq_zero k h hne) f

/-- **Stacks 02RU in the displayed-sum form.** For a proper integral curve over a field the
weighted sum `∑_x ord_x(f) · [κ(x) : k]` of the orders of vanishing of an invertible rational
function vanishes. This is the other form of
`Stacks.Chow.properPushforward_principalDivisorCycle_eq_zero`, the two being identified by
`Stacks.Chow.properPushforward_principalDivisorCycle_eq_zero_iff`. -/
@[stacks 02RU "displayed-sum form"]
theorem principalDivisorDegree_eq_zero_of_isProper
    (k : Type u) [Field k] (C : ChowSituation.{u})
    (hS : C.S = AlgebraicGeometry.Spec (.of k))
    (hδ : ∀ p : C.S, C.dimensionFunction p = 0)
    {X : Scheme.{u}} (c : X ⟶ C.S) [IsProper c] [IsIntegral X] [IsLocallyNoetherian X]
    (hdim : schemeDeltaDimension C c = (1 : EInt))
    (f : (rationalFunctions X)ˣ) :
    principalDivisorDegree c ((rationalFunctionsEquivFunctionField X).1 ↑f) = 0 := by
  have hsub : Subsingleton C.S := by rw [hS]; infer_instance
  have hne : Nonempty C.S := by rw [hS]; infer_instance
  rw [← properPushforward_principalDivisorCycle_eq_zero_iff C hδ c hdim]
  exact properPushforward_principalDivisorCycle_eq_zero k C hS hδ c hdim f

end Stacks.Chow

end
