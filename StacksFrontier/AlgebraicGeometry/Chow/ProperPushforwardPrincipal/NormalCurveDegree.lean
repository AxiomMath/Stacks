module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GeneralCurve
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ToProjectiveLine

/-!
# Degree of a principal divisor on a normal proper curve

For a normal proper curve `X` over a field `k` the degree of every principal divisor vanishes:

  `∑_{x ∈ X} ord_x(f) · [κ(x) : k] = 0`.

A normal proper curve carries a proper dominant morphism to `ℙ¹_k`
(`Stacks.Chow.exists_isProper_isDominant_to_projectiveLine`), and on a curve carrying such a
morphism the degree of a principal divisor vanishes
(`Stacks.Chow.principalDivisorDegree_eq_zero_of_properDominant_projectiveLine`).

## Main results

* `Stacks.Chow.principalDivisorDegree_eq_zero_of_isNormal` — the degree of a principal divisor
  on a normal proper curve is zero.
* `Stacks.Chow.properPushforward_principalDivisorCycle_eq_zero_of_isNormal` — the same in its
  cycle form over `Stacks.Chow.fieldChowSituation`.

## References

* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
* [Stacks Project, Tag 0BXZ](https://stacks.math.columbia.edu/tag/0BXZ)
* [Stacks Project, Tag 0A23](https://stacks.math.columbia.edu/tag/0A23)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- On a normal curve `X` proper over a field `k` the degree of the principal divisor of every
nonzero rational function vanishes. -/
theorem principalDivisorDegree_eq_zero_of_isNormal (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (.of k))]
    [IsCurve k (X ↘ AlgebraicGeometry.Spec (.of k))] [IsNormal X]
    [IsProper (X ↘ AlgebraicGeometry.Spec (.of k))] [IsLocallyNoetherian X]
    (f : X.functionField) (hf : f ≠ 0) :
    principalDivisorDegree (X ↘ AlgebraicGeometry.Spec (.of k)) f = 0 := by
  obtain ⟨p, _, _, hcomp⟩ := exists_isProper_isDominant_to_projectiveLine k X
  exact principalDivisorDegree_eq_zero_of_properDominant_projectiveLine p _ hcomp
    (IsCurve.topologicalKrullDim_eq_one (k := k)
      (f := X ↘ AlgebraicGeometry.Spec (.of k))) f hf

/-- The proper pushforward to `Spec k` of the principal divisor of a nonzero rational function
on a normal proper curve vanishes. -/
theorem properPushforward_principalDivisorCycle_eq_zero_of_isNormal (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [IsCurve k (X ↘ AlgebraicGeometry.Spec (.of k))] [IsNormal X]
    [IsProper (X ↘ AlgebraicGeometry.Spec (.of k))] [IsLocallyNoetherian X]
    (c : X ⟶ (fieldChowSituation k).S) [IsProper c]
    (hc : c = X ↘ AlgebraicGeometry.Spec (.of k))
    (hdim : schemeDeltaDimension (fieldChowSituation k) c = ((1 : ℤ) : EInt))
    (f : X.functionField) (hf : f ≠ 0) :
    properPushforward (fieldChowSituation k) c (𝟙 (fieldChowSituation k).S) c
        (Category.comp_id c) 0
      (principalDivisorCycle (fieldChowSituation k) c hdim f) = 0 := by
  refine (properPushforward_principalDivisorCycle_eq_zero_iff (fieldChowSituation k)
    (fieldChowSituation_dimensionFunction_eq_zero k) c hdim f).mpr ?_
  rw [hc]
  exact principalDivisorDegree_eq_zero_of_isNormal k X f hf

end Stacks.Chow

end
