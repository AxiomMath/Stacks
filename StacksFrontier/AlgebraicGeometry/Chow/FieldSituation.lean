module

public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.Base
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveLineDivisorDegree.ProperCurve

/-!
# Stacks 02RU at the spectrum of a field

`Stacks.Chow.properPushforward_principalDivisorCycle_eq_zero` — the vanishing of the degree of a
principal divisor on a proper curve — is stated over a Chow situation subject to two side
conditions: that the base be the spectrum of a field, and that the dimension function vanish. Both
hold at `Stacks.Chow.fieldChowSituation`, so over a field base the theorem holds with no side
condition.

## Main results

* `Stacks.Chow.properPushforward_principalDivisorCycle_eq_zero_fieldChowSituation` — Tag 02RU at
  this base, with its two side conditions discharged.

## References

* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- **Stacks 02RU at the field situation.** For a proper integral curve `X` over the Chow situation
`Stacks.Chow.fieldChowSituation k` of the field `k`, the proper pushforward to the base of the
principal divisor of an invertible rational function on `X` vanishes. -/
theorem properPushforward_principalDivisorCycle_eq_zero_fieldChowSituation (k : Type u) [Field k]
    {X : Scheme.{u}} (c : X ⟶ (fieldChowSituation k).S) [IsProper c] [IsIntegral X]
    (hdim : schemeDeltaDimension (fieldChowSituation k) c = (1 : EInt))
    (f : (rationalFunctions X)ˣ) :
    properPushforward (fieldChowSituation k) c (𝟙 (fieldChowSituation k).S) c (by simp) 0
      (principalDivisorCycle (fieldChowSituation k) c hdim
        ((rationalFunctionsEquivFunctionField X).1 ↑f)) = 0 :=
  properPushforward_principalDivisorCycle_eq_zero k (fieldChowSituation k) rfl (fun _ => rfl) c
    hdim f

end Stacks.Chow

end
