module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.CurveDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ProjectiveLineDegree

/-!
# Degree of a principal divisor on a curve over the projective line

Let `X` be a proper integral curve over a field `k` admitting a proper dominant morphism
`p : X ⟶ ℙ¹_k`. Then the degree of the principal divisor of every nonzero rational function on
`X` vanishes.

## Main results

* `Stacks.Chow.properPushforward_principalDivisorCycle_eq_zero_of_properDominant_projectiveLine`:
  the proper pushforward to `Spec k` of the principal divisor of a nonzero rational function on
  `X` vanishes.
* `Stacks.Chow.principalDivisorDegree_eq_zero_of_properDominant_projectiveLine`: the degree of
  the principal divisor of a nonzero rational function on `X`, computed along any structure
  morphism `q : X ⟶ Spec k` factoring through `p`, vanishes.

## References

* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
* [Stacks Project, Tag 02RT](https://stacks.math.columbia.edu/tag/02RT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k]

/-- Let `X` be an integral curve over a field `k` with a proper dominant morphism
`p : X ⟶ ℙ¹_k`. Then the proper pushforward to `Spec k` of the principal divisor of a nonzero
rational function on `X` vanishes. -/
theorem properPushforward_principalDivisorCycle_eq_zero_of_properDominant_projectiveLine
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ projectiveLine k)
    [IsProper p] [IsDominant p]
    (hnX : schemeDeltaDimension (fieldChowSituation k) (p ≫ projectiveLineOverField k) =
      ((1 : ℤ) : EInt))
    (f : X.functionField) (hf : f ≠ 0) :
    properPushforward (fieldChowSituation k) (p ≫ projectiveLineOverField k)
        (𝟙 (fieldChowSituation k).S) (p ≫ projectiveLineOverField k) (by simp) 0
      (principalDivisorCycle (fieldChowSituation k) (p ≫ projectiveLineOverField k) hnX f) = 0 :=
  properPushforward_principalDivisorCycle_eq_zero_of_properDominant (fieldChowSituation k)
    (fieldChowSituation_dimensionFunction_eq_zero k) (projectiveLineOverField k) p hnX
    (schemeDeltaDimension_projectiveLine k)
    (fun g hg ↦ principalDivisorDegree_projectiveLine_eq_zero k g hg) f hf

/-- Let `X` be an integral scheme of topological dimension one, proper over a field `k` through a
morphism that factors as a proper dominant `p : X ⟶ ℙ¹_k` followed by the structure morphism of
the projective line. Then for every nonzero rational function `f` on `X`

  `∑_{x ∈ X} ord_x(f) · [κ(x) : k] = 0`. -/
theorem principalDivisorDegree_eq_zero_of_properDominant_projectiveLine {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ projectiveLine k) [IsProper p] [IsDominant p]
    (q : X ⟶ AlgebraicGeometry.Spec (.of k))
    (hq : p ≫ (projectiveLine k ↘ AlgebraicGeometry.Spec (.of k)) = q)
    (hdim : topologicalKrullDim X = ((1 : ℕ) : WithBot ℕ∞))
    (f : X.functionField) (hf : f ≠ 0) :
    principalDivisorDegree q f = 0 := by
  have hnX : schemeDeltaDimension (fieldChowSituation k) (p ≫ projectiveLineOverField k) =
      ((1 : ℤ) : EInt) :=
    schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq (n := 1) _ hdim
  rw [← hq]
  exact (properPushforward_principalDivisorCycle_eq_zero_iff (fieldChowSituation k)
    (fieldChowSituation_dimensionFunction_eq_zero k) _ hnX f).mp
    (properPushforward_principalDivisorCycle_eq_zero_of_properDominant_projectiveLine p hnX f hf)

end Stacks.Chow

end
