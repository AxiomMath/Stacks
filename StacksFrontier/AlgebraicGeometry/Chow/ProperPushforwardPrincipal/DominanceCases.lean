module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.NotDominant
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ProjectiveLineDeltaDimension

/-!
# The degree of a principal divisor on a proper curve: the two branches combined

Let `c : X ⟶ S` be proper with `X` integral of delta-dimension one over a field, and `f` an
invertible rational function on `X`. The proper pushforward of `div(f)` to the base vanishes
provided the same holds on `ℙ¹_S`. Let `q : Y ⟶ ℙ¹_S` be the second projection out of the graph
closure of Stacks 02RQ. If `q` is dominant this is the reduction to the projective line; otherwise
`div(f)` is itself zero (`Stacks.Chow.principalDivisorCycle_eq_zero_of_not_isDominant`).

## Main results

* `Stacks.Chow.properPushforward_principalDivisorCycle_eq_zero_of_projectiveLine` — Stacks 02RU
  for a proper integral curve, conditional only on Stacks 02RU for `ℙ¹_S`.

## References

* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
* [Stacks Project, Tag 02RQ](https://stacks.math.columbia.edu/tag/02RQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-- **Stacks 02RU for a proper integral curve, conditional only on the projective-line case.** Let
the base of `C` be the spectrum of a field and its dimension function vanish. If every nonzero
rational function on `ℙ¹_S` has principal divisor of degree zero, then for a proper integral `X` of
delta-dimension one over the base and an invertible rational function `f` on `X`, the proper
pushforward of `div(f)` to the base is zero. -/
theorem properPushforward_principalDivisorCycle_eq_zero_of_projectiveLine
    (k : Type u) [Field k] (C : ChowSituation.{u}) [IsIntegral C.S]
    (hS : C.S = AlgebraicGeometry.Spec (.of k))
    (hδ : ∀ p : C.S, C.dimensionFunction p = 0)
    {X : Scheme.{u}} (c : X ⟶ C.S) [IsProper c] [IsIntegral X]
    (hdim : schemeDeltaDimension C c = (1 : EInt))
    (hP : ∀ h : (relativeProjectiveLine C.S).functionField, h ≠ 0 →
      principalDivisorDegree (relativeProjectiveLine C.S ↘ C.S) h = 0)
    (f : (rationalFunctions X)ˣ) :
    properPushforward C c (𝟙 C.S) c (by simp) 0
      (principalDivisorCycle C c hdim ((rationalFunctionsEquivFunctionField X).1 ↑f)) = 0 := by
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian c
  have hPint : IsIntegral (relativeProjectiveLine C.S) :=
    isIntegral_relativeProjectiveLine C.S
  have hPdim : schemeDeltaDimension C (relativeProjectiveLine C.S ↘ C.S) = (1 : EInt) :=
    schemeDeltaDimension_relativeProjectiveLine_eq_one k C hS hδ
  obtain ⟨U, g, hg⟩ := exists_dense_unit_section f
  by_cases hdom : IsDominant (graphLineProjection c U.1 ↑g)
  · exact properPushforward_principalDivisorCycle_eq_zero_of_graph k C hS hδ c hdim U.1 g U.2 f hg
      hPint hPdim hP hdom
  · have hd : GraphPreimageDense c U.1 ↑g := dense_graphPreimage c U.1 ↑g
    have hYint : IsIntegral (graphClosure c U.1 ↑g) := isIntegral_graphClosure c U.1 ↑g U.2
    have hYft : LocallyOfFiniteType (graphBaseMorphism c U.1 ↑g) :=
      locallyOfFiniteType_graphBaseMorphism c U.1 ↑g
    have hYdim : schemeDeltaDimension C (graphBaseMorphism c U.1 ↑g) = (1 : EInt) :=
      schemeDeltaDimension_graphClosure C c U.1 g 1 hdim U.2 hYft
    have _ : IsIntegral (relativeProjectiveLine C.S) := hPint
    rw [principalDivisorCycle_eq_zero_of_not_isDominant C hδ c hPdim U.1 g 1 hdim f U.2 hg hd
      hYint hYft (graphProjection_isProper c U.1 ↑g) hYdim hdom]
    exact properPushforward_zero C c (𝟙 C.S) c (by simp) 0

end Stacks.Chow

end
