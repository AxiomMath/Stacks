module

public import StacksFrontier.RingTheory.IntegralClosure.OverIdeal

/-!
# Integrality over an ideal: the Rees algebra criterion, forward direction

This file keeps the name `isIntegralElem_of_isIntegralElemOverIdeal`, now a deprecated alias of
`isIntegralElem_of_isIntegralOverIdeal`, for the forward implication of [Stacks, Tag 00H3]. The
equivalence itself is `isIntegralElemOverIdeal_iff_isIntegralElem`, in
`StacksFrontier/RingTheory/IntegralClosure/OverIdeal.lean`.

## Main results

* `isIntegralElem_of_isIntegralElemOverIdeal`: deprecated alias; if `s : S` is integral over the
  ideal `I ⊆ R` along `φ : R →+* S`, then `C s · X` is integral over the Rees algebra of `I`.
-/

@[expose] public section

/-- The forward direction of `isIntegralElemOverIdeal_iff_isIntegralElem`, under its earlier name:
use `isIntegralElem_of_isIntegralOverIdeal`. -/
@[deprecated isIntegralElem_of_isIntegralOverIdeal (since := "2026-11-05")]
alias isIntegralElem_of_isIntegralElemOverIdeal := isIntegralElem_of_isIntegralOverIdeal

end
