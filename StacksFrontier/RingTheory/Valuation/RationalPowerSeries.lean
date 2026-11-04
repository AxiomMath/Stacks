module

public import StacksFrontier.RingTheory.Valuation.RationalPowerSeries.CoefficientRing
public import StacksFrontier.RingTheory.Valuation.RationalPowerSeries.CompletionEquiv
public import StacksFrontier.RingTheory.Valuation.RationalPowerSeries.ValuationRing
public import StacksFrontier.RingTheory.Valuation.RationalPowerSeries.RadicalCompletion

/-!
# Power series with nonnegative rational exponents

The valuation ring of power series with nonnegative rational exponents over a field
(Stacks 0CB8) and the two completions of the monoid algebra `κ[t^(ℚ≥0)]` (Stacks 0CKX). The
development is split into `CoefficientRing` (the construction as a `(t)`-adic completion and
the coefficient ring inside the Hahn series ring), `CompletionEquiv` (the identification of the
completion with that coefficient ring), `ValuationRing` (the ring is a complete local domain
and a valuation ring with non-finitely generated maximal ideal) and `RadicalCompletion` (the
radical of `(t)` and the completion at it).
-/
