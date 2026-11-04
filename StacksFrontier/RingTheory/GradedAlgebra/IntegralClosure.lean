module

public import StacksFrontier.RingTheory.GradedAlgebra.IntegralClosure.GradedTwist
public import StacksFrontier.RingTheory.GradedAlgebra.IntegralClosure.TwoVariableDescent
public import StacksFrontier.RingTheory.GradedAlgebra.IntegralClosure.Homogeneous

/-!
# The integral closure of a graded ring is graded

This file re-exports its parts:

* `GradedTwist`: the graded twist `Ψ : S →+* S[T;T⁻¹]` and its integrality;
* `TwoVariableDescent`: the two-variable Laurent descent lemmas;
* `Homogeneous`: integrality of homogeneous components and the main theorem
  `integralClosure_carrier_eq` (Stacks Tag 077G).
-/
