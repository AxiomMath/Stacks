module

public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.ClosedPointDivisor
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass

/-!
# The Picard class of a closed point of a smooth curve

Let `X` be a smooth curve over a field `k` and `x` a closed point of `X`. The reduced point
`x`, cut out by the vanishing ideal of `{x}`, is an effective Cartier divisor
(`AlgebraicGeometry.IsCurve.isEffectiveCartierDivisor_vanishingIdeal_closure_singleton`), so it
has an invertible sheaf `𝒪_X(x)` and a class `[𝒪_X(x)]` in `Pic(X) = Stacks.Picard.ofScheme X`.

## Main definitions

* `AlgebraicGeometry.IsCurve.pointPicardClass`: the class `[𝒪_X(x)]` of a closed point.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.IsCurve

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]

/-- **The Picard class `[𝒪_X(x)]` of a closed point `x` of a smooth curve**: the class of the
invertible sheaf of the reduced point, an effective Cartier divisor. -/
def pointPicardClass {x : X} (hx : IsClosed ({x} : Set X)) : Stacks.Picard.ofScheme X :=
  letI := isEffectiveCartierDivisor_vanishingIdeal_closure_singleton k f hx
  Stacks.Divisors.picardClass (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X)))

end AlgebraicGeometry.IsCurve

end
