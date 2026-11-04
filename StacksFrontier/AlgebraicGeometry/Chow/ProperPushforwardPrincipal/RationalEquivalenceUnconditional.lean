module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.DimensionDropApplications

/-!
# Proper pushforward preserves rational equivalence

## Main results

* `Stacks.Chow.properPushforward_rationallyEquivalent_of_isProper`: the pushforwards along a
  proper morphism over the base of two rationally equivalent cycles are rationally equivalent.

## References

* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- Proper pushforward preserves rational equivalence of cycles: if `α` and `β` are rationally
equivalent `k`-cycles on `X` and `p : X ⟶ Y` is proper over the base, then `p_*α` and `p_*β` are
rationally equivalent `k`-cycles on `Y`. -/
@[stacks 02S2]
theorem properPushforward_rationallyEquivalent_of_isProper (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (p : X ⟶ Y) [IsProper p] (hp : p ≫ sY = sX) (k : ℤ)
    {α β : CycleGroup C sX k} (h : RationallyEquivalent C sX k α β) :
    RationallyEquivalent C sY k (properPushforward C sX sY p hp k α)
      (properPushforward C sX sY p hp k β) :=
  properPushforward_rationallyEquivalent C sX sY p hp k
    (properPushforwardFactorsThroughRationalEquivalence C sX sY p hp k) h

end Stacks.Chow

end
