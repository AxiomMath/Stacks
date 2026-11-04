module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GenericFibre

/-!
# Proper pushforward of the class of a closed subscheme that stays closed, on Chow groups

Let `f : X ⟶ Y` be proper over the base of chapter 42 and `i : Z ⟶ X` a closed immersion whose
composite `i ≫ f` is again a closed immersion. On cycles,
`Stacks.Chow.properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp` gives
`f_*[Z ⊆ X]_k = [Z ⊆ Y]_k`. This file reads that identity in the Chow groups, for the genuine
proper pushforward `f_* : A_k(X) ⟶ A_k(Y)` whose descent through rational equivalence is
Stacks 02S2 (`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isProper`), so
nothing is carried.

It is the Chow-side step of the proof of [Stacks, Tag 0FIR]: for a closed immersion
`h : Z ⟶ X × G` whose composite with the projection `p : X × G ⟶ X` is the closed immersion
`i : Z ⟶ X`, the class `[Z]` on `X × G` pushes forward to the class `[Z]` on `X`. It is a special
case of Stacks 02R6 (see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme`) and carries no attribute.

## Main results

* `Stacks.Chow.properChowPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp`

## References

* [Stacks Project, Tag 02R6](https://stacks.math.columbia.edu/tag/02R6)
* [Stacks Project, Tag 0FIR](https://stacks.math.columbia.edu/tag/0FIR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- **The class of a closed subscheme pushes forward to its class**, on Chow groups: for
`f : X ⟶ Y` proper over the base and a closed immersion `i : Z ⟶ X` with `i ≫ f` a closed
immersion, `f_*[Z ⊆ X]_k = [Z ⊆ Y]_k` in `A_k(Y)`. -/
theorem properChowPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp
    (C : ChowSituation.{u}) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX)
    (i : Z ⟶ X) [IsClosedImmersion i] [IsClosedImmersion (i ≫ f)] (k : ℤ) :
    properChowPushforward C sX sY f hf k
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sX sY f hf k)
        (QuotientAddGroup.mk' (rationalEquivalences C sX k)
          (cycleAssociatedToClosedSubscheme C sX i k)) =
      QuotientAddGroup.mk' (rationalEquivalences C sY k)
        (cycleAssociatedToClosedSubscheme C sY (i ≫ f) k) := by
  rw [properChowPushforward_mk,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp]

end Stacks.Chow

end
