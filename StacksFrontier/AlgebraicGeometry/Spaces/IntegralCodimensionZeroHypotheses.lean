module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericPointsFiniteComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedReduced

/-!
# Hypotheses (a), (b) and (c) of Stacks 0ENA for a locally Noetherian integral space

Stacks 0ENA, and with it every statement about `𝒦_X` and `𝒦_X(F)` that rests on it, is stated
under three hypotheses on the algebraic space `X`:

* (a) every weakly associated point of `X` has codimension `0`;
* (b) every quasi-compact open of every étale scheme chart of `X` has finitely many irreducible
  components, which is the condition of Stacks 0BB1;
* (c) every point of codimension `0` of `X` is represented by a monomorphism from the spectrum
  of a field.

Chapter 72's divisor theory, Stacks 0EPR to 0EQU, works instead under the standing hypothesis
that `X` is a *locally Noetherian integral* algebraic space. This file discharges all three
from that standing hypothesis, so that the conclusions of Stacks 0ENA are available there
without carrying them.

## Main results

* `AlgebraicGeometry.Space.forall_localRingDimension_eq_zero_of_isIntegralSpace` is hypothesis
  (a), from reducedness alone.
* hypothesis (b), from local Noetherianness alone, is Stacks 0GMB,
  `AlgebraicGeometry.Space.hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian` in
  `StacksFrontier.AlgebraicGeometry.Spaces.NormalizationFiniteness`, re-exported from here.
* `AlgebraicGeometry.Space.hasMonomorphicCodimensionZeroPoints_of_isDecentSpace` is hypothesis
  (c), from decency alone.

## Implementation notes

None of the three is new mathematics; each is an existing theorem read at the hypothesis the
divisor theory supplies, and the point of collecting them is that the consumers of Stacks 0ENA
carried all three as hypotheses and none of them derived any.

Hypothesis (a) is Stacks 0EN1,
`AlgebraicGeometry.Space.weaklyAssociatedPointsOfSpace_eq_setOf_localRingDimension_eq_zero`:
on a reduced algebraic space the weakly associated points are *exactly* the codimension-zero
points, so one inclusion of that equality is (a). Only reducedness is used, so the statement
below takes it rather than integrality; `AlgebraicGeometry.Space.IsIntegralSpace` supplies it
through its first component.

Hypothesis (b) is local Noetherianness transported to the charts by Stacks 03E8,
`AlgebraicGeometry.Space.exists_atlas_iff_forall_etale`, followed by
`AlgebraicGeometry.finite_irreducibleComponents_of_isCompact`: a quasi-compact open of a
locally Noetherian scheme is a Noetherian space. Integrality is not used.

Hypothesis (c) is `AlgebraicGeometry.Space.IsDecentSpace.hasMonomorphicFieldRepresentative`,
condition (4) of Stacks 03JU, at the codimension-zero points; it holds at *every* point of a
decent space, so the codimension hypothesis is discarded. This is the derivation
`AlgebraicGeometry.Space.IsDecentWithFinitelyManyComponents.hasMonomorphicCodimensionZeroPoints`
already makes from decency, restated so that it does not also demand finitely many components.

## References

* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
* [Stacks Project, Tag 0EN1](https://stacks.math.columbia.edu/tag/0EN1)
* [Stacks Project, Tag 0BB1](https://stacks.math.columbia.edu/tag/0BB1)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
* [Stacks Project, Tag 03JU](https://stacks.math.columbia.edu/tag/03JU)
* [Stacks Project, Tag 0AD4](https://stacks.math.columbia.edu/tag/0AD4)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Hypothesis (a) of Stacks 0ENA on a reduced algebraic space.** Every weakly associated
point of a reduced algebraic space has codimension `0`.

This is one inclusion of Stacks 0EN1, which identifies the weakly associated points of a
reduced algebraic space with its codimension-zero points. -/
theorem forall_localRingDimension_eq_zero_of_isReduced (X : AlgebraicSpaces B S hS)
    (hred : HasEtaleLocalProperty B S hS X.1 (fun Y : Scheme.{u} => IsReduced Y)) :
    ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0 := by
  intro z hz
  rw [weaklyAssociatedPointsOfSpace_eq_setOf_localRingDimension_eq_zero B S hS X hred] at hz
  exact hz

/-- **Hypothesis (a) of Stacks 0ENA on an integral algebraic space.** Every weakly associated
point of an integral algebraic space has codimension `0`, integrality including
reducedness. -/
theorem forall_localRingDimension_eq_zero_of_isIntegralSpace (X : AlgebraicSpaces B S hS)
    (hint : IsIntegralSpace B S hS X.1) :
    ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0 :=
  forall_localRingDimension_eq_zero_of_isReduced B S hS X
    (hint.hasEtaleLocalProperty_isReduced B S hS X.1)

/-- **Hypothesis (c) of Stacks 0ENA on a decent algebraic space.** Every point of codimension
`0` of a decent algebraic space is represented by a monomorphism from the spectrum of a field.

A decent algebraic space has such a representative at *every* point, which is condition (4) of
Stacks 03JU, so the codimension hypothesis is not used. -/
theorem hasMonomorphicCodimensionZeroPoints_of_isDecentSpace
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hdec : IsDecentSpace B S hS F) :
    HasMonomorphicCodimensionZeroPoints B S hS F :=
  fun x _ => IsDecentSpace.hasMonomorphicFieldRepresentative B S hS F hdec x

/-- **Hypothesis (c) of Stacks 0ENA on an integral algebraic space**, integrality including
decency. -/
theorem hasMonomorphicCodimensionZeroPoints_of_isIntegralSpace
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hint : IsIntegralSpace B S hS F) :
    HasMonomorphicCodimensionZeroPoints B S hS F :=
  hasMonomorphicCodimensionZeroPoints_of_isDecentSpace B S hS
    (hint.isDecentSpace B S hS F)

end AlgebraicGeometry.Space

end
