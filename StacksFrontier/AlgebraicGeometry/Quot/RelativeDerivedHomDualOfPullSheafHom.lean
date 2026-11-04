module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeDerivedHomDual
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeDerivedHomDualNaturality

/-!
# Stacks 0DKY from its inputs and Stacks 08JF

The proof of Stacks 0DKY is assembled here from its internal steps: the window and the fibre test
(`AlgebraicGeometry.Space.relativeDerivedHomDualExistsNaturalCompatible_of_steps'`), the
naturality step (`AlgebraicGeometry.Space.relativeDerivedHomDualNaturality_of_pullSheafHom`) and
the isomorphism of inverse systems of Stacks 08JF
(`AlgebraicGeometry.Space.pullSheafHomPerfectSystemIso_of_pullSheafHomComparisonIsIso`). The
result is conditional on Stacks 0DKB, 0DKX and 0DKS (2), and on the invertibility of the map of
Stacks 08JF for perfect sources (`AlgebraicGeometry.Space.PullSheafHomComparisonIsIso`), all taken
as hypotheses.

## Main results

* `AlgebraicGeometry.Space.relativeDerivedHomDualExistsNaturalCompatible`.

## References

* [Stacks Project, Tag 0DKY](https://stacks.math.columbia.edu/tag/0DKY)
* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0DKY, from its inputs and Stacks 08JF**: granted Stacks 0DKB, Stacks 0DKX,
Stacks 0DKS (2) and the invertibility of the map of Stacks 08JF for perfect sources, the natural
and compatible form of Stacks 0DKY,
`AlgebraicGeometry.Space.RelativeDerivedHomDualExistsNaturalCompatible`, holds. -/
theorem relativeDerivedHomDualExistsNaturalCompatible
    (h0DKB : PseudoCoherentHomotopyColimitApproximation B S hS)
    (h0DKX : RelativelyPerfectPushforwardBaseChange B S hS)
    (h0DKS : TensorPerfectRelativelyPerfect B S hS)
    (hH : PullSheafHomComparisonIsIso B S hS) :
    RelativeDerivedHomDualExistsNaturalCompatible B S hS :=
  relativeDerivedHomDualExistsNaturalCompatible_of_steps' B S hS h0DKB h0DKX h0DKS
    (relativeDerivedHomDualNaturality_of_pullSheafHom B S hS hH)
    (pullSheafHomPerfectSystemIso_of_pullSheafHomComparisonIsIso B S hS hH)

end AlgebraicGeometry.Space
