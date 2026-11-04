module

public import StacksFrontier.RingTheory.Smoothing.LiftingLemma.SmoothAtCriteria
public import StacksFrontier.RingTheory.Smoothing.LiftingLemma.SmoothAway
public import StacksFrontier.RingTheory.Smoothing.LiftingLemma.Charts
public import StacksFrontier.RingTheory.Smoothing.LiftingLemma.ExistsLift

/-!
# Lifting an algebra modulo the square of an element

A finitely presented algebra over `R / (π²)` which maps to `Λ / (π²)` can be
lifted, modulo `π`, to a finitely presented `R`-algebra.  The lift is smooth away
from `π`, and retains the smooth locus of the original algebra both over `R`
and relative to its reduction modulo `π`.

## Main definitions

There are no new definitions.

## Main results

* `exists_finitePresentation_lift_smoothAt` is the lifting lemma.

## Implementation notes

The three maps in the vertical direction are specified by their values on
quotient representatives.  This records that they are the canonical reduction
maps, rather than merely asking for an abstract commutative diagram.  A prime
of `D` containing `π` is regarded as a prime of `D / πD` using the image
under the quotient map.

## References

* [Stacks Project, Tag 07CP](https://stacks.math.columbia.edu/tag/07CP)
-/
