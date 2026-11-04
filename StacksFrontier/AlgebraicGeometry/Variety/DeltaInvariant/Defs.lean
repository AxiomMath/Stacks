module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.FractionRing
public import StacksCore.Tactic.StacksAttribute

/-!
# The delta invariant of a ring

The delta invariant of a reduced one-dimensional Nagata local ring is the length of the
quotient of its integral closure in its total ring of fractions by the original ring.

## Main definitions

* `Ring.deltaInvariant`: the length of this quotient, defined for every commutative ring.

## References

* [Stacks Project, Tag 0C3T](https://stacks.math.columbia.edu/tag/0C3T)
-/

@[expose] public section

/-- The delta invariant of a commutative ring is the length of the quotient of its integral
closure in its total ring of fractions by the image of the ring.  For a reduced
one-dimensional Nagata local ring, this quotient has finite length. -/
@[stacks 0C3T,
  stacks 0C1T "the invariant of a scheme at a point, as the invariant of the local ring there",
  sga "7 X 2.10"]
public noncomputable abbrev Ring.deltaInvariant (A : Type*) [CommRing A] : ℕ∞ :=
  Module.length A (↥(integralClosure A (FractionRing A)) ⧸
    LinearMap.range (Algebra.linearMap A ↥(integralClosure A (FractionRing A))))
