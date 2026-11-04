module

public import StacksFrontier.AlgebraicGeometry.Chow.PreparationTameSymbols.Preparation
public import StacksFrontier.RingTheory.Localization.Glueing.RingHomGluing.MaximalIdealGluing

/-!
# The glueing input of the tame-symbol preparation

`AlgebraicGeometry.RingHomGluingAtMaximalIdeals` is one of the two ring-theoretic inputs that the
tame-symbol preparation consumes as a hypothesis. This file discharges it from the glueing theorem
proved for arbitrary universes, specialized to the all-universes-equal instance.

## Main results

* `AlgebraicGeometry.ringHomGluingAtMaximalIdeals` proves
  `AlgebraicGeometry.RingHomGluingAtMaximalIdeals`.

## Implementation notes

The glueing theorem produces its ring in `Type (max u v w)` for a base ring in `Type u`, target
rings in `Type v` and an index type in `Type w`. The predicate asks for all three to be the same
universe, where that maximum is that universe, so the specialization is the identity on the
statement.

## References

* [Stacks Project, Tag 0EAE](https://stacks.math.columbia.edu/tag/0EAE)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- The glueing of ring maps over the localizations at finitely many maximal ideals, in the
all-universes-equal instance consumed by the tame-symbol preparation. -/
theorem ringHomGluingAtMaximalIdeals : RingHomGluingAtMaximalIdeals.{u} := by
  intro _ _ _ _ _ m _ B _ hm f hker hcoker
  exact Stacks.RingHomGluing.exists_ringHom_inducing_at_maximal_ideal m B hm f hker hcoker

end AlgebraicGeometry

end
