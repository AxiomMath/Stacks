module

public import StacksFrontier.AlgebraicGeometry.Curves.MulticrossNormalization
public import StacksFrontier.AlgebraicGeometry.Curves.Node
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.RingEquivTransport
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The delta invariant of a nodal power-series hypersurface

The delta invariant of `k[[x, y]]/(q)` for a nondegenerate binary quadratic form `q` is `1`.

## Main results

* `Stacks.Curves.deltaInvariant_quotient_nodalBinaryQuadratic_of_isotropic` computes the delta
  invariant of the hypersurface of a nondegenerate binary quadratic form that has a nontrivial
  zero, over an arbitrary field.
* `Stacks.Curves.deltaInvariant_quotient_nodalBinaryQuadratic` is the same statement over an
  algebraically closed field.

## Implementation notes

`Stacks.Curves.deltaInvariant_multicross` computes the delta invariant of the two-branch
multicross ring, which is the hypersurface only up to isomorphism of `k`-algebras.  Carrying the
value across that isomorphism is `Ring.deltaInvariant_eq_of_ringEquiv`: the delta invariant
compares modules over the ring itself, so its invariance under isomorphism is a statement about
a change of base ring and not a formal consequence of transporting the integral closure.

## References

* [Stacks Project, Tag 0C4A](https://stacks.math.columbia.edu/tag/0C4A)
-/

@[expose] public section

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k]

/-- **The delta invariant of a nodal power-series hypersurface is `1`**, for a nondegenerate
binary quadratic form with a nontrivial zero over an arbitrary field.  This is the first
numerical read-off of Case I of the proof of Stacks Tag 0C4A, stated for the hypersurface rather
than for the multicross ring it is isomorphic to. -/
@[sga "7 X 2.24" "more general"]
theorem deltaInvariant_quotient_nodalBinaryQuadratic_of_isotropic
    (a b c : k) (h : 4 * a * c - b ^ 2 ≠ 0)
    (hsplit : ∃ u v : k, (u ≠ 0 ∨ v ≠ 0) ∧ a * u ^ 2 + b * u * v + c * v ^ 2 = 0) :
    Ring.deltaInvariant
        (MvPowerSeries (Fin 2) k ⧸ Ideal.span {nodalBinaryQuadratic a b c}) = 1 := by
  obtain ⟨e⟩ := nonempty_algEquiv_multicross_of_isotropic a b c h hsplit
  rw [Ring.deltaInvariant_eq_of_ringEquiv _ _ e.toRingEquiv]
  exact deltaInvariant_multicross

/-- **The delta invariant of a nodal power-series hypersurface over an algebraically closed field
is `1`.** Over such a field every nondegenerate binary quadratic form has a nontrivial zero. -/
@[sga "7 X 2.24" "more general"]
theorem deltaInvariant_quotient_nodalBinaryQuadratic [IsAlgClosed k]
    (a b c : k) (h : 4 * a * c - b ^ 2 ≠ 0) :
    Ring.deltaInvariant
        (MvPowerSeries (Fin 2) k ⧸ Ideal.span {nodalBinaryQuadratic a b c}) = 1 := by
  obtain ⟨e⟩ := nonempty_algEquiv_multicross_of_nondegenerate a b c h
  rw [Ring.deltaInvariant_eq_of_ringEquiv _ _ e.toRingEquiv]
  exact deltaInvariant_multicross

end Stacks.Curves
