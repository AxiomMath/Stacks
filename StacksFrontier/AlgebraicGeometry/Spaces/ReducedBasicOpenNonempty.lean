module

public import Mathlib.AlgebraicGeometry.Properties

/-!
# The non-vanishing locus of a nonzero function on a reduced scheme

On a reduced scheme a global regular function whose non-vanishing locus is empty is zero, so
a nonzero function has a nonempty non-vanishing locus. Mathlib has the two halves of this —
`AlgebraicGeometry.eq_zero_of_basicOpen_eq_bot` and
`TopologicalSpace.Opens.not_nonempty_iff_eq_bot` — but not the combination, which several
files in the algebraic-spaces development need.

This is a statement about schemes alone; it lives in `AlgebraicGeometry` rather than
`AlgebraicGeometry.Space`, and in a module of its own so that the files needing it do not
have to import each other's closures to get it.
-/

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The non-vanishing locus of a nonzero global regular function on a reduced scheme is
nonempty. -/
public theorem nonempty_basicOpen_of_ne_zero (Y : Scheme.{u}) [IsReduced Y] {r : Γ(Y, ⊤)}
    (hr : r ≠ 0) : ((Y.basicOpen r : Y.Opens) : Set Y).Nonempty := by
  by_contra hn
  exact hr (eq_zero_of_basicOpen_eq_bot r ((Opens.not_nonempty_iff_eq_bot _).mp hn))

end AlgebraicGeometry

end
