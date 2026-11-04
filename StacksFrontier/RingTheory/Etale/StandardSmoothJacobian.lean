module

public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import StacksCore.Tactic.StacksAttribute

/-!
# Étale ring maps are exactly the standard ones with invertible Jacobian (Stacks 03PC (3))

Clause (3) of Stacks 03PC characterizes étale ring maps `A → B` as those presenting `B` as
`A[x_1, …, x_n]/(f_1, …, f_n)` with invertible Jacobian determinant; this is Mathlib's
`Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`, which this file registers.

## References

* [StacksProject 03PC](https://stacks.math.columbia.edu/tag/03PC)
-/

@[expose] public section

-- Clause (3) of Stacks 03PC is this same equivalence: a ring map `A → B` is étale if and only if
-- `B` is `A[x_1, …, x_n]/(f_1, …, f_n)` with the Jacobian determinant `det (∂f_i/∂x_j)`
-- invertible in `B`. That is what `Algebra.IsStandardSmoothOfRelativeDimension 0` says. It
-- asserts a finite `Algebra.SubmersivePresentation`, whose `jacobian_isUnit` field is
-- invertibility of the determinant of `(∂f_i/∂x_{map i})`, with `dimension = 0`. Since `map` is
-- injective, there are at most as many relations as variables, so vanishing of the truncated
-- difference of the two cardinalities forces them to be equal and `map` to be a bijection. The
-- system is therefore square, and the determinant is the full Jacobian up to a relabelling of
-- the columns, which does not affect invertibility. Unlike 00U9, which the source states as the
-- forward implication alone, clause (3) is the equivalence, so it is recorded on the `iff`.
add_to_stacks 03PC "jacobian"
  Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero

