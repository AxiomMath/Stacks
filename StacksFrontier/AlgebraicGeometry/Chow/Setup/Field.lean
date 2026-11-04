module

public import Mathlib.AlgebraicGeometry.Scheme
public import StacksCore.Tactic.StacksAttribute

/-!
# The base dimension function over a field

For a field `k`, the base dimension function on the spectrum of `k` is the constant
integer-valued function with value zero.

## Main definitions

* `AlgebraicGeometry.fieldBaseDimensionFunction` is the constant-zero function on `Spec(k)`.

## Implementation notes

The underlying type of `AlgebraicGeometry.Spec (.of k)` is definitionally the prime spectrum
of `k`. The construction is an abbreviation so that clients can use the existing API for the
zero function directly.

## References

* [Stacks Project, Tag 02QM](https://stacks.math.columbia.edu/tag/02QM)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- The base dimension function on the spectrum of a field, taking every point to zero. -/
@[stacks 02QM "field_base_dimension_function"]
abbrev fieldBaseDimensionFunction (k : Type u) [Field k] :
    AlgebraicGeometry.Spec (.of k) → ℤ := fun _ => 0

end AlgebraicGeometry
