module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import StacksCore.Tactic.StacksAttribute

/-!
# \(C_r\) fields

A field is a \(C_r\) field when every homogeneous polynomial of degree `d` in `n` variables
has a nontrivial zero, for every `d` and `n` with `0 < d` and `d ^ r < n`. Finite fields and, more
generally, quasi-algebraically closed fields are the case `r = 1`; the condition weakens as `r`
grows.

## Main definitions

* `IsCField` is the predicate that a field is a \(C_r\) field.

## Implementation notes

The variables of a polynomial are indexed by `Fin n`, and a nontrivial solution is represented
by a function `Fin n → K` which is not the zero function. The condition is stated in the
namespace of fields rather than of schemes, since nothing geometric enters it.

## References

* [Stacks Project, Tag 03R9](https://stacks.math.columbia.edu/tag/03R9)
-/

@[expose] public section

/-- A field `K` is a \(C_r\) field if every homogeneous polynomial of degree
`d ≥ 1` in `n` variables has a nonzero solution when `d ^ r < n`.

The degree bound is `0 < d`, not `0 < d ^ r`. The two agree for every `r ≥ 1`, but at `r = 0`
they do not: `d ^ 0 = 1` even for `d = 0`, so `0 < d ^ r` is satisfied by the constant
polynomial `1`, which is homogeneous of degree `0` and has no nonzero root. With that spelling
`IsCField K 0` is false for every field, which is not what \(C_0\) means. -/
@[stacks 03R9,
  sga "4½ Arcata 3.2.1" "more general"]
abbrev IsCField (K : Type*) [Field K] (r : ℕ) : Prop :=
  ∀ (d n : ℕ), (0 < d ∧ d ^ r < n) → ∀ f : MvPolynomial (Fin n) K,
    f.IsHomogeneous d → ∃ α : Fin n → K, α ≠ 0 ∧ MvPolynomial.eval α f = 0
