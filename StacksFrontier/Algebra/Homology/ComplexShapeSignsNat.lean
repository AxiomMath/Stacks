module

public import Mathlib.Algebra.Homology.ComplexShapeSigns

/-!
# The Koszul signs of a nonnegatively graded cochain complex

Mathlib's `ComplexShape.TensorSigns` carries the signs with which the total complex of a double
complex is formed, and Mathlib provides it for `ComplexShape.up ℤ`. This module provides it for
`ComplexShape.up ℕ`, with the same convention `ε p = (-1)^p`. Through
`ComplexShape.instTotalComplexShape` this gives `TotalComplexShape (up ℕ) (up ℕ) (up ℕ)`, the
shape of the total complex of a tensor product of two `ℕ`-indexed cochain complexes.

## References

* [Stacks Project, Tag 012Z](https://stacks.math.columbia.edu/tag/012Z), the sign convention
-/

@[expose] public section

/-- The Koszul signs `ε p = (-1)^p` for the shape `ComplexShape.up ℕ` of nonnegatively graded
cochain complexes. -/
instance : ComplexShape.TensorSigns (ComplexShape.up ℕ) where
  ε' := MonoidHom.mk' (fun i : Multiplicative ℕ => (-1 : ℤˣ) ^ i.toAdd) (pow_add (-1 : ℤˣ))
  rel_add p q r (hpq : p + 1 = q) := by
    change p + r + 1 = q + r
    lia
  add_rel p q r (hpq : p + 1 = q) := by
    change r + p + 1 = r + q
    lia
  ε'_succ := by
    rintro p _ rfl
    change (-1 : ℤˣ) ^ (p + 1) = -((-1 : ℤˣ) ^ p)
    simp [pow_succ, mul_comm]

end
