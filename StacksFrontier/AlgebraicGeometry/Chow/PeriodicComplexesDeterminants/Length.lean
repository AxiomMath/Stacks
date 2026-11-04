module

public import Mathlib.RingTheory.Length
public import StacksCore.Tactic.StacksAttribute

/-!
# Length of an exact one-differential periodic complex

An exact periodic complex built from a single module and a single repeated differential has
length twice the length of the image of that differential.

## Main results

* `Module.length_eq_twice_image_length` computes the length of the module of an exact periodic
  complex with a single repeated differential.

## Implementation notes

The exact `(2, 1)`-periodic complex `(M, φ, φ)` is expressed by `Function.Exact φ φ`. Since
`Module.length` takes values in `ℕ∞`, the equality remains valid without assuming that the
length is finite. Neither commutativity nor locality of the ring is needed.

## References

* [Stacks Project, Tag 02PM](https://stacks.math.columbia.edu/tag/02PM)
-/

@[expose] public section

namespace Module

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- **Stacks Project, Tag 02PM.** The length of an exact one-differential periodic complex is
twice the length of the image of its differential. -/
@[stacks 02PM "length_eq_twice_image_length"]
lemma length_eq_twice_image_length (φ : M →ₗ[R] M) (hφ : Function.Exact φ φ) :
    Module.length R M = 2 * Module.length R (LinearMap.range φ) := by
  rw [Module.length_eq_add_of_exact (LinearMap.ker φ).subtype φ.rangeRestrict
    (Submodule.subtype_injective _) (LinearMap.surjective_rangeRestrict φ)
    (by rw [LinearMap.exact_iff]; simp), ← hφ.linearMap_ker_eq, two_mul]

end Module
