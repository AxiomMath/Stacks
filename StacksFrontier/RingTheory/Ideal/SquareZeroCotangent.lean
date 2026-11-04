module

public import Mathlib.RingTheory.Ideal.Cotangent

/-!
# The cotangent module of a square-zero ideal is the ideal itself

For an ideal `I` of a commutative ring with `I ^ 2 = ⊥` the quotient map
`Ideal.toCotangent : I →ₗ[R] I.Cotangent` onto `I/I²` is injective as well as surjective, so
`I/I²` *is* `I`.

Combined with [Stacks Project, Tag 01R3] part (2) — the sections of the conormal sheaf over an
affine open are `I/I²` — this identifies those sections with the defining ideal itself when the
immersion is a first-order thickening.

## Main definitions

* `Ideal.toCotangentEquivOfSqZero` is `Ideal.toCotangent` as a linear equivalence
  `I ≃ₗ[R] I.Cotangent`, for `I ^ 2 = ⊥`.

## Main results

* `Ideal.toCotangent_injective_of_sqZero`: `Ideal.toCotangent` is injective when `I ^ 2 = ⊥`.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

universe u

namespace Ideal

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- **`Ideal.toCotangent` is injective on a square-zero ideal.** A class in `I/I²` vanishes
exactly when its representative lies in `I²`, which is `⊥`. -/
theorem toCotangent_injective_of_sqZero (hI : I ^ 2 = ⊥) :
    Function.Injective I.toCotangent := by
  intro x y hxy
  have h : (x - y : R) ∈ I ^ 2 := I.toCotangent_eq.mp hxy
  rw [hI, Ideal.mem_bot, sub_eq_zero] at h
  exact Subtype.ext h

/-- **The cotangent module of a square-zero ideal is the ideal.** `Ideal.toCotangent` is
surjective always and injective here, so it is a linear equivalence `I ≃ₗ[R] I/I²`. -/
noncomputable def toCotangentEquivOfSqZero (hI : I ^ 2 = ⊥) : I ≃ₗ[R] I.Cotangent :=
  LinearEquiv.ofBijective I.toCotangent
    ⟨I.toCotangent_injective_of_sqZero hI, I.toCotangent_surjective⟩

/-- The equivalence `Ideal.toCotangentEquivOfSqZero` sends `x ∈ I` to its class
`Ideal.toCotangent x` in `I/I²`. -/
@[simp]
theorem toCotangentEquivOfSqZero_apply (hI : I ^ 2 = ⊥) (x : I) :
    I.toCotangentEquivOfSqZero hI x = I.toCotangent x := rfl

end Ideal

end
