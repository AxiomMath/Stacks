module

public import StacksFrontier.RingTheory.Blowup.Defs

@[expose] public section

/-!
# Nonzerodivisors of `R` stay nonzerodivisors in the affine blowup algebra

Let `R` be a ring, `I ⊆ R` an ideal, `a : R`, and let `R[I/a] = affineBlowupAlgebra I a S` be the
affine blowup algebra realized inside a localization `S` of `R` away from `a`. This file proves
that the image of a nonzerodivisor `x` of `R` under the canonical map `R → R[I/a]` is again a
nonzerodivisor of `R[I/a]`.

This is the algebra fact behind [Stacks, Tag 085X]: it is applied there to the local equation `a`
of an effective Cartier divisor, which is a nonzerodivisor by hypothesis, to see that `a` remains
a nonzerodivisor in the affine blowup algebra of the chart of the blow-up attached to `a`.

## Main results

* `algebraMap_mem_nonZeroDivisors_affineBlowupAlgebra`: the statement above.

## Implementation notes

Every `z : S` satisfies `z * aⁿ = y` in `S`, for some `n : ℕ` and `y : R` (`IsLocalization.
Away.surj`), since `S` is a localization away from `a`. Given `z * x = 0` in `R[I/a]`,
multiplying by `aⁿ` and substituting turns this into `x * y = 0` in `R`, so `x * y` dies in `S`;
since `S` is a localization away from `a`, this means `aᵏ · (x * y) = 0` in `R` for some `k`.
Cancelling the nonzerodivisor `x` gives `aᵏ · y = 0`, hence `aᵏ⁺ⁿ · z = 0` in `S`, and `aᵏ⁺ⁿ` is a
unit there, so `z = 0`.

No relation between `a` and `I` is used, matching `affineBlowupAlgebra` itself.

## References

* [Stacks Project, Tag 085X](https://stacks.math.columbia.edu/tag/085X)
-/

variable {R : Type*} [CommRing R]

/-- **A nonzerodivisor of `R` stays a nonzerodivisor in the affine blowup algebra `R[I/a]`.**
This is the algebra fact used in [Stacks, Tag 085X]. -/
theorem algebraMap_mem_nonZeroDivisors_affineBlowupAlgebra (I : Ideal R) (a : R) (S : Type*)
    [CommRing S] [Algebra R S] [IsLocalization.Away a S] {x : R} (hx : x ∈ nonZeroDivisors R) :
    algebraMap R (affineBlowupAlgebra I a S) x ∈ nonZeroDivisors (affineBlowupAlgebra I a S) := by
  rw [mem_nonZeroDivisors_iff_right]
  rintro ⟨z, hz⟩ hz0
  have hz0' : z * algebraMap R S x = 0 := congrArg Subtype.val hz0
  obtain ⟨n, y, hny⟩ := IsLocalization.Away.surj a z
  -- `hny : z * algebraMap a ^ n = algebraMap y`
  have h2 : algebraMap R S y * algebraMap R S x = 0 := by
    rw [← hny, mul_right_comm, hz0', zero_mul]
  have h3 : algebraMap R S (y * x) = 0 := by rw [map_mul]; exact h2
  obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers a) S (y * x)).mp h3
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff (m : R) a).mp m.2
  have h4 : a ^ k * y * x = 0 := by rw [mul_assoc, hk]; exact hm
  have h5 : a ^ k * y = 0 := mem_nonZeroDivisors_iff_right.mp hx _ h4
  have h6 : algebraMap R S a ^ (k + n) * z = 0 := by
    have e : algebraMap R S a ^ (k + n) * z =
        algebraMap R S a ^ k * (z * algebraMap R S a ^ n) := by ring
    rw [e, hny, ← map_pow, ← map_mul, h5, map_zero]
  exact Subtype.ext ((IsLocalization.Away.algebraMap_pow_isUnit a (k + n)).mul_right_eq_zero.mp h6)
