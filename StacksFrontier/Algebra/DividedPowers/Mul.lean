module

public import Mathlib.RingTheory.DividedPowers.Basic

/-!
# Two divided power structures agree on the product of their ideals

Let `I` and `J` be ideals of a commutative ring `A`, carrying divided power structures `γ` and
`δ`. The product ideal `I * J` is contained in both, so both structures are defined on it, and
they agree there. The reason is the factorial identity `n ! · γₙ(x) = xⁿ`, valid in every divided
power structure: for `x ∈ I` and `y ∈ J` the two candidate values of the `n`th divided power of
`x y` are `yⁿ · γₙ(x)` and `xⁿ · δₙ(y)`, and substituting the factorial identity for `xⁿ` in the
first and for `yⁿ` in the second turns both into `n ! · γₙ(x) · δₙ(y)`. The addition law then
propagates the agreement from the generators `x y` of `I * J` to all of `I * J`.

This is the side condition of `DividedPowers.existsUnique_on_ideal_add` (Stacks 07GQ(2)) in the
frequent situation where the two ideals meet in their product.

## Main results

* `DividedPowers.dpow_eq_of_mem_mul` — two divided power structures agree on the product of
  their ideals.
* `DividedPowers.dpow_eq_of_mem_inf_of_inf_le_mul` — the resulting side condition for gluing
  divided powers along `DividedPowers.existsUnique_on_ideal_add`.

## References

* [Stacks Project, Tag 07GQ](https://stacks.math.columbia.edu/tag/07GQ)
* [Stacks Project, Tag 07H5](https://stacks.math.columbia.edu/tag/07H5)
-/

@[expose] public section

namespace DividedPowers

/-- Two divided power structures on ideals `I` and `J` of a commutative ring agree on the
product ideal `I * J`. -/
public theorem dpow_eq_of_mem_mul {A : Type*} [CommRing A] {I J : Ideal A}
    (γ : DividedPowers I) (δ : DividedPowers J) {z : A} (hz : z ∈ I * J) (n : ℕ) :
    γ.dpow n z = δ.dpow n z := by
  have hsubI : I * J ≤ I := by rw [mul_comm]; exact Ideal.mul_le_right
  have hsubJ : I * J ≤ J := Ideal.mul_le_right
  revert n
  induction hz using Submodule.mul_induction_on' with
  | mem_mul_mem x hx y hy =>
      intro n
      rw [mul_comm x y, γ.dpow_mul hx, mul_comm y x, δ.dpow_mul hy,
        ← γ.factorial_mul_dpow_eq_pow hx, ← δ.factorial_mul_dpow_eq_pow hy]
      ring
  | add x hx y hy ihx ihy =>
      intro n
      rw [γ.dpow_add (hsubI hx) (hsubI hy), δ.dpow_add (hsubJ hx) (hsubJ hy)]
      exact Finset.sum_congr rfl fun k _ ↦ by rw [ihx, ihy]

/-- If the ideals `I` and `J` meet in their product, then divided power structures on them agree
on the intersection, which is the side condition of
`DividedPowers.existsUnique_on_ideal_add`. -/
public theorem dpow_eq_of_mem_inf_of_inf_le_mul {A : Type*} [CommRing A] {I J : Ideal A}
    (γ : DividedPowers I) (δ : DividedPowers J) (hIJ : I ⊓ J ≤ I * J) (n : ℕ) {x : A}
    (hx : x ∈ I ⊓ J) : γ.dpow n x = δ.dpow n x :=
  dpow_eq_of_mem_mul γ δ (hIJ hx) n

end DividedPowers

end
