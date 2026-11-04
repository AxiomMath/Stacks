module

public import Mathlib.RingTheory.DividedPowers.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Nilpotent.Ideal

/-!
# Nilpotence of a divided power ideal

Let `p` be a prime number, let `I` be an ideal of a commutative ring `A` carrying a divided
power structure `γ`, and assume that `p` is nilpotent in `A ⧸ I`. Under these hypotheses the
local nilpotence of `I` — every element of `I` is nilpotent — is equivalent to the nilpotence
of `p` in `A`.

If `pᴺ = 0` in `A`, then multiplication by the natural number `pᴺ` kills `I`, and the factorial
identity `n ! · γₙ(x) = xⁿ` forces `x ^ pᴺ = 0` for every `x ∈ I`. Conversely, nilpotence of `p`
in `A ⧸ I` says that `pʳ ∈ I` for some `r`, so local nilpotence of `I` makes `pʳ`, and hence `p`,
nilpotent in `A`.

## Main results

* `DividedPowers.locallyNilpotent_iff_isNilpotent_natCast` — for a divided power ideal `I` with
  `p` nilpotent in `A ⧸ I`, the ideal `I` is locally nilpotent if and only if `p` is nilpotent
  in `A`.

## Implementation notes

The direction producing nilpotence of the elements of `I` is Mathlib's
`DividedPowers.nilpotent_of_mem_dpIdeal`, which turns the vanishing of `n • y` on a divided
power ideal into `y ^ n = 0`; here `n = pᴺ`. Local nilpotence of an ideal is the repository's
`Ideal.LocallyNilpotent`.

## References

* [Stacks Project, Tag 07GR](https://stacks.math.columbia.edu/tag/07GR)
-/

@[expose] public section

namespace DividedPowers

/-- Let `p` be a prime number, let `γ` be a divided power structure on an ideal `I` of a
commutative ring `A`, and assume `p` is nilpotent in `A ⧸ I`. Then `I` is locally nilpotent,
i.e. every element of `I` is nilpotent, if and only if `p` is nilpotent in `A`. -/
@[stacks 07GR]
public theorem locallyNilpotent_iff_isNilpotent_natCast {A : Type*} [CommRing A] {p : ℕ}
    (hp : p.Prime) {I : Ideal A} (γ : DividedPowers I) (hpI : IsNilpotent (p : A ⧸ I)) :
    I.LocallyNilpotent ↔ IsNilpotent (p : A) := by
  constructor
  · intro hI
    obtain ⟨r, hr⟩ := hpI
    have hmem : (p : A) ^ r ∈ I := by
      rwa [← Ideal.Quotient.eq_zero_iff_mem, map_pow, map_natCast]
    exact (hI _ hmem).of_pow
  · rintro ⟨N, hN⟩ x hx
    refine ⟨p ^ N, nilpotent_of_mem_dpIdeal (pow_ne_zero N hp.pos.ne') ?_ γ hx⟩
    intro y _
    rw [nsmul_eq_mul, Nat.cast_pow, hN, zero_mul]

end DividedPowers

end
