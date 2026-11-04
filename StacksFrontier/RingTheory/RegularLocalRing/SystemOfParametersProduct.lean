module

public import StacksFrontier.RingTheory.RegularLocalRing.RegularParameterFactorization

/-!
# Products of regular parameters are nonzerodivisors

Let `(R, 𝔪)` be a regular local ring and let `h₁, …, h_d` be a regular system of parameters of
`R`, that is, a system of parameters generating `𝔪`. Every entry of such a list is a prime
element, so in particular nonzero, and a regular local ring is a domain. The product of any
initial segment `h₁ ⋯ h_s` is therefore a nonzerodivisor.

## Main results

* `IsRegularLocalRing.mem_nonZeroDivisors_prod_take_of_ofList_eq_maximalIdeal`: the product of an
  initial segment of a regular system of parameters is a nonzerodivisor.

## Implementation notes

A regular system of parameters is the conjunction `IsLocalRing.IsSystemOfParameters rs ∧
Ideal.ofList rs = IsLocalRing.maximalIdeal R`, so both conjuncts are carried explicitly. The
primality of the entries is `IsRegularLocalRing.prime_of_mem_of_ofList_eq_maximalIdeal`, whose
length hypothesis is stated against `Submodule.spanFinrank` of the maximal ideal rather than
against the Krull dimension; the two agree for a regular local ring by Stacks 00NN, which is how
the hypothesis is discharged here.

No bound relating `s` to the length of the list is needed: `List.take` truncates, and the empty
product `1` is a nonzerodivisor as well.

## References

* [StacksProject 00NN](https://stacks.math.columbia.edu/tag/00NN), the minimal number of
  generators of the maximal ideal of a regular local ring is its dimension
* [StacksProject 00NQ](https://stacks.math.columbia.edu/tag/00NQ), the initial quotients of a
  regular system of parameters
-/

@[expose] public section

universe u

namespace IsRegularLocalRing

/-- **The product of an initial segment of a regular system of parameters is a nonzerodivisor.**
Let `h₁, …, h_d` be a system of parameters of a regular local ring `R` generating the maximal
ideal. Then `h₁ ⋯ h_s` is a nonzerodivisor for every `s`. -/
theorem mem_nonZeroDivisors_prod_take_of_ofList_eq_maximalIdeal {R : Type u} [CommRing R]
    [IsRegularLocalRing R] {rs : List R} (hsop : IsLocalRing.IsSystemOfParameters rs)
    (hgen : Ideal.ofList rs = IsLocalRing.maximalIdeal R) (s : ℕ) :
    (rs.take s).prod ∈ nonZeroDivisors R := by
  have : IsDomain R := IsRegularLocalRing.isDomain R
  -- For a regular local ring the length of a system of parameters is the embedding dimension.
  have hlen : rs.length = (IsLocalRing.maximalIdeal R).spanFinrank := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    rw [hsop.2] at h
    exact_mod_cast h.symm
  have hprime : ∀ t ∈ rs.take s, Prime t := fun t ht ↦
    prime_of_mem_of_ofList_eq_maximalIdeal hgen hlen (List.mem_of_mem_take ht)
  exact mem_nonZeroDivisors_of_ne_zero
    (List.prod_ne_zero fun h0 ↦ (hprime 0 h0).ne_zero rfl)

end IsRegularLocalRing

end
