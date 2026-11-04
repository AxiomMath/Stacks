module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.Data.Nat.Prime.Int

/-!
# Associated primes of the quotient by a power of a nonzerodivisor

Let `A` be a commutative ring and let `f ∈ A` be a nonzerodivisor. Then the associated primes
of `A ⧸ fⁿA` do not depend on `n ≥ 1`:

`Ass(A ⧸ fⁿA) = Ass(A ⧸ fA)`.

Both inclusions come from the short exact sequence `0 → A ⧸ fⁿA → A ⧸ fⁿ⁺¹A → A ⧸ fA → 0`,
whose first map is multiplication by `f`. Downwards it is additivity of `Ass` along a short
exact sequence together with induction on `n`; upwards it is the injection `A ⧸ fA → A ⧸ fⁿ⁺¹A`
given by multiplication by `fⁿ`.

## Main definitions

* `Stacks.RingTheory.AssociatedPrimes.mulSelfQuotPow` — multiplication by `f`, as a map
  `A ⧸ fⁿ⁺¹A → A ⧸ fⁿ⁺²A`.
* `Stacks.RingTheory.AssociatedPrimes.quotPowProj` — the projection `A ⧸ fⁿ⁺²A → A ⧸ fA`.
* `Stacks.RingTheory.AssociatedPrimes.mulPowQuot` — multiplication by `fᵐ`, as a map
  `A ⧸ fA → A ⧸ fᵐ⁺¹A`.

## Main results

* `Stacks.RingTheory.AssociatedPrimes.exact_mulSelfQuotPow_quotPowProj` — the sequence
  `0 → A ⧸ fⁿ⁺¹A → A ⧸ fⁿ⁺²A → A ⧸ fA → 0` is exact at its middle term, and its first map is
  injective by `mulSelfQuotPow_injective`.
* `Stacks.RingTheory.AssociatedPrimes.associatedPrimes_quotient_span_singleton_pow_succ` —
  `Ass(A ⧸ fⁿ⁺¹A) = Ass(A ⧸ fA)`.
* `Stacks.RingTheory.AssociatedPrimes.associatedPrimes_quotient_span_singleton_pow_succ'` — the
  same statement written with the ideal power `(fA)ⁿ⁺¹` in place of `fⁿ⁺¹A`.

## Implementation notes

No Noetherian hypothesis is needed. The exponent is written `n + 1` rather than carried with a
side condition `n ≠ 0`, which is what makes the induction step `A ⧸ fⁿ⁺¹A → A ⧸ fⁿ⁺²A` typecheck
without rewriting the exponent.

## References

* [Stacks Project, Tag 0DXU](https://stacks.math.columbia.edu/tag/0DXU)
* [Stacks Project, Tag 02M3](https://stacks.math.columbia.edu/tag/02M3)
-/

@[expose] public section

universe u

namespace Stacks.RingTheory.AssociatedPrimes

variable {A : Type u} [CommRing A] {f : A}

/-- Multiplication by `f`, as an `A`-linear map `A ⧸ fⁿ⁺¹A → A ⧸ fⁿ⁺²A`. -/
noncomputable def mulSelfQuotPow (f : A) (n : ℕ) :
    (A ⧸ Ideal.span {f ^ (n + 1)}) →ₗ[A] (A ⧸ Ideal.span {f ^ (n + 2)}) :=
  Submodule.mapQ _ _ (LinearMap.lsmul A A f) (by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hx
    rw [Submodule.mem_comap, LinearMap.lsmul_apply, smul_eq_mul, Ideal.mem_span_singleton]
    exact ⟨c, by ring⟩)

/-- The projection `A ⧸ fⁿ⁺²A → A ⧸ fA`. -/
noncomputable def quotPowProj (f : A) (n : ℕ) :
    (A ⧸ Ideal.span {f ^ (n + 2)}) →ₗ[A] (A ⧸ Ideal.span {f}) :=
  Submodule.mapQ _ _ LinearMap.id (by
    intro x hx
    rw [Submodule.mem_comap, LinearMap.id_apply, Ideal.mem_span_singleton]
    exact dvd_trans (dvd_pow_self f (by omega)) (Ideal.mem_span_singleton.mp hx))

/-- Multiplication by `fᵐ`, as an `A`-linear map `A ⧸ fA → A ⧸ fᵐ⁺¹A`. -/
noncomputable def mulPowQuot (f : A) (m : ℕ) :
    (A ⧸ Ideal.span {f}) →ₗ[A] (A ⧸ Ideal.span {f ^ (m + 1)}) :=
  Submodule.mapQ _ _ (LinearMap.lsmul A A (f ^ m)) (by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hx
    rw [Submodule.mem_comap, LinearMap.lsmul_apply, smul_eq_mul, Ideal.mem_span_singleton]
    exact ⟨c, by ring⟩)

/-- If `g` is a nonzerodivisor and `g * x` vanishes in `A ⧸ bA` with `b = g * a`, then `x`
vanishes in `A ⧸ aA`. -/
private theorem mk_eq_zero_of_mul_eq_zero {g a b : A} (hg : g ∈ nonZeroDivisors A) (hb : b = g * a)
    (x : A) (h : Submodule.Quotient.mk (p := Ideal.span {b}) (g * x) = 0) :
    Submodule.Quotient.mk (p := Ideal.span {a}) x = 0 := by
  rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton] at h ⊢
  obtain ⟨c, hc⟩ := h
  refine ⟨c, sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hg).1 _ ?_)⟩
  rw [mul_sub, hc, hb]
  ring

/-- Multiplication by a nonzerodivisor `f` is injective on `A ⧸ fⁿ⁺¹A`. -/
theorem mulSelfQuotPow_injective (hf : f ∈ nonZeroDivisors A) (n : ℕ) :
    Function.Injective (mulSelfQuotPow f n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro m hm
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (Ideal.span {f ^ (n + 1)}) m
  exact mk_eq_zero_of_mul_eq_zero hf (pow_succ' f (n + 1)) x hm

/-- Multiplication by a power of a nonzerodivisor `f` is injective as a map
`A ⧸ fA → A ⧸ fᵐ⁺¹A`. -/
theorem mulPowQuot_injective (hf : f ∈ nonZeroDivisors A) (m : ℕ) :
    Function.Injective (mulPowQuot f m) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (Ideal.span {f}) y
  exact mk_eq_zero_of_mul_eq_zero (pow_mem hf m) (pow_succ f m) x hy

/-- The sequence `A ⧸ fⁿ⁺¹A → A ⧸ fⁿ⁺²A → A ⧸ fA`, with first map multiplication by `f` and
second map the projection, is exact at its middle term. -/
theorem exact_mulSelfQuotPow_quotPowProj (f : A) (n : ℕ) :
    Function.Exact (mulSelfQuotPow f n) (quotPowProj f n) := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (Ideal.span {f ^ (n + 2)}) y
  rw [quotPowProj, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.id_apply,
    Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨Submodule.Quotient.mk c, rfl⟩
  · rintro ⟨z, hz⟩
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective (Ideal.span {f ^ (n + 1)}) z
    rw [mulSelfQuotPow, Submodule.mapQ_apply, LinearMap.lsmul_apply, smul_eq_mul,
      Submodule.Quotient.eq, Ideal.mem_span_singleton] at hz
    obtain ⟨c, hc⟩ := hz
    have hx : x = f * w - f ^ (n + 2) * c := by
      rw [← hc]
      ring
    refine ⟨w - f ^ (n + 1) * c, ?_⟩
    rw [hx]
    ring

/-- **Stacks Project, Tag 0DXU (the associated-primes step).** For a nonzerodivisor `f` of a
commutative ring `A`, the associated primes of `A ⧸ fⁿ⁺¹A` are those of `A ⧸ fA`. -/
@[stacks 0DXU "the step of the proof asserting that the associated primes of A/fⁿA agree with \
those of A/fA, for f a nonzerodivisor"]
theorem associatedPrimes_quotient_span_singleton_pow_succ (hf : f ∈ nonZeroDivisors A) (n : ℕ) :
    associatedPrimes A (A ⧸ Ideal.span {f ^ (n + 1)}) =
      associatedPrimes A (A ⧸ Ideal.span {f}) := by
  induction n with
  | zero => rw [pow_one]
  | succ n ih =>
    refine Set.Subset.antisymm (fun p hp => ?_)
      (associatedPrimes.subset_of_injective (mulPowQuot_injective hf (n + 1)))
    rcases associatedPrimes.subset_union_of_exact (mulSelfQuotPow_injective hf n)
      (exact_mulSelfQuotPow_quotPowProj f n) hp with h | h
    exacts [ih.subset h, h]

/-- The associated primes of `A ⧸ (fA)ⁿ⁺¹` are those of `A ⧸ fA`, for `f` a nonzerodivisor.
This is `associatedPrimes_quotient_span_singleton_pow_succ` with the ideal power `(fA)ⁿ⁺¹` in
place of the element power `fⁿ⁺¹A`. -/
theorem associatedPrimes_quotient_span_singleton_pow_succ'
    (hf : f ∈ nonZeroDivisors A) (n : ℕ) :
    associatedPrimes A (A ⧸ (Ideal.span {f} ^ (n + 1))) =
      associatedPrimes A (A ⧸ Ideal.span {f}) := by
  rw [Ideal.span_singleton_pow]
  exact associatedPrimes_quotient_span_singleton_pow_succ hf n

/-! ### Satisfiability of the hypothesis

The hypothesis `f ∈ nonZeroDivisors A` is carried by every result above. It is satisfied by
`f = 2` in `A = ℤ`, where the common value of the two sides is moreover a nonempty set, so the
conclusion is not an equality of empty sets. -/

example : (2 : ℤ) ∈ nonZeroDivisors ℤ := mem_nonZeroDivisors_of_ne_zero two_ne_zero

example : associatedPrimes ℤ (ℤ ⧸ Ideal.span {(2 : ℤ) ^ 3}) =
    associatedPrimes ℤ (ℤ ⧸ Ideal.span {(2 : ℤ)}) :=
  associatedPrimes_quotient_span_singleton_pow_succ
    (mem_nonZeroDivisors_of_ne_zero two_ne_zero) 2

example : Ideal.span {(2 : ℤ)} ∈ associatedPrimes ℤ (ℤ ⧸ Ideal.span {(2 : ℤ)}) := by
  have hp : (Ideal.span {(2 : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime two_ne_zero).mpr Int.prime_two
  have hcol : (⊥ : Submodule ℤ (ℤ ⧸ Ideal.span {(2 : ℤ)})).colon
      {Submodule.Quotient.mk (1 : ℤ)} = Ideal.span {(2 : ℤ)} := by
    ext r
    simp only [Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
      smul_eq_mul, mul_one, Submodule.Quotient.mk_eq_zero]
  exact ⟨hp, Submodule.Quotient.mk (1 : ℤ), by rw [hcol, hp.radical]⟩

end Stacks.RingTheory.AssociatedPrimes
