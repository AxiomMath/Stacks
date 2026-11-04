module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.RingTheory.Ideal.Span
public import StacksFrontier.RingTheory.IntegralClosure.AwayExactSequence
public import StacksFrontier.RingTheory.Nagata.MonogenicN1

/-!
# The two chart subalgebras of a pair of inverse elements

Let `A` be a commutative ring with an algebra map to a commutative ring `K`, let `x y : A` and
let `t s : K` satisfy `t * s = 1` and `x * t = y` (images in `K`, so that `t` plays the role of
`y / x` and `s` of `x / y`). This file relates the two `A`-subalgebras

* `B = Algebra.adjoin A {t}`,
* `C = Algebra.adjoin A {s}`

of `K` to their join `D = Algebra.adjoin A {t, s}`: the overlap `D` is the sum of `B` and `C` as
`A`-submodules, and — once `K` is a domain, `A` embeds in `K`, `x ≠ 0` and `y` is a
nonzerodivisor modulo `x` — the intersection of `B` and `C` is `A` itself.

## Main results

* `Stacks.ResolutionOfSurfaces.CartierDescent.exists_add_mem_adjoin`: every element of
  `Algebra.adjoin A {t, s}` is a sum of an element of `Algebra.adjoin A {t}` and an element of
  `Algebra.adjoin A {s}`.
* `Stacks.ResolutionOfSurfaces.CartierDescent.exists_pow_mul_eq_algebraMap_of_mem_adjoin`:
  clearing denominators — a power of `x` carries `Algebra.adjoin A {t}` into the image of `A`.
* `Stacks.ResolutionOfSurfaces.CartierDescent.mem_span_pow_of_mul_pow_mem`: the descent step,
  `a * y ^ m = x ^ n * b → a ∈ (x ^ n)` for `y` a nonzerodivisor modulo `x`.
* `Stacks.ResolutionOfSurfaces.CartierDescent.mem_range_algebraMap_of_pow_mul_eq`: cancelling a
  cleared denominator again, inside a ring without zero divisors.
* `Stacks.ResolutionOfSurfaces.CartierDescent.mem_range_algebraMap_of_mem_adjoin_inter`: the two
  subalgebras meet in the image of `A`.

## Implementation notes

The intended instance is a two-dimensional regular local ring `A` with maximal ideal
`𝔪 = (x, y)` and `K = FractionRing A`, with `t = y / x` and `s = x / y`. Then `B = A[𝔪/x]` and
`C = A[𝔪/y]` are the affine blowup algebras of the two standard charts of the blowup of a
regular local surface at its closed point, read inside the fraction field, and `D` is the ring
of the overlap of those two charts. None of that — regularity, locality, dimension, or the
identification of `𝔪` — is used below: the statements are about a bare pair `t * s = 1` over a
ring mapping to `K`.

## References

* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
-/

@[expose] public section

universe u

namespace Stacks.ResolutionOfSurfaces.CartierDescent

variable {A K : Type u} [CommRing A] [CommRing K] [Algebra A K]

/-- If `t * s = 1` and `x * t = y` in `K`, then `y * s = x`. -/
public theorem algebraMap_mul_eq_of_mul_eq_one {x y : A} {t s : K} (hts : t * s = 1)
    (hxt : algebraMap A K x * t = algebraMap A K y) :
    algebraMap A K y * s = algebraMap A K x := by
  rw [← hxt, mul_assoc, hts, mul_one]

/-- **The two charts span their overlap.** For `t * s = 1` every element of
`Algebra.adjoin A {t, s}` is the sum of an element of `Algebra.adjoin A {t}` and an element of
`Algebra.adjoin A {s}`: the overlap of the two charts is the sum of the two charts as
`A`-submodules of `K`. -/
public theorem exists_add_mem_adjoin {t s : K} (hts : t * s = 1) (z : K)
    (hz : z ∈ Algebra.adjoin A ({t, s} : Set K)) :
    ∃ b ∈ Algebra.adjoin A ({t} : Set K), ∃ c ∈ Algebra.adjoin A ({s} : Set K), z = b + c := by
  have hz' : z ∈ Subalgebra.toSubmodule (Algebra.adjoin A ({t} : Set K)) ⊔
      Subalgebra.toSubmodule (Algebra.adjoin A ({s} : Set K)) := by
    rw [← toSubmodule_adjoin_pair_eq_sup hts]
    exact (Subalgebra.mem_toSubmodule _).2 hz
  obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.1 hz'
  exact ⟨b, (Subalgebra.mem_toSubmodule _).1 hb, c, (Subalgebra.mem_toSubmodule _).1 hc, hbc.symm⟩

/-- **Clearing denominators on a chart.** If `x * t = y` in `K`, then for every `z` in
`Algebra.adjoin A {t}` some power of `x` takes `z` into the image of `A`. -/
public theorem exists_pow_mul_eq_algebraMap_of_mem_adjoin {x y : A} {t : K}
    (hxt : algebraMap A K x * t = algebraMap A K y) {z : K}
    (hz : z ∈ Algebra.adjoin A ({t} : Set K)) :
    ∃ (n : ℕ) (a : A), (algebraMap A K x) ^ n * z = algebraMap A K a := by
  have hab : algebraMap A (Algebra.adjoin A ({t} : Set K)) x *
      ⟨t, Algebra.self_mem_adjoin_singleton A t⟩ =
        algebraMap A (Algebra.adjoin A ({t} : Set K)) y := Subtype.ext (by simpa using hxt)
  obtain ⟨n, a, h⟩ := MonogenicN1.exists_pow_mul_eq_algebraMap
    (A := A) (C := ↥(Algebra.adjoin A ({t} : Set K)))
    ⟨t, Algebra.self_mem_adjoin_singleton A t⟩ (MonogenicN1.adjoin_singleton_top t) x y hab
    ⟨z, hz⟩
  exact ⟨n, a, by simpa using congrArg Subtype.val h⟩

/-- **A nonzerodivisor modulo `x` stays one after iteration.** If multiplying by `y` does not
take an element of `A` outside the ideal `(x)`, then neither does multiplying by a power of
`y`. -/
public theorem mem_span_singleton_of_mul_pow_mem {x y : A}
    (hreg : ∀ a : A, a * y ∈ Ideal.span ({x} : Set A) → a ∈ Ideal.span ({x} : Set A))
    (m : ℕ) (a : A) (h : a * y ^ m ∈ Ideal.span ({x} : Set A)) :
    a ∈ Ideal.span ({x} : Set A) := by
  induction m with
  | zero => simpa using h
  | succ k ih => exact ih (hreg _ (by rwa [mul_assoc, ← pow_succ]))

/-- **Descent along a power of `x`.** If `x` is a nonzerodivisor of `A` and `y` is a
nonzerodivisor modulo `x`, then `a * y ^ m = x ^ n * b` forces `a ∈ (x ^ n)`. -/
public theorem mem_span_pow_of_mul_pow_mem {x y : A}
    (hreg : ∀ a : A, a * y ∈ Ideal.span ({x} : Set A) → a ∈ Ideal.span ({x} : Set A))
    (hx : x ∈ nonZeroDivisors A) (n m : ℕ) (a b : A) (h : a * y ^ m = x ^ n * b) :
    a ∈ Ideal.span ({x ^ n} : Set A) := by
  induction n generalizing a b with
  | zero => simp
  | succ k ih =>
    have hxa : a * y ^ m ∈ Ideal.span ({x} : Set A) := by
      rw [h]
      exact Ideal.mem_span_singleton.2 ⟨x ^ k * b, by ring⟩
    obtain ⟨a', rfl⟩ :=
      Ideal.mem_span_singleton.1 (mem_span_singleton_of_mul_pow_mem hreg m a hxa)
    have h' : a' * y ^ m = x ^ k * b := by
      refine (mul_cancel_right_mem_nonZeroDivisors hx).1 ?_
      calc a' * y ^ m * x = x * a' * y ^ m := by ring
        _ = x ^ (k + 1) * b := h
        _ = x ^ k * b * x := by ring
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 (ih a' b h')
    exact Ideal.mem_span_singleton.2 ⟨c, by ring⟩

/-- **Cancelling a cleared denominator.** In a ring without zero divisors, if a power of `x`
has nonzero image and takes `z` to the image of an element of the ideal `(x ^ n)`, then `z`
itself is in the image of `A`. -/
public theorem mem_range_algebraMap_of_pow_mul_eq [NoZeroDivisors K] {x : A} {z : K}
    (hx0 : algebraMap A K x ≠ 0) (n : ℕ) (a : A) (ha : a ∈ Ideal.span ({x ^ n} : Set A))
    (h : (algebraMap A K x) ^ n * z = algebraMap A K a) :
    z ∈ (algebraMap A K).range := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 ha
  exact ⟨c, mul_left_cancel₀ (pow_ne_zero n hx0) (by rw [h, map_mul, map_pow])⟩

/-- **The two charts meet in `A`.** Let `A` embed in a domain `K`, let `t * s = 1` and
`x * t = y` in `K`, let `x ≠ 0` and let `y` be a nonzerodivisor modulo `x` in `A`. Then an
element of `K` lying in both `Algebra.adjoin A {t}` and `Algebra.adjoin A {s}` is already in the
image of `A`. -/
public theorem mem_range_algebraMap_of_mem_adjoin_inter [IsDomain K]
    (hinj : Function.Injective (algebraMap A K)) {x y : A} {t s : K} (hts : t * s = 1)
    (hxt : algebraMap A K x * t = algebraMap A K y) (hx : x ≠ 0)
    (hreg : ∀ a : A, a * y ∈ Ideal.span ({x} : Set A) → a ∈ Ideal.span ({x} : Set A)) (z : K)
    (hzB : z ∈ Algebra.adjoin A ({t} : Set K)) (hzC : z ∈ Algebra.adjoin A ({s} : Set K)) :
    z ∈ (algebraMap A K).range := by
  have hx0 : algebraMap A K x ≠ 0 := fun h => hx (hinj (by rw [h, map_zero]))
  obtain ⟨n, a, ha⟩ := exists_pow_mul_eq_algebraMap_of_mem_adjoin hxt hzB
  obtain ⟨m, b, hb⟩ :=
    exists_pow_mul_eq_algebraMap_of_mem_adjoin (algebraMap_mul_eq_of_mul_eq_one hts hxt) hzC
  have key : a * y ^ m = x ^ n * b := by
    refine hinj ?_
    rw [map_mul, map_mul, map_pow, map_pow, ← ha, ← hb]
    ring
  have : IsDomain A := Function.Injective.isDomain (algebraMap A K) hinj
  have hxnzd : x ∈ nonZeroDivisors A := mem_nonZeroDivisors_of_ne_zero hx
  exact mem_range_algebraMap_of_pow_mul_eq hx0 n a
    (mem_span_pow_of_mul_pow_mem hreg hxnzd n m a b key) ha

end Stacks.ResolutionOfSurfaces.CartierDescent

end
