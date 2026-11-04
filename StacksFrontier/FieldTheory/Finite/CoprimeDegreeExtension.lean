module

import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Algebra.Field.ULift
public import Mathlib.FieldTheory.Finite.Extension

/-!
# Extensions of a finite field of degree prime to a given integer

A finite field `k` has, for every positive integer `d` and every bound `N`, a finite extension
`L/k` whose degree is prime to `d` and which has more than `N` elements: take the extension of a
prime degree `n > N + d`. This is the choice made in the proof of Stacks Lemma 0B85 for a finite
ground field ("choose an integer `n ≫ 0` prime to `d`"), and again in Stacks Remark 0BA7.

## Main results

* `FiniteField.exists_finrank_coprime_lt_card`: a finite extension of degree prime to `d` and of
  cardinality larger than `N`, in the universe of `k`.

## References

* [Stacks Project, Tag 0B85](https://stacks.math.columbia.edu/tag/0B85)
* [Stacks Project, Tag 0BA7](https://stacks.math.columbia.edu/tag/0BA7)
-/

@[expose] public section

universe u

open Module

/-- **A finite field has extensions of degree prime to `d` and of arbitrarily large
cardinality.** For a finite field `k`, a bound `N` and a positive integer `d` there is a finite
field extension `L/k`, in the universe of `k`, with `[L : k]` prime to `d` and `N < #L`. -/
theorem FiniteField.exists_finrank_coprime_lt_card (k : Type u) [Field k] [Finite k] (N d : ℕ)
    (hd : 0 < d) :
    ∃ (L : Type u) (_ : Field L) (_ : Finite L) (_ : Algebra k L),
      Nat.Coprime (finrank k L) d ∧ N < Nat.card L := by
  obtain h0 | ⟨p, hp, hchar⟩ := CharP.exists' k
  · exact absurd (inferInstance : Finite k) (not_finite_iff_infinite.mpr inferInstance)
  obtain ⟨n, hn, hnp⟩ := Nat.exists_infinite_primes (N + d + 1)
  have : NeZero n := ⟨hnp.ne_zero⟩
  let L := ULift.{u} (FiniteField.Extension k p n)
  let e : L ≃ₐ[k] FiniteField.Extension k p n := ULift.algEquiv
  refine ⟨L, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · rw [e.toLinearEquiv.finrank_eq, FiniteField.finrank_extension]
    exact (hnp.coprime_iff_not_dvd).mpr fun h => by have := Nat.le_of_dvd hd h; omega
  · rw [Nat.card_congr e.toEquiv, FiniteField.natCard_extension]
    calc N < n := by omega
      _ < 2 ^ n := Nat.lt_two_pow_self
      _ ≤ Nat.card k ^ n := Nat.pow_le_pow_left Finite.one_lt_card n
