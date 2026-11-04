module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.Ideal.GoingUp

import StacksCore.Tactic.StacksAttribute

/-!
# Integral algebras over a field

Let `k` be a field and `S` a `k`-algebra. If `S` is a domain which is finite dimensional over `k`,
or more generally a domain integral over `k`, then `S` is a field; and if `S` is integral over `k`
then every prime of `S` is maximal (Stacks 00GS).

## Main results

* `Algebra.IsIntegral.isMaximal_of_isPrime`: every prime ideal of an integral algebra over a field
  is maximal, which is item (3) of Stacks 00GS.

Items (1) and (2) are Mathlib's `IsField.of_isDomain_of_finite` and
`isField_of_isIntegral_of_isField'`; the latter is stated for an integral extension of any
commutative ring which is a field, the base `k` of the source giving `Field.toIsField k`.

## References

* [Stacks Project, Tag 00GS](https://stacks.math.columbia.edu/tag/00GS)
-/

@[expose] public section

add_to_stacks 00GS "(1) If `S` is a domain and finite dimensional over the field `k`, then `S` is \
a field; finite dimensionality is `Module.Finite k S`." IsField.of_isDomain_of_finite

add_to_stacks 00GS "(2) If `S` is integral over `k` and a domain, then `S` is a field; Mathlib \
states it for an integral extension of any ring `R` with `IsField R`, applied to \
`Field.toIsField k`." isField_of_isIntegral_of_isField'

/-- **Stacks 00GS (3).** Every prime ideal of an integral algebra over a field is maximal: its
contraction to the field is the zero ideal, which is maximal. -/
@[stacks 00GS "(3) If `S` is integral over `k` then every prime of `S` is a maximal ideal."]
theorem Algebra.IsIntegral.isMaximal_of_isPrime {k S : Type*} [Field k] [CommRing S] [Algebra k S]
    [Algebra.IsIntegral k S] (P : Ideal S) [P.IsPrime] : P.IsMaximal :=
  Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P <| by
    rw [Ideal.eq_bot_of_prime (P.comap (algebraMap k S))]
    exact Ideal.bot_isMaximal
