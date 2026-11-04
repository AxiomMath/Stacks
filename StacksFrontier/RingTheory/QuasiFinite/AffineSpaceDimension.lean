module


public import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import StacksFrontier.RingTheory.QuasiFinite.Dimension

@[expose] public section

/-!
# Dimension of a quasi-finite cover of affine space

Let `k` be a field, let `σ` be a finite index type and let `S` be a quasi-finite algebra over the
polynomial ring `k[t_i ; i ∈ σ]` in `n = #σ` variables. This file proves Stacks 00QG:
`dim(S) ≤ n`, so that a quasi-finite cover of affine `n`-space has dimension at most `n`.

The bound is taken prime by prime, along `dim(S) = ⨆_𝔮 height(𝔮)`. A quasi-finite map does not
raise the dimension of a local ring (Stacks 00QF), so every prime `𝔮` of `S` satisfies
`height(𝔮) ≤ height(𝔮 ∩ k[t_i]) ≤ dim k[t_i]`; the supremum over `𝔮` is then
`dim(S) ≤ dim k[t_i]`, and `dim k[t_i] = dim k + n = n`.

## Main results

* `Stacks.QuasiFinite.AffineSpaceDimension.solution`: the statement of Stacks 00QG.

## Implementation notes

Stacks 00QF bounds one prime at a time; summed over all primes of `S` it is the inequality
`dim(S) ≤ dim(R)` for a quasi-finite algebra `R → S`, which is not in Mathlib and is
`Stacks.QuasiFinite.AffineSpaceDimension.ringKrullDim_le_of_quasiFinite` here. It needs no
finiteness hypothesis on `R → S`: `Algebra.QuasiFinite R S` is quasi-finiteness at every prime of
`S`, which is all that 00QF asks for at each prime separately.

The source bounds the local rings of `k[t_1, …, t_n]` individually, using that at a maximal ideal
the local ring is regular of dimension exactly `n` (Stacks 00OP). Here that step is the global
`dim k[t_1, …, t_n] = dim k + n = n` (`MvPolynomial.ringKrullDim_of_isNoetherianRing` and
`ringKrullDim_eq_zero_of_field`) together with `height(𝔭) ≤ dim k[t_1, …, t_n]`, the same bound
with the supremum taken outside rather than inside; for an upper bound neither regularity nor a
maximal ideal is needed.

## References

* [StacksProject 00QG](https://stacks.math.columbia.edu/tag/00QG)
* [StacksProject 00QF](https://stacks.math.columbia.edu/tag/00QF)
* [StacksProject 00OP](https://stacks.math.columbia.edu/tag/00OP)
-/

namespace Stacks.QuasiFinite.AffineSpaceDimension

/-- A quasi-finite algebra has Krull dimension at most that of its base. This is Stacks 00QF, the
bound `height(𝔮) ≤ height(𝔮 ∩ R)` at a prime where `R → S` is quasi-finite, taken over all primes
of `S` at once; no finiteness hypothesis on `R → S` is needed. -/
private lemma ringKrullDim_le_of_quasiFinite (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.QuasiFinite R S] : ringKrullDim S ≤ ringKrullDim R :=
  (ringKrullDim_le_iff_height_le _).2 fun {𝔮} _ ↦
    (WithBot.coe_le_coe.2
        (Ideal.height_le_height_of_liesOver_of_quasiFiniteAt (𝔮.under R) 𝔮)).trans
      Ideal.height_le_ringKrullDim_of_isPrime

/-- **Stacks 00QG.** Let `k` be a field and let `S` be a quasi-finite algebra over the polynomial
ring `k[t_i ; i ∈ σ]` in `n = #σ` variables. Then `dim(S) ≤ n`: a quasi-finite cover of
affine `n`-space has dimension at most `n`. -/
public theorem solution (k : Type*) [Field k]
    {σ S : Type*} [Finite σ] [CommRing S] [Algebra (MvPolynomial σ k) S]
    [Algebra.QuasiFinite (MvPolynomial σ k) S] : ringKrullDim S ≤ Nat.card σ :=
  (ringKrullDim_le_of_quasiFinite (MvPolynomial σ k) S).trans_eq <| by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]

end Stacks.QuasiFinite.AffineSpaceDimension

/-!
# Dimension of a quasi-finite cover of affine space

Let `k` be a field, let `σ` be a finite index type and let `S` be an algebra over the polynomial
ring `k[t_i ; i ∈ σ]` in `n = #σ` variables. If `S` is quasi-finite over `k[t_i]`, then

`dim(S) ≤ n`,

that is, a quasi-finite cover of affine `n`-space has dimension at most `n`. Indeed every local
ring of `k[t_1, …, t_n]` has dimension at most `n` (at a maximal ideal it is regular of dimension
exactly `n`, tag 00OP), and a quasi-finite map does not raise the dimension of a local ring
(tag 00QF), so every local ring of `S` has dimension at most `n`; and `dim(S)` is the supremum of
the dimensions of the local rings of `S`.

## Main results

* `ringKrullDim_le_natCard_of_quasiFinite_mvPolynomial`: Stacks 00QG.

## Implementation notes

*Quasi-finiteness.* `Algebra.QuasiFinite R S` (tagged 00PL) asks that the fibre `κ(𝔭) ⊗_R S` be a
finite `κ(𝔭)`-module for every prime `𝔭` of `R`, without the source's finite type hypothesis.
Under `Algebra.FiniteType R S` it is exactly the source's quasi-finite ring map, by
`Algebra.QuasiFinite.iff_finite_primesOver` and
`Algebra.QuasiFinite.iff_finite_comap_preimage_singleton` (tag 00PM: for a finite type map,
quasi-finite means finite fibres, equivalently quasi-finite at every prime).

*Two hypotheses of the source are dropped, so the statement below implies the tag.* Neither the
finite type hypothesis on `S` nor injectivity of `k[t_1, …, t_n] → S` (the source writes
`k[t_1, …, t_n] ⊂ S`) is used: only the fibres of `Spec(S) → Spec(k[t_1, …, t_n])` enter, through
the fact that a prime of `S` is determined by a prime containing it with the same contraction, so
that `Spec(S) → Spec(k[t_1, …, t_n])` is strictly monotone. Adding
`[Algebra.FiniteType (MvPolynomial σ k) S]` back — equivalently, `S` of finite type over `k`, the
two agreeing because `k → MvPolynomial σ k` is itself of finite type — recovers the source's
statement, and instance resolution supplies that hypothesis at every use site.

*Finitely many variables, indexed by `σ`.* The source's `k[t_1, …, t_n]` is `MvPolynomial σ k` for
`Finite σ` and its `n` is `Nat.card σ`, the spelling of Mathlib's
`MvPolynomial.ringKrullDim_of_isNoetherianRing`. Finiteness of `σ` is load-bearing: for infinite
`σ` one has `Nat.card σ = 0` while `dim k[t_i] = ∞`.

*The dimension is `ringKrullDim`, valued in `WithBot ℕ∞`.* The source's `dim(S) ≤ n` is
`ringKrullDim S ≤ (Nat.card σ : WithBot ℕ∞)`; for `S = 0` the left-hand side is `⊥`, so no
nontriviality hypothesis on `S` is needed.

*Where the `n` enters.* Only half of the argument is about polynomial rings: for any quasi-finite
algebra `R → S` one has `dim(S) ≤ dim(R)`, which is 00QF globalized along
`dim(R) = ⨆_𝔭 height(𝔭)`, and the present tag is that inequality together with
`dim k[t_1, …, t_n] = n` (`MvPolynomial.ringKrullDim_of_isNoetherianRing` and
`ringKrullDim_eq_zero_of_field`). The statement is kept over the polynomial ring, with the bound
`Nat.card σ`, because that is what the tag claims.

Faithfulness to [StacksProject 00QG]:

1. No hypothesis is idle: `Field k` is load-bearing (for `k = ℤ` and `S = ℤ[t]` quasi-finite over
   itself, `dim(S) = 2 > 1 = Nat.card σ`), `Finite σ` bounds the right-hand side, and the
   `MvPolynomial σ k`-algebra structure together with quasi-finiteness is what the left-hand side
   is bounded by; the source's two remaining hypotheses are absent precisely because unused.
2. The scalars and base are the source's: quasi-finiteness is of `S` over the polynomial ring
   `MvPolynomial σ k` itself, not over `k` and not over a localization, and `dim(S)` is the Krull
   dimension of the ring `S`. The source's `k`-algebra structure on `S` is the composite
   `k → k[t_i] → S`, determined by the given instance, so it needs no separate hypothesis.
3. The map is pinned, not merely assumed to exist: it is `algebraMap (MvPolynomial σ k) S` of the
   given instance, and both sides of the inequality are functions of that datum.
4. The instantiation is not degenerate: `σ = Fin 1` and `S = MvPolynomial (Fin 1) k` give `1 ≤ 1`,
   sharp and with neither side `0`, `⊥` or `⊤` (quasi-finiteness holds there by
   `Algebra.QuasiFinite.instOfFinite`), and `S = MvPolynomial (Fin 1) k × MvPolynomial (Fin 1) k`
   is a witness whose structure map is not an isomorphism.

## References

* [StacksProject 00QG](https://stacks.math.columbia.edu/tag/00QG)
* [StacksProject 00QF](https://stacks.math.columbia.edu/tag/00QF)
* [StacksProject 00OP](https://stacks.math.columbia.edu/tag/00OP)
* [StacksProject 00PL](https://stacks.math.columbia.edu/tag/00PL)

## Tags

quasi-finite algebra, Krull dimension, polynomial ring, affine space, finite type algebra
-/

@[expose] public section

/-- **Stacks 00QG.** Let `k` be a field and let `S` be a quasi-finite algebra over the polynomial
ring `k[t_i ; i ∈ σ]` in `n = #σ` variables. Then `dim(S) ≤ n`: a quasi-finite cover of
affine `n`-space has dimension at most `n`. -/
@[stacks 00QG "The source's `k[t_1, …, t_n] ⊂ S` with `S` of finite type over `k` and the map
quasi-finite is weakened to `Algebra.QuasiFinite (MvPolynomial σ k) S` with `Finite σ`, which the
source's hypotheses imply (tag 00PM); neither finite type nor injectivity is used. See the module
docstring."]
public theorem ringKrullDim_le_natCard_of_quasiFinite_mvPolynomial (k : Type*) [Field k]
    {σ S : Type*} [Finite σ] [CommRing S] [Algebra (MvPolynomial σ k) S]
    [Algebra.QuasiFinite (MvPolynomial σ k) S] : ringKrullDim S ≤ Nat.card σ :=
  Stacks.QuasiFinite.AffineSpaceDimension.solution k

end
