module

public import Mathlib.RingTheory.Noetherian.OfPrime
import StacksCore.Tactic.StacksAttribute

/-!
# Maximality criteria for an ideal to be prime

Over a commutative ring, an ideal maximal with respect to a suitable property is prime. The two
general criteria are Mathlib's: an ideal maximal among those disjoint from a multiplicative
subset is prime (Stacks 05KF), and an ideal maximal for not satisfying an Oka predicate — such
as `Ideal.FG` — is prime, whence Cohen's theorem that a ring all of whose primes are finitely
generated is Noetherian (Stacks 05KG). Only the `add_to_stacks` pointers to those declarations
are recorded here.

What remains is the specialization of the first criterion to the submonoid of nonzerodivisors
(Stacks 05KI).
-/

@[expose] public section

-- The former @[stacks 05KF] theorem is the Mathlib lemma.
add_to_stacks 05KF Ideal.isPrime_of_maximally_disjoint

-- The former @[stacks 05KG "(1)"] theorem is Mathlib's Oka criterion applied to `Ideal.FG`,
-- with maximality spelled as `Maximal (¬ Ideal.FG ·)` instead of by hand.
add_to_stacks 05KG "(1): `Ideal.FG` is an Oka predicate" Ideal.isOka_fg
add_to_stacks 05KG "(1)" Ideal.IsOka.isPrime_of_maximal_not

-- The former @[stacks 05KG "(2)"] theorem is Mathlib's Cohen's theorem, whose conclusion
-- `IsNoetherianRing R` unfolds to "every ideal is finitely generated".
add_to_stacks 05KG "(2)" IsNoetherianRing.of_prime
add_to_stacks 05KG "(2)" isNoetherianRing_iff_ideal_fg

/-!
## Ideals maximal among those containing no nonzerodivisor

For (1), `R` may be a commutative semiring; (2) assumes a commutative ring.
`R⁰` denotes the submonoid `nonZeroDivisors R`, whose membership is characterized by
`x ∈ R⁰ ↔ ∀ y, y * x = 0 → y = 0`. For commutative `R` the two one-sided
cancellation conditions defining a nonzerodivisor coincide, so `R⁰` is the set of
nonzerodivisors.

An ideal `I ⊆ R` *contains a nonzerodivisor* when `¬ Disjoint (I : Set R) R⁰`,
and `I` is *maximal among the ideals which do not contain a nonzerodivisor* when
`Maximal (fun J : Ideal R ↦ Disjoint (J : Set R) R⁰) I`, that is, when
`Disjoint (I : Set R) R⁰` and `¬ Disjoint (J : Set R) R⁰` for every ideal
`I < J`.

Two results are proved.

1. An ideal maximal among the ideals which do not contain a nonzerodivisor is
   prime. This is the special case `S = R⁰` of the statement that an ideal
   maximal among those disjoint from a multiplicative set is prime.
2. If `R` is nonzero and every nonzero prime ideal of `R` contains a
   nonzerodivisor, then `R` is a domain. Indeed `⊥` is disjoint from `R⁰`, since
   every nonzerodivisor is nonzero, and the hypothesis forces `⊥` to be prime.
-/

open scoped nonZeroDivisors

/-- An ideal maximal among the ideals which do not contain a nonzerodivisor is prime. -/
@[stacks 05KI "(1)"]
theorem Ideal.isPrime_of_maximal_disjoint_nonZeroDivisors {R : Type*} [CommSemiring R]
    (I : Ideal R) (hI : Maximal (fun J : Ideal R ↦ Disjoint (J : Set R) (R⁰ : Set R)) I) :
    I.IsPrime :=
  I.isPrime_of_maximally_disjoint _ hI.prop fun _ hJ ↦ hI.not_prop_of_gt hJ

variable {R : Type*} [CommRing R]

/-- (Characterization of a domain.) If `R` is nonzero and every nonzero prime
ideal of `R` contains a nonzerodivisor, then `R` is a domain. -/
@[stacks 05KI "(2)"]
theorem isDomain_of_forall_nonzero_prime_containsNonZeroDivisor [Nontrivial R]
    (h : ∀ P : Ideal R, P.IsPrime → P ≠ ⊥ →
      ¬ Disjoint (P : Set R) (nonZeroDivisors R : Set R)) :
    IsDomain R := by
  obtain ⟨p, hp, -, hpd⟩ := Ideal.exists_le_prime_disjoint ⊥ R⁰ <| by
    simp [zero_notMem_nonZeroDivisors]
  obtain rfl : p = ⊥ := by_contra (h p hp · hpd)
  exact IsDomain.of_bot_isPrime R
