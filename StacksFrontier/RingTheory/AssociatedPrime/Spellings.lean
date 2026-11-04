module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs

/-!
# Reconciling the spellings of "associated prime"

The Stacks project defines an associated prime of a module `M` over a ring `R` to be a prime
ideal which is *exactly* the annihilator of a single element of `M` (Tag 00LA), while Mathlib's
`IsAssociatedPrime` asks only that the prime be the *radical* of such an annihilator. This file
proves that the two agree over a Noetherian ring, that the Stacks notion is always the stronger
one, and that the several spellings of the Stacks notion carried by this repository are literally
the same set of ideals.

It also identifies the two notions attached to an *ideal* `I` of `R`: the associated primes of
the module `R ⧸ I` and Mathlib's `Submodule.associatedPrimes I`, the primes of the form
`(I : x).radical`. These turn out to be equal with no hypothesis at all, which matters because the
consumer `Stacks.RingTheory.PrincipalCodimOne.isPrincipal_of_forall_associatedPrimes_height_eq_one`
is stated with `Submodule.associatedPrimes` while the geometry produces associated primes of a
module.

## Main results

* `isAssociatedPrime_of_isAssociatedPrimeStacks`: the Stacks notion implies Mathlib's, with no
  hypothesis on `R`. The converse needs `R` Noetherian and is
  `isAssociatedPrimeStacks_iff_mem_associatedPrimes`, which this file imports rather than
  reproves; `assStacks_eq_associatedPrimes` is its set form.
* `colon_bot_quotient_eq_colon`: for `x : R`, the annihilator of the class of `x` in `R ⧸ I` is
  the colon ideal `(I : x)`.
* `associatedPrimes_quotient_eq_submodule_associatedPrimes`:
  `associatedPrimes R (R ⧸ I) = Submodule.associatedPrimes I`, unconditionally.
* `mem_assAssociatedPrimes_iff_isAssociatedPrimeStacks`, `assPrimes_eq_assStacks` and
  `mem_ass_iff_isAssociatedPrimeStacks`: the three further spellings of the Stacks notion that
  live in `StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs` agree with `assStacks`.

## Route

Everything rests on two rewrites. First, `Submodule.colon_span` and `Submodule.bot_colon` say
that the three ways this repository writes the annihilator of an element — as a colon ideal
`(⊥ : Submodule R M).colon (span R {m})`, as a colon against a singleton set
`(⊥ : Submodule R M).colon {m}`, and as `(span R {m}).annihilator` — are the same ideal.
Second, a prime ideal is its own radical, which gives the easy implication; the converse, over a
Noetherian ring, is `isAssociatedPrime_iff`, already in the library.

For the quotient, every element of `R ⧸ I` is the class of some `x : R`, and `r` kills that class
exactly when `r * x ∈ I`; so the annihilators appearing in the two definitions run over the same
family of ideals and the radicals match term by term.

## References

* [Stacks Project, Tag 00LA](https://stacks.math.columbia.edu/tag/00LA)
* [Stacks Project, Tag 02M3](https://stacks.math.columbia.edu/tag/02M3)
-/

@[expose] public section

namespace Stacks.RingTheory.AssociatedPrimeStacks

section Module

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {p : Ideal R}

/-- The annihilator of an element, written as a colon ideal against the cyclic submodule it
generates, is the colon ideal against the singleton set. This is the only discrepancy between
`IsAssociatedPrimeStacks` and the inner condition of Mathlib's `IsAssociatedPrime`. -/
theorem colon_span_singleton_eq_colon_singleton (m : M) :
    (⊥ : Submodule R M).colon (Submodule.span R {m}) = (⊥ : Submodule R M).colon {m} :=
  Submodule.colon_span

/-- The annihilator of an element, written as a colon ideal, is the annihilator of the cyclic
submodule it generates. -/
theorem colon_span_singleton_eq_annihilator (m : M) :
    (⊥ : Submodule R M).colon (Submodule.span R {m}) = (Submodule.span R {m}).annihilator :=
  Submodule.bot_colon

/-- A prime which is exactly the annihilator of an element is in particular the radical of that
annihilator, so the Stacks notion of an associated prime implies Mathlib's. No hypothesis on `R`
is needed. -/
theorem isAssociatedPrime_of_isAssociatedPrimeStacks (h : IsAssociatedPrimeStacks R M p) :
    IsAssociatedPrime p M := by
  obtain ⟨hp, m, hm⟩ := h
  rw [colon_span_singleton_eq_colon_singleton] at hm
  refine ⟨hp, m, ?_⟩
  rw [hm]
  exact hp.radical.symm

/-- The annihilator of an element, written as a colon ideal, is `Ideal.torsionOf`. -/
private theorem colon_span_singleton_eq_torsionOf (m : M) :
    (⊥ : Submodule R M).colon (Submodule.span R {m}) = Ideal.torsionOf R M m := by
  rw [colon_span_singleton_eq_annihilator]
  exact Ideal.annihilator_span_singleton_eq_torsionOf m

variable (R M)

/-- The Stacks associated primes are always among Mathlib's. -/
theorem assStacks_subset_associatedPrimes : assStacks R M ⊆ associatedPrimes R M :=
  fun _ h => isAssociatedPrime_of_isAssociatedPrimeStacks h

/-- Over a Noetherian ring the Stacks set of associated primes is Mathlib's `associatedPrimes`.
The pointwise statement is `isAssociatedPrimeStacks_iff_mem_associatedPrimes`. -/
theorem assStacks_eq_associatedPrimes [IsNoetherianRing R] :
    assStacks R M = associatedPrimes R M :=
  Set.ext fun _ => isAssociatedPrimeStacks_iff_mem_associatedPrimes _

/-! ### The remaining spellings in `StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs`

Three further sets of associated primes are defined in that file. All three are the Stacks
notion again, written with `Submodule.annihilator` instead of a colon ideal and, in two cases,
indexed by `PrimeSpectrum R` rather than by `Ideal R`. -/

/-- `assAssociatedPrimes`, the `PrimeSpectrum`-indexed spelling, is the Stacks notion. -/
theorem mem_assAssociatedPrimes_iff_isAssociatedPrimeStacks (q : PrimeSpectrum R) :
    q ∈ assAssociatedPrimes R M ↔ IsAssociatedPrimeStacks R M q.asIdeal := by
  refine ⟨fun ⟨x, hx⟩ => ⟨q.isPrime, x, ?_⟩, fun ⟨_, m, hm⟩ => ⟨m, ?_⟩⟩
  · rw [colon_span_singleton_eq_annihilator]
    exact hx.symm
  · rw [← hm, colon_span_singleton_eq_annihilator]

/-- `Stacks.AssociatedPrimes.assPrimes`, the `Ideal.torsionOf` spelling, is `assStacks`. -/
theorem assPrimes_eq_assStacks : Stacks.AssociatedPrimes.assPrimes R M = assStacks R M := by
  ext q
  exact ⟨fun ⟨hq, m, hm⟩ => ⟨hq, m, (colon_span_singleton_eq_torsionOf m).trans hm⟩,
    fun ⟨hq, m, hm⟩ => ⟨hq, m, (colon_span_singleton_eq_torsionOf m).symm.trans hm⟩⟩

/-- `StacksProblem.Ass`, the `Ideal.torsionOf` spelling, is the Stacks notion. -/
theorem mem_ass_iff_isAssociatedPrimeStacks (q : PrimeSpectrum R) :
    q ∈ StacksProblem.Ass R M ↔ IsAssociatedPrimeStacks R M q.asIdeal := by
  exact ⟨fun ⟨m, hm⟩ => ⟨q.isPrime, m, (colon_span_singleton_eq_torsionOf m).trans hm⟩,
    fun ⟨_, m, hm⟩ => ⟨m, (colon_span_singleton_eq_torsionOf m).symm.trans hm⟩⟩

end Module

section Quotient

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- The annihilator of the class of `x : R` in `R ⧸ I`, as a colon ideal in the module `R ⧸ I`,
is the colon ideal `(I : x)` in `R`. -/
theorem colon_bot_quotient_eq_colon (x : R) :
    (⊥ : Submodule R (R ⧸ I)).colon {(Ideal.Quotient.mk I) x} = I.colon {x} := by
  ext r
  rw [Submodule.mem_colon_singleton, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
    Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem, Submodule.mem_colon_singleton, smul_eq_mul]

/-- **The associated primes of a quotient.** The associated primes of the `R`-module `R ⧸ I` are
exactly Mathlib's `Submodule.associatedPrimes I`, the primes of the form `(I : x).radical`. No
hypothesis on `R` is required: the two definitions quantify over the same family of colon ideals,
because `Ideal.Quotient.mk I` is surjective. -/
theorem associatedPrimes_quotient_eq_submodule_associatedPrimes :
    associatedPrimes R (R ⧸ I) = Submodule.associatedPrimes I := by
  ext q
  refine ⟨fun ⟨hq, z, hz⟩ => ⟨hq, ?_⟩, fun ⟨hq, x, hx⟩ => ⟨hq, (Ideal.Quotient.mk I) x, ?_⟩⟩
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨x, by rw [hz, colon_bot_quotient_eq_colon]⟩
  · rw [hx, colon_bot_quotient_eq_colon]

end Quotient

end Stacks.RingTheory.AssociatedPrimeStacks

end
