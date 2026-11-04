module

public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import StacksFrontier.RingTheory.Flat.ShortExact
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Covering the associated primes of a module by standard opens

Let `R` be a ring, let `M` be an `R`-module and let `g : ι → R` be a family of elements. The
standard opens `D(g i)` cover the associated primes of `M` exactly when the canonical map
`M → ∏ i, M_{g i}` is injective. Over a Noetherian ring this is the only way the condition
`Ass(M) ⊆ ⋃ i, D(g i)` is ever used: it converts a statement about the associated primes of a
module into the injectivity of an explicit `R`-linear map, which is a condition that base
change can be made to preserve.

The companion fact is the one that makes it preserved. If an injective map of modules has a
flat cokernel, then every base change of it is still injective. Combining the two gives the
step that both Stacks 0573 and Stacks 05KP call "reversing the arguments above": having
arranged, by generic freeness (Stacks 051T), that the cokernel of `M → ∏ i, M` is flat over
the base, the covering condition on the associated primes spreads from the generic fibre to
every fibre.

## Main definitions

* `Stacks.Divisors.smulPi` is the `R`-linear map `M → (ι → M)` whose components are
  multiplication by the `g i`.

## Main results

* `Stacks.Divisors.eq_zero_of_forall_exists_pow_smul_eq_zero`: if the standard opens `D(g i)`
  cover `Ass(M)` over a Noetherian ring, an element of `M` killed by a power of every `g i` is
  zero.
* `Stacks.Divisors.injective_pi_iff_forall_exists_notMem`: over a Noetherian ring, the
  canonical map from `M` to a product of localizations `M_{g i}` is injective exactly when
  the `D(g i)` cover `Ass(M)`.
* `Stacks.Divisors.injective_smulPi_iff_forall_exists_notMem`: the same criterion in the form
  used in practice, where the product of localizations is replaced by the single map
  `m ↦ (g i • m)`.
* `Stacks.Divisors.exists_notMem_of_injective_smulPi`: the direction that needs no Noetherian
  hypothesis, stated for the strict notion `IsAssociatedPrimeStacks` of Stacks 00LA.
* `Stacks.Divisors.injective_lTensor_of_flat_of_exact` and
  `Stacks.Divisors.injective_lTensor_of_flat_quotient`: an injective map of modules with flat
  cokernel stays injective after any base change.
* `Stacks.Divisors.isAssociatedPrimeStacks_iff_mem_associatedPrimes`: over a Noetherian ring
  the strict notion of Stacks 00LA agrees with Mathlib's `associatedPrimes`.

## Implementation notes

The localizations are not pinned to `LocalizedModule (Submonoid.powers (g i)) M`: the maps
`l i : M →ₗ[R] M' i` are arbitrary, constrained only by
`IsLocalizedModule (Submonoid.powers (g i)) (l i)`. The consumers of this criterion meet the
localizations as the sections `Γ(D(g i), F)` of a quasi-coherent sheaf, which are a model of
`M_{g i}` but not that model, so pinning it would force a transport at every use.

Two notions of associated prime are in play and both are used, each where it is cheapest.
Mathlib's `associatedPrimes R M` asks for a prime which is the *radical* of the annihilator of
an element; the strict notion `IsAssociatedPrimeStacks` of Stacks 00LA, which is the one the
Stacks project and `Stacks.Divisors.IsAssociatedPoint` use, asks for equality. The two agree
over a Noetherian ring (`isAssociatedPrime_iff`), and the statements below carry a Noetherian
hypothesis exactly where they need one: the direction producing an associated prime out of a
nonzero element does, the direction consuming one does not.

The covering condition is written `∀ p ∈ associatedPrimes R M, ∃ i, g i ∉ p` rather than as an
inclusion of subsets of `PrimeSpectrum R`, since `associatedPrimes` is a set of ideals; the
two readings agree because `g i ∉ p` is membership of the prime corresponding to `p` in the
standard open `D(g i)`.

## References

* [Stacks Project, Tag 00LA](https://stacks.math.columbia.edu/tag/00LA)
* [Stacks Project, Tag 00HL](https://stacks.math.columbia.edu/tag/00HL)
* [Stacks Project, Tag 0565](https://stacks.math.columbia.edu/tag/0565)
* [Stacks Project, Tag 0573](https://stacks.math.columbia.edu/tag/0573)
* [Stacks Project, Tag 05KP](https://stacks.math.columbia.edu/tag/05KP)
-/

@[expose] public section

universe u

namespace Stacks.Divisors

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {ι : Type*}

/-- The `R`-linear map `M → (ι → M)` sending `m` to the family `(g i • m)`. Its injectivity is
the condition that the standard opens `D(g i)` cover the associated primes of `M`. -/
def smulPi (g : ι → R) : M →ₗ[R] ι → M :=
  LinearMap.pi fun i => g i • LinearMap.id

/-- The `i`-th component of `smulPi g m` is `g i • m`. -/
@[simp]
theorem smulPi_apply (g : ι → R) (m : M) (i : ι) : smulPi g m i = g i • m :=
  rfl

/-- A strict associated prime in the sense of Stacks 00LA is one in Mathlib's sense: the
annihilator of the witnessing element is the prime itself, so a fortiori has it as radical. -/
theorem mem_associatedPrimes_of_isAssociatedPrimeStacks {p : Ideal R}
    (h : IsAssociatedPrimeStacks R M p) : p ∈ associatedPrimes R M := by
  obtain ⟨hp, m, hm⟩ := h
  rw [Submodule.colon_span] at hm
  exact ⟨hp, m, hp.radical.symm.trans (congrArg Ideal.radical hm.symm)⟩

/-- Over a Noetherian ring, an associated prime in Mathlib's sense is a strict associated prime
in the sense of Stacks 00LA: Noetherianity upgrades the radical in Mathlib's definition to an
equality (`isAssociatedPrime_iff`). -/
theorem isAssociatedPrimeStacks_of_mem_associatedPrimes [IsNoetherianRing R] {p : Ideal R}
    (h : p ∈ associatedPrimes R M) : IsAssociatedPrimeStacks R M p := by
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at h
  obtain ⟨hp, m, hm⟩ := h
  exact ⟨hp, m, by rw [Submodule.colon_span, ← hm]⟩

/-- Over a Noetherian ring the two notions of associated prime agree. -/
theorem isAssociatedPrimeStacks_iff_mem_associatedPrimes [IsNoetherianRing R] {p : Ideal R} :
    IsAssociatedPrimeStacks R M p ↔ p ∈ associatedPrimes R M :=
  ⟨mem_associatedPrimes_of_isAssociatedPrimeStacks, isAssociatedPrimeStacks_of_mem_associatedPrimes⟩

/-- If the standard opens `D(g i)` cover the associated primes of `M` over a Noetherian ring,
then an element of `M` annihilated by a power of each `g i` is zero.

Were `m` nonzero, some associated prime `p` of `M` would contain the annihilator of `m`
(`exists_le_isAssociatedPrime_of_isNoetherianRing`), hence would contain a power of every
`g i` and so, being prime, every `g i` itself — contradicting the covering hypothesis. -/
theorem eq_zero_of_forall_exists_pow_smul_eq_zero [IsNoetherianRing R] {g : ι → R}
    (hg : ∀ p ∈ associatedPrimes R M, ∃ i, g i ∉ p) {m : M}
    (hm : ∀ i, ∃ k : ℕ, g i ^ k • m = 0) : m = 0 := by
  by_contra hm0
  obtain ⟨p, hp, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R m hm0
  obtain ⟨i, hi⟩ := hg p hp
  obtain ⟨k, hk⟩ := hm i
  exact hi <| hp.isPrime.mem_of_pow_mem k <|
    hle <| Submodule.mem_colon_singleton.mpr <| (Submodule.mem_bot R).mpr hk

/-- The direction of the criterion that needs no finiteness hypothesis: if `m ↦ (g i • m)` is
injective, then no associated prime of `M` — in the strict sense of Stacks 00LA — contains
every `g i`.

Indeed such a prime is the annihilator of some `m : M`, which is therefore killed by every
`g i` and hence zero; but the annihilator of `0` is the unit ideal, which is not prime. -/
theorem exists_notMem_of_injective_smulPi {g : ι → R}
    (h : Function.Injective (smulPi (M := M) g)) {p : Ideal R}
    (hp : IsAssociatedPrimeStacks R M p) : ∃ i, g i ∉ p := by
  obtain ⟨hprime, m, hm⟩ := hp
  by_contra hall
  simp only [not_exists, not_not] at hall
  have hsmul : ∀ i, g i • m = 0 := by
    intro i
    have : g i ∈ (⊥ : Submodule R M).colon (Submodule.span R {m}) := hm ▸ hall i
    rw [Submodule.colon_span, Submodule.mem_colon_singleton] at this
    exact (Submodule.mem_bot R).mp this
  have hm0 : m = 0 := by
    refine h ?_
    rw [map_zero]
    exact funext fun i => by simpa using hsmul i
  refine hprime.ne_top ?_
  rw [← hm, hm0, Submodule.span_zero_singleton, Submodule.colon_bot]

/-- A linear map `f` out of `M` is injective exactly when the `D(g i)` cover the associated
primes of `M`, provided the kernel of `f` contains the kernel of `smulPi g` and consists of
elements killed by a power of every `g i`. -/
private theorem injective_iff_forall_exists_notMem_of_ker [IsNoetherianRing R] {g : ι → R}
    {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (h₁ : ∀ m, smulPi g m = 0 → f m = 0) (h₂ : ∀ m, f m = 0 → ∀ i, ∃ k : ℕ, g i ^ k • m = 0) :
    Function.Injective f ↔ ∀ p ∈ associatedPrimes R M, ∃ i, g i ∉ p := by
  refine ⟨fun h p hp => exists_notMem_of_injective_smulPi ?_
    (isAssociatedPrimeStacks_of_mem_associatedPrimes hp), fun hg => ?_⟩
  · exact (injective_iff_map_eq_zero _).mpr fun m hm => h <| (h₁ m hm).trans (map_zero f).symm
  · exact (injective_iff_map_eq_zero _).mpr fun m hm =>
      eq_zero_of_forall_exists_pow_smul_eq_zero hg (h₂ m hm)

/-- Over a Noetherian ring, a canonical map from `M` into a product of localizations
`M_{g i}` is injective exactly when the standard opens `D(g i)` cover the associated primes
of `M`.

The localizations are arbitrary models, pinned only by `IsLocalizedModule`. -/
theorem injective_pi_iff_forall_exists_notMem [IsNoetherianRing R] (g : ι → R)
    {M' : ι → Type*} [∀ i, AddCommGroup (M' i)] [∀ i, Module R (M' i)]
    (l : ∀ i, M →ₗ[R] M' i)
    [∀ i, IsLocalizedModule (Submonoid.powers (g i)) (l i)] :
    Function.Injective (LinearMap.pi l) ↔ ∀ p ∈ associatedPrimes R M, ∃ i, g i ∉ p := by
  refine injective_iff_forall_exists_notMem_of_ker _ (fun m hm => funext fun i => ?_)
    fun m hm i => ?_
  · refine (IsLocalizedModule.eq_zero_iff (Submonoid.powers (g i)) (l i)).mpr
      ⟨⟨g i, Submonoid.mem_powers _⟩, ?_⟩
    simpa using congrFun hm i
  · obtain ⟨s, hs⟩ :=
      (IsLocalizedModule.eq_zero_iff (Submonoid.powers (g i)) (l i)).mp (congrFun hm i)
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    exact ⟨k, hk ▸ hs⟩

/-- Over a Noetherian ring, the map `m ↦ (g i • m)` is injective exactly when the standard
opens `D(g i)` cover the associated primes of `M`. This is the form the criterion takes in the
proofs of Stacks 0573 and Stacks 05KP, where it is reached through Stacks 0565. -/
theorem injective_smulPi_iff_forall_exists_notMem [IsNoetherianRing R] (g : ι → R) :
    Function.Injective (smulPi (M := M) g) ↔ ∀ p ∈ associatedPrimes R M, ∃ i, g i ∉ p :=
  injective_iff_forall_exists_notMem_of_ker _ (fun _ => id) fun m hm i => ⟨1, by
    simpa using congrFun hm i⟩

/-- An injective map of modules presented with a flat cokernel stays injective after base
change along any `R`-module `Q`.

This is Stacks 00HL applied to the short exact sequence `0 → N → P → C → 0`; the cokernel is
given by an arbitrary surjection `ψ` with `Function.Exact Φ ψ` rather than as the quotient
`P ⧸ LinearMap.range Φ`, since a consumer that obtains flatness from generic freeness
(Stacks 051T) meets the cokernel as some other model of it. -/
@[ega "0 6.1.2" "partial",
  ega "0 6.7.4" "partial",
  sga "1 IV 1.1" "(i)",
  sga "3 III 4.6.4" "more general"]
theorem injective_lTensor_of_flat_of_exact {N P C : Type*} [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [AddCommGroup C] [Module R C] [Module.Flat R C]
    (Φ : N →ₗ[R] P) (ψ : P →ₗ[R] C) (hΦ : Function.Injective Φ) (hex : Function.Exact Φ ψ)
    (hψ : Function.Surjective ψ) (Q : Type*) [AddCommGroup Q] [Module R Q] :
    Function.Injective (LinearMap.lTensor Q Φ) :=
  (flat_tor_zero (N := Q) Φ ψ hΦ hex hψ).1

/-- An injective map of modules whose cokernel is flat over the base stays injective after
base change along any `R`-module `Q`. The quotient form of
`Stacks.Divisors.injective_lTensor_of_flat_of_exact`. -/
@[ega "0 6.1.2" "partial"]
theorem injective_lTensor_of_flat_quotient {N P : Type*} [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (Φ : N →ₗ[R] P) (hΦ : Function.Injective Φ)
    [Module.Flat R (P ⧸ LinearMap.range Φ)] (Q : Type*) [AddCommGroup Q] [Module R Q] :
    Function.Injective (LinearMap.lTensor Q Φ) :=
  injective_lTensor_of_flat_of_exact Φ (LinearMap.range Φ).mkQ hΦ Φ.exact_map_mkQ_range
    (Submodule.mkQ_surjective _) Q

end Stacks.Divisors

end
