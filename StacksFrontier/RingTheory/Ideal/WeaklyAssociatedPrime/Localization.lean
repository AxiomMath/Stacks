module

import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Regular.IsSMulRegular
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.WeaklyAssociated
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.Defs

@[expose] public section

/-!
# Weakly associated primes are unchanged by a localization at nonzerodivisors

Let `R` be a commutative semiring, let `M` be an `R`-module, let `S ⊆ R` be a multiplicative subset
every element of which acts as a nonzerodivisor on `M`, and let `f : M →ₗ[R] M'` exhibit `M'` as
the localization `S⁻¹M`. Write `WeakAss(N)` for the set of primes of `R` minimal among the primes
containing the annihilator `Ann(n) = (R ∙ n).annihilator` of an element `n` of an `R`-module `N`.
This file proves `Module.weaklyAssociatedPrimes_eq_of_isSMulRegular_of_isLocalizedModule`
(Stacks 05CA): `WeakAss(M) = WeakAss(S⁻¹M)`.

The hypothesis on `S` says exactly that `f` is injective
(`IsLocalizedModule.injective_iff_isRegular`), so the inclusion `WeakAss(M) ⊆ WeakAss(S⁻¹M)` is
Stacks 0548 applied to `f`. The reverse inclusion is an equality of ideals rather than an argument
about primes: an element of `S⁻¹M` is of the form `m/s`, that is, it is an `m'` with `s • m' = f m`
for some `m : M` and `s ∈ S`, and such an `m'` has the same annihilator in `R` as `m`. Minimality
over the annihilator is then a statement about the same ideal on both sides, so nothing further is
needed.

That equality of annihilators, `annihilator_span_singleton_eq_of_smul_eq_map`, is the composite of
two facts about the annihilator of a single element, each holding in any module: it is unchanged by
an injective linear map, and it is unchanged by multiplying the element by a nonzerodivisor. Since
every `s ∈ S` acts injectively on the localization `S⁻¹M`, they give
`Ann(m') = Ann(s • m') = Ann(f m) = Ann(m)`.

## Main results

* `Stacks.WeaklyAssociatedPrimes.Localized.solution`: the equality `WeakAss(M) = WeakAss(S⁻¹M)`.

## References

* [StacksProject 05CA](https://stacks.math.columbia.edu/tag/05CA)
-/

@[expose] public section

namespace Stacks.WeaklyAssociatedPrimes.Localized

/-- An injective linear map preserves the annihilator of an element: `Ann(f m) = Ann(m)`. -/
private theorem annihilator_span_singleton_map_of_injective {R : Type*} [CommSemiring R]
    {M M' : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
    {f : M →ₗ[R] M'} (hf : Function.Injective f) (m : M) :
    (R ∙ f m).annihilator = (R ∙ m).annihilator := by
  ext r
  simp only [Submodule.mem_annihilator_span_singleton, ← map_smul, LinearMap.map_eq_zero_iff f hf]

/-- Multiplying an element by a nonzerodivisor does not change its annihilator:
`Ann(s • m) = Ann(m)` for `s` acting injectively on the ambient module. -/
private theorem annihilator_span_singleton_smul_of_isSMulRegular {R : Type*} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M] {s : R} (hs : IsSMulRegular M s) (m : M) :
    (R ∙ s • m).annihilator = (R ∙ m).annihilator := by
  ext r
  simp only [Submodule.mem_annihilator_span_singleton, smul_comm r s]
  exact ⟨hs.right_eq_zero_of_smul, fun h => by rw [h, smul_zero]⟩

/-- An element `m/s` of a localization `S⁻¹M` at a submonoid acting on `M` by nonzerodivisors has
the same annihilator in `R` as `m` does: if `s • m' = f m` with `s ∈ S`, then `Ann(m') = Ann(m)`.
The two hypotheses enter separately — `s` is a nonzerodivisor on `S⁻¹M` because `S` is inverted
there, and `f` is injective because every `s ∈ S` is a nonzerodivisor on `M`. -/
private theorem annihilator_span_singleton_eq_of_smul_eq_map {R : Type*} [CommSemiring R]
    {M M' : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
    (S : Submonoid R) (f : M →ₗ[R] M') [IsLocalizedModule S f] (hf : Function.Injective f)
    {m : M} {s : S} {m' : M'} (hs : (s : R) • m' = f m) :
    (R ∙ m').annihilator = (R ∙ m).annihilator := by
  rw [← annihilator_span_singleton_smul_of_isSMulRegular
    (fun _ _ h => IsLocalizedModule.smul_injective f s h) m', hs,
    annihilator_span_singleton_map_of_injective hf]

/-- Localizing at a submonoid `S` acting on `M` by nonzerodivisors does not change the weakly
associated primes: if `f : M →ₗ[R] M'` exhibits `M'` as `S⁻¹M`, then the primes minimal over the
annihilator of some element of `M` are exactly those minimal over the annihilator of some element
of `M'`. -/
public theorem solution
    {R : Type*} [CommSemiring R] {M M' : Type*}
    [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
    (S : Submonoid R) (f : M →ₗ[R] M') [IsLocalizedModule S f]
    (hS : ∀ s ∈ S, IsSMulRegular M s) :
    {p : Ideal R | ∃ m : M, p ∈ (R ∙ m).annihilator.minimalPrimes} =
      {p : Ideal R | ∃ m : M', p ∈ (R ∙ m).annihilator.minimalPrimes} := by
  have hf : Function.Injective f :=
    (IsLocalizedModule.injective_iff_isRegular S f).2 fun c => hS c c.2
  refine subset_antisymm (Module.weaklyAssociatedPrimes_subset_of_injective hf) ?_
  rintro p ⟨m', hm'⟩
  obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj S f m'
  exact ⟨m, annihilator_span_singleton_eq_of_smul_eq_map S f hf hs ▸ hm'⟩

end Stacks.WeaklyAssociatedPrimes.Localized

end

/-!
# Weakly associated primes are unchanged by a localization at regular elements

Let `R` be a ring, let `M` be an `R`-module and let `S ⊆ R` be a multiplicative subset every
element of which is a nonzerodivisor on `M`. A prime `p` of `R` is *weakly associated* to a module
`N` when `p` is minimal among the primes containing the annihilator of some element of `N`, and
`WeakAss(N)` denotes the set of these primes. Then

`WeakAss(M) = WeakAss(S⁻¹M)`,

an equality of sets of primes of `R`. One inclusion is the statement that `M ↪ S⁻¹M` (which is
where the hypothesis on `S` enters) together with Tag 0548; the other is the observation that an
element `m/s` of `S⁻¹M` has the same annihilator in `R` as the element `m` of `M`, so the two
sides are in fact cut out by the same family of ideals. Neither `R` nor `M` is assumed Noetherian
or finite, which is what weakly associated primes buy over associated ones.

## Main results

* `Module.weaklyAssociatedPrimes_eq_of_isSMulRegular_of_isLocalizedModule`: if every element of
  `S` acts as a nonzerodivisor on `M`, then `M` and its localization at `S` have the same weakly
  associated primes.

## Implementation notes

`WeakAss(N)` is spelled out inline, as the set of primes `p` with
`p ∈ (R ∙ m).annihilator.minimalPrimes` for some `m : N`: the annihilator of an element is the
annihilator of the cyclic submodule it generates, and minimality among the primes containing an
ideal is `Ideal.minimalPrimes`. This is the spelling of Tag 0548
(`Module.weaklyAssociatedPrimes_subset_of_injective`) and of Tag 05CB
(`Module.injective_pi_localization_weaklyAssociatedPrimes`), which keeps the files of this family
interchangeable; the notion has no name in Mathlib.

The localization is kept abstract: rather than fixing `S⁻¹M = LocalizedModule S M`, the statement
takes any `R`-module `M'` and any `R`-linear `f : M →ₗ[R] M'` exhibiting `M'` as the localization
of `M` at `S` (`IsLocalizedModule S f`). Taking `M' = LocalizedModule S M` with
`f = LocalizedModule.mkLinearMap S M` returns the source's statement verbatim, and no user of this
lemma has to undo a choice of model. `S` is a `Submonoid R`, Mathlib's spelling of a multiplicative
subset, and "every `s ∈ S` is a nonzerodivisor on `M`" is `∀ s ∈ S, IsSMulRegular M s`; by
`IsLocalizedModule.injective_iff_isRegular` this hypothesis is *equivalent* to injectivity of `f`,
i.e. to the inclusion `M ⊆ S⁻¹M` the source uses, so nothing is lost or gained by either wording.

Generality beyond the source: `R` need only be a `CommSemiring` and the two modules
`AddCommMonoid`s. Both inclusions are assertions about annihilators of single elements, which
need no subtraction — the source's route through `M ⊆ S⁻¹M` is available verbatim there.

Faithfulness. (1) Both hypotheses are live: without regularity the statement fails for `R = ℤ`,
`M = ℤ/2` and `S = {1, 2, 4, …}`, where `S⁻¹M = 0` and so `WeakAss(M) = {(2)} ≠ ∅ = WeakAss(S⁻¹M)`;
and without `IsLocalizedModule S f` there is no relation between the two sets at all.
(2) The scalars are the source's: `M` and `M'` are `R`-modules, `f` is `R`-linear, and both sides
are sets of primes of `R` — no `S⁻¹R`-module structure and no comparison of `Spec(S⁻¹R)` with
`Spec R` enters, that being the content of Tag 05C9 instead.
(3) The canonical map is pinned, not merely asserted to exist: `M'` is a localization of `M` *along
the given `f`*, so the module whose weakly associated primes are computed is the localization of
`M` by that map.
(4) The instantiation is not degenerate: for `R = M = ℤ` and `S = ℤ \ {0}`, so that `S⁻¹M = ℚ`,
both sides are `{(0)}` and both are nonempty.

## References

* [StackProject 05CA](https://stacks.math.columbia.edu/tag/05CA)

## Tags

weakly associated prime, localization, nonzerodivisor, regular element, annihilator, minimal prime
-/

@[expose] public section

/-- **Stacks 05CA.** Let `R` be a ring, `M` an `R`-module and `S ⊆ R` a multiplicative subset such
that every `s ∈ S` is a nonzerodivisor on `M`. Then `M` and its localization `S⁻¹M` have the same
weakly associated primes: `WeakAss(M) = WeakAss(S⁻¹M)`, where `WeakAss(N)` is the set of primes of
`R` minimal over the annihilator of an element of `N`. -/
@[stacks 05CA]
public theorem Module.weaklyAssociatedPrimes_eq_of_isSMulRegular_of_isLocalizedModule
    {R : Type*} [CommSemiring R] {M M' : Type*}
    [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
    (S : Submonoid R) (f : M →ₗ[R] M') [IsLocalizedModule S f]
    (hS : ∀ s ∈ S, IsSMulRegular M s) :
    {p : Ideal R | ∃ m : M, p ∈ (R ∙ m).annihilator.minimalPrimes} =
      {p : Ideal R | ∃ m : M', p ∈ (R ∙ m).annihilator.minimalPrimes} :=
    by exact Stacks.WeaklyAssociatedPrimes.Localized.solution S f hS

end

end

/-!
# Weakly associated primes and base change to the fraction field

Stacks tag 05CC (Lemma 10.66.18). Let `R → S` be a ring map and `N` an `S`-module. Assume
`N` is flat as an `R`-module and `R` is a domain with fraction field `K = Frac(R)`. Then,
via the canonical inclusion `Spec(S ⊗_R K) ↪ Spec(S)`, we have an equality of subsets of
`Spec(S)`:

  `WeakAss_S(N) = WeakAss_{S ⊗_R K}(N ⊗_R K)`.

Here `WeakAss` denotes the set of weakly associated primes (Stacks tag 0547): `p` is weakly
associated to a module `M` over a ring `A` if there is `m ∈ M` such that `p` is minimal
among the primes containing the annihilator `Ann_A(m) = { f ∈ A | f • m = 0 }`, which is
`(A ∙ m).annihilator`; thus `IsWeaklyAssociatedPrime A M p` unfolds to
`∃ m, p ∈ (A ∙ m).annihilator.minimalPrimes`.

## Identification of `S ⊗_R K` with the localization `T⁻¹ S`

Let `T = R \ {0}`. Since `R` is a domain, `R \ {0}` is exactly the monoid of nonzero
divisors `nonZeroDivisors R`. Let `T_S` denote the image of `T` in `S`, i.e.
`baseChangeSubmonoid R S = Algebra.algebraMapSubmonoid S (nonZeroDivisors R)`. There are
canonical identifications

  `S ⊗_R K ≅ T_S⁻¹ S = Localization T_S`   and   `N ⊗_R K ≅ T_S⁻¹ N = LocalizedModule T_S N`.

Indeed `IsLocalization.tensor` shows `S ⊗_R K` is a localization of `S` at `T_S`, hence
canonically `S`-isomorphic to `Localization T_S`. Working with `Localization T_S` and
`LocalizedModule T_S N` is therefore equivalent to working with `S ⊗_R K` and `N ⊗_R K`, but
it provides the well-behaved module structure
`Module (Localization T_S) (LocalizedModule T_S N)` that is needed to even speak of
`WeakAss_{S ⊗_R K}(N ⊗_R K)`. Under this identification the canonical inclusion of spectra
`Spec(S ⊗_R K) ↪ Spec(S)` is `PrimeSpectrum.comap (algebraMap S (Localization T_S))`.

Throughout, `T_S = baseChangeSubmonoid R S`, `A = Localization T_S` and
`M = LocalizedModule T_S N`.
-/

@[expose] public section

namespace Stacks.WeaklyAssociatedPrimes.BaseChange

variable (R S N : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- `T_S` is the image in `S` of the nonzero elements `R \ {0}` of the domain `R`.
Since `R` is a domain, `R \ {0} = nonZeroDivisors R`, so `T_S` is the multiplicative
set through which `S → S ⊗_R K` is the localization map. -/
noncomputable abbrev baseChangeSubmonoid : Submonoid S :=
  Algebra.algebraMapSubmonoid S (nonZeroDivisors R)

/-- Every element `t` of `T_S` acts as a nonzerodivisor on `N` when `N` is flat over the
domain `R`.

Membership `t ∈ T_S = Algebra.algebraMapSubmonoid S (nonZeroDivisors R)` means
`t = algebraMap R S r` for some `r ∈ nonZeroDivisors R`, and flatness of `N` over `R` gives
`IsSMulRegular N r`. By `IsScalarTower R S N` we have `t • n = r • n` for all `n : N`, so
the two scalar actions on `N` agree and `IsSMulRegular N t` follows. -/
theorem isSMulRegular_of_mem_baseChangeSubmonoid [Module.Flat R N]
    {t : S} (ht : t ∈ baseChangeSubmonoid R S) : IsSMulRegular N t := by
  obtain ⟨r, hr, hrt⟩ := Submonoid.mem_map.mp ht
  have hreg : IsSMulRegular N r := Module.Flat.isSMulRegular_of_nonZeroDivisors hr
  have hsmul : ∀ n : N, t • n = r • n := fun n => by rw [← hrt, algebraMap_smul]
  exact fun x y hxy => hreg (by simpa only [← hsmul] using hxy)

/-- Any prime `q` weakly associated to `N` over `S` is disjoint from `T_S`.

Suppose `q.asIdeal ∈ (S ∙ m).annihilator.minimalPrimes` for some `m : N`, and let
`t ∈ T_S`. Then `t` is regular on `N`, hence regular on the cyclic submodule `S ∙ m`, and a
minimal prime over the annihilator of `S ∙ m` consists of zerodivisors on `S ∙ m`; so
`t ∉ q.asIdeal`, i.e. `Disjoint (T_S : Set S) q.asIdeal`. -/
theorem disjoint_baseChangeSubmonoid_of_weakAss [Module.Flat R N]
    {q : PrimeSpectrum S} (hq : IsWeaklyAssociatedPrime S N q.asIdeal) :
    Disjoint (baseChangeSubmonoid R S : Set S) (q.asIdeal : Set S) := by
  obtain ⟨m, hm⟩ := hq
  rw [Set.disjoint_left]
  intro t ht htq
  -- `t` is SMul-regular on `N`, hence on the cyclic submodule `S ∙ m`.
  have hreg : IsSMulRegular N t := isSMulRegular_of_mem_baseChangeSubmonoid R S N ht
  have hregSub : IsSMulRegular (S ∙ m) t := IsSMulRegular.submodule (S ∙ m) t hreg
  -- `q.asIdeal` is a minimal prime over `Module.annihilator S (S ∙ m)`, so it avoids `t`.
  have hann : (S ∙ m).annihilator = Module.annihilator S (S ∙ m) :=
    Submodule.toSubMulAction_inj.mp rfl
  rw [hann] at hm
  exact hregSub.notMem_of_mem_minimalPrimes hm htq

/-- Since every `t ∈ T_S` is regular on `N`, the annihilator of `m : N` over `S` is the
contraction of the annihilator of its image in `M = LocalizedModule T_S N` over `A`. -/
theorem annihilator_span_singleton_eq_comap [Module.Flat R N] (m : N) :
    (S ∙ m).annihilator = Ideal.comap (algebraMap S (Localization (baseChangeSubmonoid R S)))
      (Localization (baseChangeSubmonoid R S) ∙
        LocalizedModule.mkLinearMap (baseChangeSubmonoid R S) N m).annihilator := by
  ext r
  rw [Submodule.mem_annihilator_span_singleton, Ideal.mem_comap,
    Submodule.mem_annihilator_span_singleton, algebraMap_smul, ← map_smul]
  refine ⟨fun h => by rw [h, map_zero], fun h => ?_⟩
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (baseChangeSubmonoid R S) _).mp h
  refine isSMulRegular_of_mem_baseChangeSubmonoid R S N s.property ?_
  change (s : S) • (r • m) = (s : S) • 0
  simpa only [Submonoid.smul_def, smul_zero] using hs

/-- For a prime `q` of `S` that is the contraction of a prime `q'` of `A` (equivalently, `q`
is disjoint from `T_S`), `q` is weakly associated to `N` over `S` if and only if `q'` is
weakly associated to `M = LocalizedModule T_S N` over `A = Localization T_S`.

The localization map `f := LocalizedModule.mkLinearMap T_S N : N → M` is `S`-linear and
realizes `M` as `IsLocalizedModule T_S f`, and because every `t ∈ T_S` is regular on `N`,
for `m : N` the annihilator of the cyclic submodule satisfies
`(S ∙ m).annihilator = Ideal.comap (algebraMap S A) (A ∙ f m).annihilator`. By
`IsLocalization.minimalPrimes_comap`, taking minimal primes commutes with this contraction,
so the minimal primes over `(S ∙ m).annihilator` correspond bijectively, via `comap`, to
the minimal primes over `(A ∙ f m).annihilator`. Unwinding `IsWeaklyAssociatedPrime` on
both sides then gives the equivalence: `m` ranges over `N` on the left and `f m` over `M` on
the right, and every element of `M` is `f m'` up to a unit scalar from `T_S`, which does not
change the annihilator, so the existential over `M` reduces to one over `N`. -/
theorem weakAss_localization_iff [Module.Flat R N]
    {q : PrimeSpectrum S}
    {q' : PrimeSpectrum (Localization (baseChangeSubmonoid R S))}
    (hqq' : PrimeSpectrum.comap (algebraMap S (Localization (baseChangeSubmonoid R S))) q' = q) :
    IsWeaklyAssociatedPrime S N q.asIdeal ↔
      IsWeaklyAssociatedPrime (Localization (baseChangeSubmonoid R S))
        (LocalizedModule (baseChangeSubmonoid R S) N) q'.asIdeal := by
  have hcomap : Ideal.comap (algebraMap S (Localization (baseChangeSubmonoid R S)))
      q'.asIdeal = q.asIdeal := by
    subst hqq'
    rfl
  set f := LocalizedModule.mkLinearMap (baseChangeSubmonoid R S) N
  have core : ∀ m : N, (q.asIdeal ∈ (S ∙ m).annihilator.minimalPrimes ↔
      q'.asIdeal ∈ (Localization (baseChangeSubmonoid R S) ∙ f m).annihilator.minimalPrimes) := by
    intro m
    rw [annihilator_span_singleton_eq_comap R S N m, IsLocalization.minimalPrimes_comap
      (baseChangeSubmonoid R S) (Localization (baseChangeSubmonoid R S))]
    refine ⟨fun ⟨P, hP, hPe⟩ => ?_, fun hq' => ⟨q'.asIdeal, hq', hcomap⟩⟩
    obtain rfl : P = q'.asIdeal := by
      rw [← IsLocalization.map_under (baseChangeSubmonoid R S) _ P,
        ← IsLocalization.map_under (baseChangeSubmonoid R S) _ q'.asIdeal]
      exact congrArg _ (hPe.trans hcomap.symm)
    exact hP
  refine ⟨fun ⟨m, hm⟩ => ⟨f m, (core m).mp hm⟩, fun ⟨m', hm'⟩ => ?_⟩
  obtain ⟨⟨n, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective (baseChangeSubmonoid R S) f m'
  have hfn : f n = algebraMap S (Localization (baseChangeSubmonoid R S)) s •
      IsLocalizedModule.mk' f n s := by
    rw [algebraMap_smul]
    exact (IsLocalizedModule.mk'_cancel' f n s).symm
  rw [Function.uncurry_apply_pair, ← Submodule.span_singleton_smul_eq
    (IsLocalization.map_units (Localization (baseChangeSubmonoid R S)) s), ← hfn] at hm'
  exact ⟨n, (core n).mpr hm'⟩

/-- Stacks tag 05CC (Lemma 10.66.18): let `R → S` be a ring map and `N` an `S`-module that
is flat over the domain `R` (with `Module R N` compatible with the `S`-action via
`IsScalarTower R S N`). Identifying `S ⊗_R K` with `A = Localization T_S`, `N ⊗_R K` with
`M = LocalizedModule T_S N`, and `Spec(S ⊗_R K)` with its image in `Spec(S)` under
`PrimeSpectrum.comap (algebraMap S A)`, the weakly associated primes of `N` over `S` are
exactly the images of the weakly associated primes of `N ⊗_R K` over `S ⊗_R K`: a prime `q`
of `S` is weakly associated to `N` if and only if there is a prime `q'` of `A` that is
weakly associated to `M` and whose contraction along `S → A` equals `q`. -/
@[stacks 05CC]
theorem weakAss_eq_of_flat_domain
    [Module.Flat R N] (q : PrimeSpectrum S) :
    IsWeaklyAssociatedPrime S N q.asIdeal ↔
      ∃ q' : PrimeSpectrum (Localization (baseChangeSubmonoid R S)),
        IsWeaklyAssociatedPrime (Localization (baseChangeSubmonoid R S))
          (LocalizedModule (baseChangeSubmonoid R S) N) q'.asIdeal ∧
        PrimeSpectrum.comap (algebraMap S (Localization (baseChangeSubmonoid R S))) q' = q := by
  refine ⟨fun hq => ?_, ?_⟩
  · obtain ⟨q', hq'⟩ : q ∈ Set.range (PrimeSpectrum.comap
        (algebraMap S (Localization (baseChangeSubmonoid R S)))) := by
      rw [PrimeSpectrum.localization_comap_range _ (baseChangeSubmonoid R S)]
      exact disjoint_baseChangeSubmonoid_of_weakAss R S N hq
    exact ⟨q', (weakAss_localization_iff R S N hq').mp hq, hq'⟩
  · rintro ⟨q', hq', rfl⟩
    exact (weakAss_localization_iff R S N rfl).mpr hq'

/-! ### The identification of `S ⊗_R K` with the localization `T_S⁻¹ S` -/

/-- `S ⊗_R K` is a localization of `S` at the multiplicative set `T_S`, so that
`Spec(S ⊗_R K)` injects into `Spec(S)` with image the primes disjoint from `T_S`. -/
theorem isLocalization_tensor_fractionRing (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] : IsLocalization (baseChangeSubmonoid R S) (TensorProduct R S K) :=
  IsLocalization.tensor K (nonZeroDivisors R)

/-- `S ⊗_R K` is canonically the localization
`Localization (baseChangeSubmonoid R S) = T_S⁻¹ S`, as `S`-algebras. -/
noncomputable def baseChangeAlgEquivLocalization (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] : Localization (baseChangeSubmonoid R S) ≃ₐ[S] TensorProduct R S K :=
  letI := isLocalization_tensor_fractionRing R S K
  IsLocalization.algEquiv (baseChangeSubmonoid R S) _ _

end Stacks.WeaklyAssociatedPrimes.BaseChange

end
