module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Weakly associated primes separate the elements of a module

Let `R` be a commutative ring and `M` an `R`-module. Write `Ann(m) = (R ∙ m).annihilator` for the
annihilator of an element `m` of `M`, and `WeakAss(M)` for the set of primes of `R` that are
minimal among the primes containing `Ann(m)` for some `m : M`. Localizing `M` at each `𝔭` in
`WeakAss(M)` assembles into an `R`-linear map `M ⟶ ∏_{𝔭 ∈ WeakAss(M)} M_𝔭`, and this file proves
that it is injective (Stacks 05CB): a nonzero module survives in the localization at one of its
weakly associated primes.

The argument is the source's, and it turns on the fact that an element of `M` survives in `M_𝔭`
exactly when `𝔭` contains its annihilator. Let `x : M` be nonzero. Then `Ann(x) ≠ R`, so some
prime `𝔭` is minimal among the primes containing `Ann(x)`; such a `𝔭` is weakly associated to `M`,
witnessed by `x` itself, and it contains `Ann(x)`, so `x` does not die in `M_𝔭`. Hence an element
dying in every `M_𝔭` with `𝔭 ∈ WeakAss(M)` is zero.

## Main results

* `Stacks.WeaklyAssociatedPrimes.Separation.solution`: the map from `M` to the product of the
  localizations of `M` at the weakly associated primes of `M` is injective.

## Implementation notes

The source runs the argument on the cyclic submodule `N = Rx`: a nonzero `N` has a weakly
associated prime `𝔭` (Lemma 0588), that `𝔭` lies in `WeakAss(M)` because `N ⊆ M` (Lemma 0548),
and `N_𝔭 ⊆ M_𝔭` is nonzero, contradicting the vanishing of `x`. Here `WeakAss(M)` is spelled by
the annihilators of the elements of `M`, so no transport along `N ⊆ M` is needed: a prime minimal
over `Ann(x)` is a weakly associated prime of `M` as it stands, witnessed by `x` itself, which is
Lemma 0548's inclusion `WeakAss(N) ⊆ WeakAss(M)` evaluated at the generator `x` of `N`, where it
is the identity. What is left are the two facts about a single element proved below, both over a
commutative semiring and for an arbitrary module:

* `annihilator_span_singleton_le_iff_map_ne_zero`, that `x` survives in `M_𝔭` if and only if
  `Ann(x) ≤ 𝔭`. This is the localization-level content the source draws from `N_𝔭 ≠ 0`, and it is
  the elementwise form of `Module.mem_support_iff_exists_annihilator`: that lemma reads the same
  equivalence off `Supp(M) = {𝔭 | ∃ m, Ann(m) ≤ 𝔭}` for the localization
  `LocalizedModule 𝔭.primeCompl M`, whereas here the localizations are abstract and it is one
  fixed element, not some element, that must survive.
* `exists_weaklyAssociatedPrime_annihilator_le`, that a nonzero element has a weakly associated
  prime containing its annihilator. This is what survives of Lemma 0588 — the contrapositive of
  its half saying that a module with no weakly associated prime is zero — together with the
  witnessing by `x` that makes the prime an index of the product.

## References

* [StacksProject 05CB](https://stacks.math.columbia.edu/tag/05CB)
-/

@[expose] public section

namespace Stacks.WeaklyAssociatedPrimes.Separation

/-- An element `x` of `M` survives in a localization `M_𝔭` of `M` at a prime `𝔭` exactly when `𝔭`
contains the annihilator of `x`: some `s ∉ 𝔭` kills `x` if and only if `Ann(x) ⊄ 𝔭`.

This is the elementwise form of `Module.mem_support_iff_exists_annihilator`, stated for an
arbitrary localization of `M` at `𝔭` rather than for `LocalizedModule 𝔭.primeCompl M`, and about
a fixed element rather than about the existence of one. -/
@[ega "0 1.7.1" "partial"]
private theorem annihilator_span_singleton_le_iff_map_ne_zero {R : Type*} [CommSemiring R]
    {M Mₚ : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid Mₚ] [Module R Mₚ]
    {p : PrimeSpectrum R} (f : M →ₗ[R] Mₚ) [IsLocalizedModule.AtPrime p.asIdeal f] (x : M) :
    (R ∙ x).annihilator ≤ p.asIdeal ↔ f x ≠ 0 := by
  rw [Ne, IsLocalizedModule.eq_zero_iff p.asIdeal.primeCompl f, not_exists]
  simp only [IsConcreteLE.le_iff, Submodule.mem_annihilator_span_singleton]
  exact ⟨fun h s hs => s.2 (h hs), fun h r hr => by_contra fun hrp => h ⟨r, hrp⟩ hr⟩

/-- A nonzero element `x` of `M` has a weakly associated prime of `M` containing `Ann(x)`: the
annihilator of `x` is a proper ideal, so some prime `𝔭` is minimal among the primes containing it,
and `x` itself witnesses that `𝔭` is weakly associated to `M`.

The conclusion is phrased over the primes indexing the product of `solution`, which is
`WeakAss(M)` as that statement spells it. -/
private theorem exists_weaklyAssociatedPrime_annihilator_le (R : Type*) [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M] {x : M} (hx : x ≠ 0) :
    ∃ q : {p : PrimeSpectrum R // ∃ m : M, p.asIdeal ∈ (R ∙ m).annihilator.minimalPrimes},
      (R ∙ x).annihilator ≤ q.1.asIdeal := by
  obtain ⟨⟨p, hp⟩⟩ := Ideal.nonempty_minimalPrimes
    (mt Submodule.annihilator_eq_top_iff.1 (by simpa using hx) : (R ∙ x).annihilator ≠ ⊤)
  exact ⟨⟨⟨p, hp.1.1⟩, x, hp⟩, hp.1.2⟩

public theorem solution
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {Mₚ : {p : PrimeSpectrum R // ∃ m : M, p.asIdeal ∈ (R ∙ m).annihilator.minimalPrimes} → Type*}
    [∀ p, AddCommMonoid (Mₚ p)] [∀ p, Module R (Mₚ p)] (f : ∀ p, M →ₗ[R] Mₚ p)
    [∀ p, IsLocalizedModule.AtPrime p.1.asIdeal (f p)] :
    Function.Injective (LinearMap.pi f) := by
  refine (injective_iff_map_eq_zero (LinearMap.pi f)).2 fun x hx => ?_
  by_contra hx0
  obtain ⟨q, hq⟩ := exists_weaklyAssociatedPrime_annihilator_le R hx0
  exact (annihilator_span_singleton_le_iff_map_ne_zero (f q) x).1 hq (congrFun hx q)

end Stacks.WeaklyAssociatedPrimes.Separation

end

/-!
# Weakly associated primes separate the elements of a module

Let `R` be a ring and let `M` be an `R`-module. A prime `𝔭` of `R` is *weakly associated* to `M`
if it is minimal among the primes containing the annihilator of some element of `M`, and
`WeakAss(M)` denotes the set of these primes. Localizing `M` at each of them assembles into a
canonical `R`-linear map

`M ⟶ ∏_{𝔭 ∈ WeakAss(M)} M_𝔭`,

and this map is injective: an element of `M` whose image in `M_𝔭` vanishes for every weakly
associated prime `𝔭` is zero. Equivalently, a nonzero module survives in the localization at one
of its weakly associated primes. Neither `R` nor `M` is assumed Noetherian or finite, which is
what weakly associated primes buy over associated ones.

## Main results

* `Module.injective_pi_localization_weaklyAssociatedPrimes`: the map from `M` to the product
  of the localizations of `M` at the weakly associated primes of `M` is injective.

## Implementation notes

`WeakAss(M)` is spelled out inline, as the primes `𝔭` with
`𝔭 ∈ (R ∙ m).annihilator.minimalPrimes` for some `m : M`: the annihilator of an element is the
annihilator of the submodule it generates, and minimality among the primes containing it is
`Ideal.minimalPrimes`. The product is indexed by exactly that set of primes and by nothing
larger, no condition beyond membership in it being imposed on the index; injectivity of the map
into a product over a set of primes containing `WeakAss(M)` follows by composing with the
projection onto the factors indexed by `WeakAss(M)`.

The localizations are kept abstract: any family of `R`-modules `Mₚ 𝔭` with `R`-linear maps
`f 𝔭 : M →ₗ[R] Mₚ 𝔭` exhibiting `Mₚ 𝔭` as a localization of `M` at `𝔭`
(`IsLocalizedModule.AtPrime`) will do, so the `𝔭`-th component of the map is pinned to be the
localization map at `𝔭` rather than merely asserted to exist, and the map itself is the
`R`-linear map `LinearMap.pi f` into the product. Taking `Mₚ 𝔭 = LocalizedModule 𝔭.primeCompl M`
with the canonical maps `LocalizedModule.mkLinearMap` returns the map of the source verbatim.
Base and scalars are the source's throughout: `M` and every `Mₚ 𝔭` are `R`-modules and the map
is `R`-linear, no `R_𝔭`-module structure being needed to state the result.

For `R = M = ℤ` the only weakly associated prime is `(0)`, and the statement is the injectivity
of `ℤ → ℚ`.

The companion statement indexed by the maximal ideals of `R`, which holds for every `R`-module
and involves no minimality over an annihilator, is `Module.eq_of_localization_maximal`; here the
index set depends on `M`, and it is that dependence that makes `WeakAss(M)` enough.

## References

* [StackProject 05CB](https://stacks.math.columbia.edu/tag/05CB)

## Tags

weakly associated prime, localization, annihilator, minimal prime
-/

@[expose] public section

/-- **Stacks 05CB.** Let `R` be a ring and `M` an `R`-module. The canonical map
`M → ∏_{𝔭 ∈ WeakAss(M)} M_𝔭` from `M` to the product of its localizations at the weakly
associated primes of `M` — the primes minimal over the annihilator of an element of `M` — is
injective. -/
@[stacks 05CB]
public theorem Module.injective_pi_localization_weaklyAssociatedPrimes
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {Mₚ : {p : PrimeSpectrum R // ∃ m : M, p.asIdeal ∈ (R ∙ m).annihilator.minimalPrimes} → Type*}
    [∀ p, AddCommMonoid (Mₚ p)] [∀ p, Module R (Mₚ p)] (f : ∀ p, M →ₗ[R] Mₚ p)
    [∀ p, IsLocalizedModule.AtPrime p.1.asIdeal (f p)] :
    Function.Injective (LinearMap.pi f) := by apply
                                                Stacks.WeaklyAssociatedPrimes.Separation.solution

end
