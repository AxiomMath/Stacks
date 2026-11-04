module

public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.FiniteCaseAlgebra
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The per-index trivialisation in the finite case of property (B)

The finite case of property (B) for the étale topology, [Stacks, Tag 04DQ], is reduced by
`Stacks.EtaleCohomology.exists_etale_completeOrthogonalIdempotents_tensorBaseChange` to the
following situation: a base ring `A'` with a prime `p'`, a module-finite `A'`-algebra `P` (the ring
of the fibre product after an étale base change of the base), an étale `P`-algebra `E` whose
spectrum surjects onto `Spec P` (a single affine étale covering of the fibre product), and two
complete orthogonal families of idempotents, one of `P` and one of `E`, whose factors carry the
finiteness and residue-field information the étale local structure theorem [Stacks, Tag 00UL]
supplies.

This file performs the step that compares one factor `F = P[1/b]` of the first decomposition with
one factor `D = E[1/c]` of the second. The comparison needs three things, and they are what this
file provides:

* `F → D` is étale, module-finite and flat, and `D` is unramified over `F` at every prime — all
  transported from `Algebra.Etale P E` to the two localisations;
* the prime of `D` over the prime of `F` below it is the *only* one, so that
  `Stacks.EtaleCohomology.exists_notMem_bijective_awayMap_of_isPurelyInseparable` applies;
* an element of `F` outside the chosen prime can be replaced by an element of the *base* `A'`
  outside `p'`, which is what makes the finitely many inversions performed over the finitely many
  indices collapse into a single étale neighbourhood of `p'`.

## Main results

* `Stacks.EtaleCohomology.etale_of_isLocalizationAway_pair`: a localisation of an étale algebra at
  one element is étale over the localisation of the base at one element, whenever the two are
  compatible.
* `Stacks.EtaleCohomology.isUnramifiedAt_of_formallyUnramified`: a formally unramified algebra is
  unramified at every prime.
* `Stacks.EtaleCohomology.moduleFinite_of_moduleFinite_base`: module-finiteness over the base
  passes to module-finiteness over an intermediate algebra.
* `Stacks.EtaleCohomology.primesOver_eq_singleton_of_forall_eq`: if an algebra has at most one
  prime over a prime of the base, then a prime over an intermediate prime is the only one.
* `Stacks.EtaleCohomology.isPrime_map_algebraMap_of_notMem`,
  `Stacks.EtaleCohomology.under_map_algebraMap_of_notMem` and
  `Stacks.EtaleCohomology.liesOver_map_algebraMap_of_notMem`: the prime of `R[1/x]` cut out by a
  prime of `R` avoiding `x` — prime, contracting back, and lying over the same prime of the base.
* `Stacks.EtaleCohomology.forall_eq_of_forall_eq_away` and
  `Stacks.EtaleCohomology.forall_eq_map_of_forall_eq_away`: uniqueness of the prime over `p'`
  passes from a ring to its localisation away from one element, in the two shapes the per-index
  trivialisation asks for it.
* `Stacks.EtaleCohomology.exists_notMem_mem_radical_span_of_forall_notMem`: **pushing an element of
  a module-finite algebra down to the base.** If no prime of a module-finite `A'`-algebra `F` lying
  over `p'` contains `r`, then a single element of `A'` outside `p'` has a power that is a multiple
  of `r`.
* `Stacks.EtaleCohomology.exists_notMem_mem_radical_span_of_unique_prime` and
  `Stacks.EtaleCohomology.exists_notMem_isUnit_of_unique_prime`: the same with the hypothesis in
  the form the local structure theorem delivers — `r` avoids the unique prime over `p'` — and with
  the conclusion read as invertibility of `r` after one localisation of the base.
* `Stacks.EtaleCohomology.isOpen_range_comap_of_etale`: the spectrum of an étale algebra has open
  image.
* `Stacks.EtaleCohomology.exists_notMem_bijective_awayMap_of_etale_pair` and
  `Stacks.EtaleCohomology.exists_notMem_bijective_awayMap_of_etale_pair_of_liesOver`: **the
  comparison of one factor of each decomposition.** Given surjectivity on spectra, `F → D` becomes
  an isomorphism after inverting a single element of `F` outside the chosen prime. The second form
  installs the algebra structures on the local rings with
  `Localization.AtPrime.algebraOfLiesOver`, which is the shape the local structure theorem's
  residue-field conclusion comes in.
* `Stacks.EtaleCohomology.surjective_comap_awayMap_of_basicOpen_subset` and
  `Stacks.EtaleCohomology.exists_notMem_surjective_comap_awayMap`: the shrinking of the base that
  makes the covering surjective on spectra.
* `Stacks.EtaleCohomology.exists_notMem_surjective_awayMap_of_localRingHom_surjective`:
  **the surjectivity half of the trivialisation, with no hypothesis on the kernel.** If `q` is the
  only prime of a module-finite algebra `S` over a prime `p` of `R` and `R_p → S_q` is surjective,
  then `R[1/r] → S[1/r]` is surjective for a single `r ∉ p`.
* `Stacks.EtaleCohomology.injective_awayMap_of_surjective_comap`: **the injectivity half.** A flat
  algebra whose spectrum surjects after one localisation has injective structure map there, by
  faithful flatness.
* `Stacks.EtaleCohomology.bijective_awayMap_of_dvd_of_basicOpen_subset`: the two halves combined at
  a common multiple of the two elements they produce.
* `Stacks.EtaleCohomology.exists_notMem_bijective_awayMap_algebraMap_of_etale_pair`: **the
  comparison of one factor of each decomposition, with the element inverted taken from the base and
  surjectivity on spectra no longer assumed.** This is the form the finite case of property (B)
  uses, since the étale neighbourhood of the base it produces must be a single scheme.

## References

* [Stacks Project, Tag 04DQ](https://stacks.math.columbia.edu/tag/04DQ)
* [Stacks Project, Tag 00UL](https://stacks.math.columbia.edu/tag/00UL)
-/

@[expose] public section

universe u v w

namespace Stacks.EtaleCohomology

section AwayPair

/-- **A factor of an étale algebra is étale over a factor of the base.** Let `E` be étale over `P`,
let `F` be the localisation of `P` away from an element `x`, and let `D` be the localisation of `E`
away from an element `y`. If `D` is an `F`-algebra compatibly with `P`, then `D` is étale over `F`.

Both localisations are étale over `P` — a localisation at one element always is — so `P → D` is
étale as a composite, and an algebra which is étale over `P` is étale over any intermediate algebra
which is itself étale over `P`.

In the finite case of property (B), [Stacks, Tag 04DQ], `F` is one factor `P[1/b]` of the
decomposition of the fibre product and `D` one factor `E[1/c]` of the decomposition of the étale
covering; the `F`-algebra structure on `D` comes from
`Stacks.EtaleCohomology.exists_notMem_algebraMap_eq_one`, which makes `b` equal to `1` in `D`. -/
theorem etale_of_isLocalizationAway_pair {P E F D : Type*} [CommRing P] [CommRing E] [CommRing F]
    [CommRing D] [Algebra P E] [Algebra P F] [Algebra P D] [Algebra E D] [Algebra F D]
    [IsScalarTower P E D] [IsScalarTower P F D] [Algebra.Etale P E]
    (x : P) [IsLocalization.Away x F] (y : E) [IsLocalization.Away y D] :
    Algebra.Etale F D :=
  have : Algebra.Etale P F := Algebra.Etale.of_isLocalizationAway x
  have : Algebra.Etale E D := Algebra.Etale.of_isLocalizationAway y
  have : Algebra.Etale P D := Algebra.Etale.comp P E D
  Algebra.Etale.of_restrictScalars (R := P) (A := F) (B := D)

/-- **A formally unramified algebra is unramified at every prime.** `Algebra.IsUnramifiedAt R q` is
formal unramifiedness of the local ring at `q`, which is a localisation of `S` and hence formally
unramified over `S`; the composite `R → S → S_q` is then formally unramified.

This is how the hypothesis `Algebra.IsUnramifiedAt F s` of
`Stacks.EtaleCohomology.exists_notMem_bijective_awayMap_of_isPurelyInseparable` is met from
étaleness of `F → D`. -/
theorem isUnramifiedAt_of_formallyUnramified (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FormallyUnramified R S] (q : Ideal S) [q.IsPrime] :
    Algebra.IsUnramifiedAt R q :=
  Algebra.FormallyUnramified.comp R S (Localization.AtPrime q)

/-- **Module-finiteness over the base implies module-finiteness over an intermediate algebra.**
This is `Module.Finite.of_restrictScalars_finite`, recorded here because it is how the hypothesis
`Module.Finite F D` of `Stacks.EtaleCohomology.exists_notMem_bijective_awayMap` is met: the factor
`D = E[1/c]` is module-finite over the base `A'` by [Stacks, Tag 00UL], and `F` sits between the
two. -/
theorem moduleFinite_of_moduleFinite_base (A' F D : Type*) [CommRing A'] [CommRing F] [CommRing D]
    [Algebra A' F] [Algebra A' D] [Algebra F D] [IsScalarTower A' F D] [Module.Finite A' D] :
    Module.Finite F D :=
  Module.Finite.of_restrictScalars_finite A' F D

/-- **A prime over an intermediate prime is the unique prime over it.** If any two primes of `D`
lying over a prime `p'` of the base `A'` are equal, and `s` is a prime of `D` lying over a prime
`t` of an intermediate algebra `F` which itself lies over `p'`, then `s` is the only prime of `D`
over `t`.

This is the hypothesis `t.primesOver D = {s}` of
`Stacks.EtaleCohomology.exists_notMem_bijective_awayMap_of_isPurelyInseparable`, obtained from the
uniqueness assertion of [Stacks, Tag 00UL] on the factor `D`: every prime of `D` over `t` lies over
`p'` as well, so uniqueness over `p'` is a fortiori uniqueness over `t`. -/
theorem primesOver_eq_singleton_of_forall_eq {A' F D : Type*} [CommRing A'] [CommRing F]
    [CommRing D] [Algebra A' F] [Algebra A' D] [Algebra F D] [IsScalarTower A' F D]
    (p' : Ideal A') [p'.IsPrime]
    (huniq : ∀ q₁ q₂ : Ideal D, q₁.IsPrime → q₂.IsPrime → q₁.LiesOver p' → q₂.LiesOver p' →
      q₁ = q₂)
    (t : Ideal F) [t.IsPrime] [t.LiesOver p'] (s : Ideal D) [s.IsPrime] [s.LiesOver t] :
    t.primesOver D = {s} := by
  have hs : s.LiesOver p' := Ideal.LiesOver.trans s t p'
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨‹s.IsPrime›, ‹s.LiesOver t›⟩, fun q hq => ?_⟩
  have hq₁ : q.IsPrime := hq.1
  have hq₂ : q.LiesOver t := hq.2
  exact huniq q s hq₁ ‹s.IsPrime› (Ideal.LiesOver.trans q t p') hs

section AwayPrimes

/-- **A prime avoiding an element is disjoint from its powers.** -/
theorem disjoint_powers_of_notMem {R : Type*} [CommRing R] (x : R) (q : Ideal R) [q.IsPrime]
    (hx : x ∉ q) : Disjoint ((Submonoid.powers x : Submonoid R) : Set R) (q : Set R) := by
  rw [Set.disjoint_left]
  rintro y ⟨k, rfl⟩ hy
  exact hx (‹q.IsPrime›.mem_of_pow_mem k hy)

/-- **An element that has been inverted lies in no prime of the localization.** The image of `x` in
`R[1/x]` is a unit, so a prime containing it would be the whole ring. -/
theorem notMem_under_of_isLocalizationAway {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (x : R) [IsLocalization.Away x S] (u : Ideal S) [u.IsPrime] : x ∉ u.under R := by
  intro hmem
  rw [Ideal.under_def, Ideal.mem_comap] at hmem
  exact ‹u.IsPrime›.ne_top
    (Ideal.eq_top_of_isUnit_mem _ hmem (IsLocalization.Away.algebraMap_isUnit x))

/-- **The prime of `R[1/x]` cut out by a prime of `R` avoiding `x`.** -/
theorem isPrime_map_algebraMap_of_notMem {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (x : R) [IsLocalization.Away x S] (q : Ideal R) [q.IsPrime] (hx : x ∉ q) :
    (q.map (algebraMap R S)).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers x) S q ‹q.IsPrime›
    (disjoint_powers_of_notMem x q hx)

/-- **The prime of `R[1/x]` cut out by a prime of `R` avoiding `x` contracts back to it.** -/
theorem under_map_algebraMap_of_notMem {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (x : R) [IsLocalization.Away x S] (q : Ideal R) [q.IsPrime] (hx : x ∉ q) :
    (q.map (algebraMap R S)).under R = q :=
  IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers x) S ‹q.IsPrime›
    (disjoint_powers_of_notMem x q hx)

/-- **The prime of `R[1/x]` cut out by a prime of `R` lies over the same prime of the base.** -/
theorem liesOver_map_algebraMap_of_notMem {A' R S : Type*} [CommRing A'] [CommRing R] [CommRing S]
    [Algebra A' R] [Algebra A' S] [Algebra R S] [IsScalarTower A' R S]
    (x : R) [IsLocalization.Away x S] (p' : Ideal A') (q : Ideal R) [q.IsPrime] [q.LiesOver p']
    (hx : x ∉ q) : (q.map (algebraMap R S)).LiesOver p' := by
  refine ⟨?_⟩
  rw [Ideal.under_def, IsScalarTower.algebraMap_eq A' R S, ← Ideal.comap_comap,
    show Ideal.comap (algebraMap R S) (Ideal.map (algebraMap R S) q) = q from
      under_map_algebraMap_of_notMem x q hx]
  exact q.over_def p'

/-- **Uniqueness of the prime over `p'` passes to a localization.** If any two primes of `R` over
`p'` avoiding `x` are equal, then any two primes of `R[1/x]` over `p'` are equal: every prime of
the localization contracts to a prime of `R` over `p'` avoiding `x`, and is recovered from it.

This is the hypothesis `huniq` of
`Stacks.EtaleCohomology.exists_notMem_bijective_awayMap_algebraMap_of_etale_pair` at the factor
`E[1/c]` of the decomposition of the covering side, obtained from the uniqueness assertion of
[Stacks, Tag 00UL], which is stated on `E` itself. -/
theorem forall_eq_of_forall_eq_away {A' R S : Type*} [CommRing A'] [CommRing R] [CommRing S]
    [Algebra A' R] [Algebra A' S] [Algebra R S] [IsScalarTower A' R S]
    (x : R) [IsLocalization.Away x S] (p' : Ideal A')
    (huniq : ∀ q₁ q₂ : Ideal R, q₁.IsPrime → q₂.IsPrime → q₁.LiesOver p' → q₂.LiesOver p' →
      x ∉ q₁ → x ∉ q₂ → q₁ = q₂) :
    ∀ u₁ u₂ : Ideal S, u₁.IsPrime → u₂.IsPrime → u₁.LiesOver p' → u₂.LiesOver p' → u₁ = u₂ := by
  intro u₁ u₂ h₁ h₂ ho₁ ho₂
  have key : u₁.under R = u₂.under R :=
    huniq _ _ (h₁.comap _) (h₂.comap _)
      (liesOver_comap (IsScalarTower.toAlgHom A' R S) p' u₁)
      (liesOver_comap (IsScalarTower.toAlgHom A' R S) p' u₂)
      (notMem_under_of_isLocalizationAway x u₁) (notMem_under_of_isLocalizationAway x u₂)
  rw [← IsLocalization.map_under (Submonoid.powers x) S u₁,
    ← IsLocalization.map_under (Submonoid.powers x) S u₂, key]

/-- **The unique prime over `p'` of a localization is the one cut out by the unique prime below.**
If any two primes of `R` over `p'` avoiding `x` are equal, and `q` is such a prime, then the prime
of `R[1/x]` cut out by `q` is the only prime of `R[1/x]` over `p'`.

This is the hypothesis `huniqF` of
`Stacks.EtaleCohomology.exists_notMem_bijective_awayMap_algebraMap_of_etale_pair` at the factor
`P[1/b]` of the decomposition of the module-finite side. -/
theorem forall_eq_map_of_forall_eq_away {A' R S : Type*} [CommRing A'] [CommRing R] [CommRing S]
    [Algebra A' R] [Algebra A' S] [Algebra R S] [IsScalarTower A' R S]
    (x : R) [IsLocalization.Away x S] (p' : Ideal A')
    (huniq : ∀ q₁ q₂ : Ideal R, q₁.IsPrime → q₂.IsPrime → q₁.LiesOver p' → q₂.LiesOver p' →
      x ∉ q₁ → x ∉ q₂ → q₁ = q₂)
    (q : Ideal R) [q.IsPrime] [q.LiesOver p'] (hx : x ∉ q) :
    ∀ u : Ideal S, u.IsPrime → u.LiesOver p' → u = q.map (algebraMap R S) := by
  intro u hu huo
  have : (q.map (algebraMap R S)).IsPrime := isPrime_map_algebraMap_of_notMem x q hx
  have : (q.map (algebraMap R S)).LiesOver p' :=
    liesOver_map_algebraMap_of_notMem x p' q hx
  exact forall_eq_of_forall_eq_away x p' huniq u _ hu ‹_› huo ‹_›

end AwayPrimes

end AwayPair

section PushDown

/-- **Pushing an element of a module-finite algebra down to the base.** Let `F` be module-finite
over `A'`, let `p'` be a prime of `A'` and let `r : F` lie in no prime of `F` over `p'`. Then there
is an `a ∉ p'` whose image in `F` lies in the radical of the ideal generated by `r`; equivalently,
`r` becomes invertible as soon as `a` is inverted.

The spectrum map of a module-finite — hence integral — algebra is closed, so the image of the
closed set `V(r)` is closed in `Spec A'` and misses `p'` by hypothesis; a basic open neighbourhood
`D(a)` of `p'` inside the complement is exactly an `a ∉ p'` whose image lies in every prime
containing `r`.

This is what makes the finitely many inversions of elements of the *factors* `F` performed by
`Stacks.EtaleCohomology.exists_notMem_bijective_awayMap_of_isPurelyInseparable`, one for each index
of the decomposition, collapse into a single inversion in the base `A'`: the étale neighbourhood of
the base produced by the finite case of property (B), [Stacks, Tag 04DQ], must be one scheme, not
one per index. -/
theorem exists_notMem_mem_radical_span_of_forall_notMem {A' F : Type*} [CommRing A'] [CommRing F]
    [Algebra A' F] [Module.Finite A' F] (p' : Ideal A') [p'.IsPrime] (r : F)
    (h : ∀ u : Ideal F, u.IsPrime → u.LiesOver p' → r ∉ u) :
    ∃ a ∉ p', algebraMap A' F a ∈ (Ideal.span {r}).radical := by
  have hint : (algebraMap A' F).IsIntegral := Algebra.IsIntegral.isIntegral
  have hclosed : IsClosed (PrimeSpectrum.comap (algebraMap A' F) ''
      PrimeSpectrum.zeroLocus (Ideal.span {r})) :=
    PrimeSpectrum.isClosedMap_comap_of_isIntegral (algebraMap A' F) hint _
      (PrimeSpectrum.isClosed_zeroLocus _)
  have hmem : (⟨p', ‹p'.IsPrime›⟩ : PrimeSpectrum A') ∈
      (PrimeSpectrum.comap (algebraMap A' F) ''
        PrimeSpectrum.zeroLocus (Ideal.span {r}))ᶜ := by
    rintro ⟨u, hu, heq⟩
    have hr : r ∈ u.asIdeal := hu (Ideal.mem_span_singleton_self r)
    have : u.asIdeal.LiesOver p' := ⟨(congrArg PrimeSpectrum.asIdeal heq).symm⟩
    exact h u.asIdeal u.2 this hr
  obtain ⟨-, ⟨a, rfl⟩, ha, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hmem
      hclosed.isOpen_compl
  refine ⟨a, ha, ?_⟩
  rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]
  refine (PrimeSpectrum.mem_vanishingIdeal _ _).mpr fun u hu => ?_
  by_contra hmem'
  exact hsub (by simpa [PrimeSpectrum.mem_basicOpen] using hmem') ⟨u, hu, rfl⟩

/-- **An element of a module-finite algebra avoiding the unique prime over `p'` is inverted by one
element of the base.** This is `exists_notMem_mem_radical_span_of_forall_notMem` in the form the
étale local structure theorem [Stacks, Tag 00UL] delivers: `t` is the only prime of `F` lying over
`p'`, so an `r ∉ t` lies in no prime over `p'` at all. -/
theorem exists_notMem_mem_radical_span_of_unique_prime {A' F : Type*} [CommRing A'] [CommRing F]
    [Algebra A' F] [Module.Finite A' F] (p' : Ideal A') [p'.IsPrime]
    (t : Ideal F) [t.IsPrime] [t.LiesOver p']
    (huniq : ∀ u : Ideal F, u.IsPrime → u.LiesOver p' → u = t)
    {r : F} (hr : r ∉ t) :
    ∃ a ∉ p', algebraMap A' F a ∈ (Ideal.span {r}).radical :=
  exists_notMem_mem_radical_span_of_forall_notMem p' r fun u hu huo => by
    rwa [huniq u hu huo]

/-- If `v` lies in the radical of `(z)` and `v` becomes a unit in `T`, so does `z`. -/
private theorem isUnit_of_mem_radical_span_aux {F T : Type*} [CommRing F] [CommRing T]
    [Algebra F T] {z v : F} (hv : v ∈ (Ideal.span {z}).radical)
    (hu : IsUnit (algebraMap F T v)) :
    IsUnit (algebraMap F T z) := by
  obtain ⟨m, hm⟩ := hv
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hm
  have hpow : IsUnit (algebraMap F T (v ^ m)) := by simpa only [map_pow] using hu.pow m
  rw [← hw, map_mul] at hpow
  exact isUnit_of_mul_isUnit_right hpow

/-- An element of the radical of the ideal generated by `r` becomes, once inverted, a witness that
`r` itself is invertible: a power of it is a multiple of `r`. -/
theorem isUnit_of_mem_radical_span {F T : Type*} [CommRing F] [CommRing T] [Algebra F T] {r z : F}
    (hz : z ∈ (Ideal.span {r}).radical) [IsLocalization.Away z T] :
    IsUnit (algebraMap F T r) :=
  isUnit_of_mem_radical_span_aux hz (IsLocalization.Away.algebraMap_isUnit z)

/-- **A member of the radical of `(z)` carries invertibility to `z`.** This is
`Stacks.EtaleCohomology.isUnit_of_mem_radical_span` with the localisation replaced by the single
consequence of it that is used: if `v` lies in the radical of the ideal generated by `z` and the
image of `v` in an `F`-algebra `T` is a unit, then so is the image of `z`.

Stated this way it applies to *any* `T` in which `v` becomes invertible, not only to `F[1/v]`
itself. That is what makes the finitely many inversions of the finite case of property (B),
[Stacks, Tag 04DQ], collapse: a single element of the base is inverted, and every element pushed
down to a divisor of it becomes a unit at once. -/
theorem isUnit_of_mem_radical_span_of_isUnit {F T : Type*} [CommRing F] [CommRing T]
    [Algebra F T] {z v : F} (hv : v ∈ (Ideal.span {z}).radical)
    (hu : IsUnit (algebraMap F T v)) :
    IsUnit (algebraMap F T z) :=
  isUnit_of_mem_radical_span_aux hv hu

/-- **Pushing an element of a factor down to the base, in localisation form.** If `r` avoids the
unique prime `t` of a module-finite `A'`-algebra `F` over `p'`, then there is an `a ∉ p'` such that
`r` is invertible in `F[1/a]` — so that `F[1/a]` is at the same time the localisation of `F` away
from `a * r`.

This is the form in which the element produced by
`Stacks.EtaleCohomology.exists_notMem_bijective_awayMap_of_isPurelyInseparable` is absorbed into
the base: its conclusion holds for every multiple of the element it produces, and `a * r` is one.
-/
theorem exists_notMem_isUnit_of_unique_prime (A' F : Type*) [CommRing A'] [CommRing F]
    [Algebra A' F] [Module.Finite A' F] (p' : Ideal A') [p'.IsPrime]
    (t : Ideal F) [t.IsPrime] [t.LiesOver p']
    (huniq : ∀ u : Ideal F, u.IsPrime → u.LiesOver p' → u = t)
    {r : F} (hr : r ∉ t) :
    ∃ a ∉ p', IsUnit (algebraMap F (Localization.Away (algebraMap A' F a)) r) := by
  obtain ⟨a, hap, ha⟩ := exists_notMem_mem_radical_span_of_unique_prime p' t huniq hr
  exact ⟨a, hap, isUnit_of_mem_radical_span ha⟩

end PushDown

section LocalRingHom

open Finset in
/-- **Surjectivity of `R_p → S_q` spreads to a basic open neighbourhood of `p`.** Let `S` be
module-finite over `R` and let `q` be the *only* prime of `S` lying over a prime `p` of `R`. If the
induced map `R_p → S_q` of local rings is surjective, then there is a single `r ∉ p` such that
`R[1/r] → S[1/r]` is already surjective.

This is the surjectivity half of Mathlib's
`Localization.exists_awayMap_bijective_of_localRingHom_bijective`, separated out and with that
lemma's hypothesis that `RingHom.ker (algebraMap R S)` be finitely generated *dropped*: that
hypothesis is needed only for the injectivity half. The finite case of property (B),
[Stacks, Tag 04DQ], has no way to produce it — the factor `D = E[1/c]` of an étale covering can be
the zero ring away from the chosen prime, so the kernel is not known to be finitely generated —
while injectivity is available there from faithful flatness after one shrinking of the base, by
`Stacks.EtaleCohomology.injective_awayMap_of_surjective_comap`.

The element `r` is the product, over a finite generating set `s` of `S` as an `R`-algebra, of
denominators `b x ∉ p` chosen so that `x · b x` lies in the image of `R`; surjectivity of
`R_p → S_q` together with the uniqueness of `q` over `p` provides them. The set of elements of `S`
that become images of `R` after inverting `r` is then an `R`-subalgebra containing `s`, hence all
of `S`. -/
theorem exists_notMem_surjective_awayMap_of_localRingHom_surjective
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {p : Ideal R} [p.IsPrime]
    {q : Ideal S} [q.IsPrime] (hq : p.primesOver S = {q}) [Module.Finite R S] [q.LiesOver p]
    (H : Function.Surjective (Localization.localRingHom p q (algebraMap R S) (q.over_def p))) :
    ∃ r ∉ p, Function.Surjective (Localization.awayMap (algebraMap R S) r) := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := S)
  have key : ∀ x : S, ∃ a, ∃ b ∉ p, algebraMap R S a = x * algebraMap R S b := by
    intro x
    have := (IsLocalization.mk'_surjective p.primeCompl).exists.mp (H (algebraMap _ _ x))
    simp only [Localization.localRingHom_mk', Prod.exists, Subtype.exists,
      Ideal.mem_primeCompl_iff, IsLocalization.mk'_eq_iff_eq_mul, exists_prop, ← map_mul,
      IsLocalization.eq_iff_exists q.primeCompl] at this
    obtain ⟨a, b, hbp, c, hcq, hc⟩ := this
    obtain ⟨d, hd, e, he⟩ :=
      Ideal.exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton hq _ hcq
    exact ⟨d * a, d * b, ‹p.IsPrime›.mul_notMem hd hbp, by grind⟩
  choose a b hbp e using key
  refine ⟨∏ i ∈ s, b i, prod_mem (S := p.primeCompl) fun _ _ ↦ hbp _, ?_⟩
  rw [Localization.awayMap_surjective_iff]
  intro x
  have hx : x ∈ Algebra.adjoin R (↑s : Set S) := hs ▸ Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem z hz =>
      refine ⟨(∏ i ∈ s.erase z, b i) * a z, 1, ?_⟩
      rw [pow_one, map_mul, e z, ← Finset.prod_erase_mul s b (Finset.mem_coe.mp hz), map_mul]
      ring
  | algebraMap z => exact ⟨z, 0, by simp⟩
  | add u v _ _ ihu ihv =>
      obtain ⟨y₁, m₁, h₁⟩ := ihu
      obtain ⟨y₂, m₂, h₂⟩ := ihv
      refine ⟨(∏ i ∈ s, b i) ^ m₂ * y₁ + (∏ i ∈ s, b i) ^ m₁ * y₂, m₁ + m₂, ?_⟩
      rw [map_add, map_mul, map_mul, map_pow, map_pow, h₁, h₂, pow_add]
      ring
  | mul u v _ _ ihu ihv =>
      obtain ⟨y₁, m₁, h₁⟩ := ihu
      obtain ⟨y₂, m₂, h₂⟩ := ihv
      refine ⟨y₁ * y₂, m₁ + m₂, ?_⟩
      rw [map_mul, h₁, h₂, pow_add]
      ring

end LocalRingHom

section AwayFlat

/-- **The away map is the structure map of the localised pair.** For an `R`-algebra `S` and
`a : R`, the algebra structure on `S[1/a]` over `R[1/a]` installed by
`Stacks.EtaleCohomology.awayAlgebra` has `Localization.awayMap (algebraMap R S) a` as its structure
map.

Both maps make the square `R → S`, `R[1/a] → S[1/a]` commute, and a map out of a localisation is
determined by its restriction. This is what lets facts about `algebraMap R[1/a] S[1/a]` — flatness,
faithful flatness, injectivity — be read as facts about the away map. -/
theorem algebraMap_away_eq_awayMap {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (a : R) :
    algebraMap (Localization.Away a) (Localization.Away (algebraMap R S a)) =
      Localization.awayMap (algebraMap R S) a := by
  refine IsLocalization.ringHom_ext (Submonoid.powers a) (RingHom.ext fun x => ?_)
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [← IsScalarTower.algebraMap_apply R (Localization.Away a)
      (Localization.Away (algebraMap R S a)),
    IsScalarTower.algebraMap_apply R S (Localization.Away (algebraMap R S a))]
  exact (IsLocalization.map_eq _ _).symm

/-- **Flatness survives inverting one element of the base.** If `S` is flat over `R` then `S[1/a]`
is flat over `R[1/a]`, for `a : R`.

`S[1/a]` is flat over `R` because it is a localisation of the flat `R`-algebra `S`, and flatness
over a localisation of `R` is equivalent to flatness over `R` by
`Module.flat_iff_of_isLocalization`. -/
@[ega "0 6.3.1" "special case", sga "1 IV 1.2" "(i), special case"]
theorem flat_away_of_flat {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (a : R) :
    Module.Flat (Localization.Away a) (Localization.Away (algebraMap R S a)) := by
  rw [Module.flat_iff_of_isLocalization (Localization.Away a) (Submonoid.powers a)
    (Localization.Away (algebraMap R S a))]
  infer_instance

/-- **A flat algebra whose spectrum surjects becomes injective.** If `S` is flat over `R` and
`Spec S[1/a] → Spec R[1/a]` is surjective, then `R[1/a] → S[1/a]` is injective.

A flat algebra surjective on spectra is faithfully flat, and a faithfully flat algebra has
injective structure map. This is the step that replaces the hypothesis `FaithfulSMul R S` of
Mathlib's `Localization.exists_awayMap_bijective_of_residueField_surjective`, which is *not*
available in the finite case of property (B), [Stacks, Tag 04DQ]: the factor `D = E[1/c]` of the
étale covering may well be zero away from the chosen prime, so `F → D` need not be injective before
the base is shrunk. -/
@[sga "1 IV 2.6" "(ii)"]
theorem injective_awayMap_of_surjective_comap {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] (a : R)
    (h : Function.Surjective
      (PrimeSpectrum.comap (Localization.awayMap (algebraMap R S) a))) :
    Function.Injective (Localization.awayMap (algebraMap R S) a) := by
  have halg := algebraMap_away_eq_awayMap (R := R) (S := S) a
  have := flat_away_of_flat (R := R) (S := S) a
  have hff : Module.FaithfullyFlat (Localization.Away a)
      (Localization.Away (algebraMap R S a)) :=
    Module.FaithfullyFlat.of_comap_surjective (by rwa [halg])
  have hinj := FaithfulSMul.algebraMap_injective (Localization.Away a)
    (Localization.Away (algebraMap R S a))
  rwa [halg] at hinj

end AwayFlat

section PerIndex

/-- **The spectrum of an étale algebra has open image.** An étale algebra is flat and of finite
presentation, so its spectrum map is open. This is the hypothesis of
`Stacks.EtaleCohomology.exists_notMem_basicOpen_subset_range_comap`, which shrinks the base until
the map becomes surjective. -/
theorem isOpen_range_comap_of_etale (F D : Type*) [CommRing F] [CommRing D] [Algebra F D]
    [Algebra.Etale F D] :
    IsOpen (Set.range (PrimeSpectrum.comap (algebraMap F D))) :=
  (PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
    (R := F) (S := D)).isOpen_range

/-- **The per-index trivialisation of the finite case of property (B), given surjectivity.** In the
situation produced by the étale local structure theorem [Stacks, Tag 00UL] — a base `A'` with a
prime `p'`, a `P`-algebra `E` which is étale, the factor `F = P[1/x]` of a decomposition of `P`,
the factor `D = E[1/y]` of a decomposition of `E`, which is module-finite over `F`, a prime `t` of
`F` over `p'` and a prime `s` of `D` over `t`, with at most one prime of `D` over `p'` and
`κ(s)/κ(p')` purely inseparable — the map `F → D` becomes an isomorphism after inverting a single
element of `F` outside `t`, provided `Spec D → Spec F` is surjective.

All the hypotheses of
`Stacks.EtaleCohomology.exists_notMem_bijective_awayMap_of_isPurelyInseparable` other than
surjectivity are discharged here: `D` is étale over `F` by
`Stacks.EtaleCohomology.etale_of_isLocalizationAway_pair`, hence flat and unramified at `s`; and
`s` is the only prime over `t` because there is at most one prime over `p'`. Module-finiteness over
`F` is asked for rather than over `A'` — which is the form [Stacks, Tag 00UL] supplies it in, see
`Stacks.EtaleCohomology.moduleFinite_of_moduleFinite_base` — because it is the one of the two that
survives a localisation of the base.

Surjectivity is *not* automatic and is the remaining hypothesis: it is arranged by shrinking the
base, since by `Stacks.EtaleCohomology.isOpen_range_comap_of_etale` the image is open and contains
`t`. -/
theorem exists_notMem_bijective_awayMap_of_etale_pair
    {A' P E F D : Type*} [CommRing A'] [CommRing P] [CommRing E] [CommRing F] [CommRing D]
    [Algebra A' P] [Algebra A' F] [Algebra A' D]
    [Algebra P E] [Algebra P F] [Algebra P D] [Algebra E D] [Algebra F D]
    [IsScalarTower A' P F] [IsScalarTower A' P D]
    [IsScalarTower P E D] [IsScalarTower P F D] [IsScalarTower A' F D]
    [Algebra.Etale P E] [Module.Finite F D]
    (p' : Ideal A') [p'.IsPrime]
    (x : P) [IsLocalization.Away x F] (y : E) [IsLocalization.Away y D]
    (t : Ideal F) [t.IsPrime] [t.LiesOver p'] (s : Ideal D) [s.IsPrime] [s.LiesOver t]
    [s.LiesOver p']
    [Algebra (Localization.AtPrime p') (Localization.AtPrime t)]
    [Localization.AtPrime.IsLiesOverAlgebra p' t]
    [Algebra (Localization.AtPrime t) (Localization.AtPrime s)]
    [Localization.AtPrime.IsLiesOverAlgebra t s]
    [Algebra (Localization.AtPrime p') (Localization.AtPrime s)]
    [Localization.AtPrime.IsLiesOverAlgebra p' s]
    (huniq : ∀ q₁ q₂ : Ideal D, q₁.IsPrime → q₂.IsPrime → q₁.LiesOver p' → q₂.LiesOver p' →
      q₁ = q₂)
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap F D)))
    (hres : IsPurelyInseparable p'.ResidueField s.ResidueField) :
    ∃ r ∉ t, ∀ r', r ∣ r' → Function.Bijective (Localization.awayMap (algebraMap F D) r') := by
  have hEt : Algebra.Etale F D := etale_of_isLocalizationAway_pair x y
  have : Algebra.IsUnramifiedAt F s := isUnramifiedAt_of_formallyUnramified F D s
  exact exists_notMem_bijective_awayMap_of_isPurelyInseparable (A := A') p' t s
    (primesOver_eq_singleton_of_forall_eq p' huniq t s) hsurj hres

/-- **The per-index trivialisation, with the residue-field tower supplied internally.** This is
`Stacks.EtaleCohomology.exists_notMem_bijective_awayMap_of_etale_pair` with the three algebra
structures on the local rings of `p'`, `t` and `s` installed by
`Localization.AtPrime.algebraOfLiesOver` rather than taken as instance arguments, so that the
hypothesis on the residue field extension is in exactly the shape the étale local structure theorem
delivers it: `Stacks.EtaleCohomology.exists_etale_completeOrthogonalIdempotents_tensorBaseChange`
states pure inseparability under the same `letI`.

The towers `κ(p') → κ(t) → κ(s)` and `κ(p') → κ(s)` are then recognised by instance search, which
is the point of Mathlib's `Localization.AtPrime.IsLiesOverAlgebra` predicate. -/
theorem exists_notMem_bijective_awayMap_of_etale_pair_of_liesOver
    {A' P E F D : Type*} [CommRing A'] [CommRing P] [CommRing E] [CommRing F] [CommRing D]
    [Algebra A' P] [Algebra A' F] [Algebra A' D]
    [Algebra P E] [Algebra P F] [Algebra P D] [Algebra E D] [Algebra F D]
    [IsScalarTower A' P F] [IsScalarTower A' P D]
    [IsScalarTower P E D] [IsScalarTower P F D] [IsScalarTower A' F D]
    [Algebra.Etale P E] [Module.Finite F D]
    (p' : Ideal A') [p'.IsPrime]
    (x : P) [IsLocalization.Away x F] (y : E) [IsLocalization.Away y D]
    (t : Ideal F) [t.IsPrime] [t.LiesOver p'] (s : Ideal D) [s.IsPrime] [s.LiesOver t]
    [s.LiesOver p']
    (huniq : ∀ q₁ q₂ : Ideal D, q₁.IsPrime → q₂.IsPrime → q₁.LiesOver p' → q₂.LiesOver p' →
      q₁ = q₂)
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap F D)))
    (hres : letI := Localization.AtPrime.algebraOfLiesOver p' s
      IsPurelyInseparable p'.ResidueField s.ResidueField) :
    ∃ r ∉ t, ∀ r', r ∣ r' → Function.Bijective (Localization.awayMap (algebraMap F D) r') := by
  let := Localization.AtPrime.algebraOfLiesOver p' t
  let := Localization.AtPrime.algebraOfLiesOver t s
  let := Localization.AtPrime.algebraOfLiesOver p' s
  exact exists_notMem_bijective_awayMap_of_etale_pair p' x y t s huniq hsurj hres

/-- **Inverting one element makes a covering of a basic open surjective.** Let `D` be an
`F`-algebra whose image on spectra contains the basic open set of `z`, and let `w : F` be an
element whose inversion already makes `z` invertible. Then `Spec D[1/w] → Spec F[1/w]` is
surjective.

Every prime of `F[1/w]` contracts to a prime of `F` avoiding `w` and, `z` being invertible there,
avoiding `z`; such a prime is the contraction of a prime of `D`, which avoids the image of `w`
because its contraction does, and hence comes from `Spec D[1/w]`. The two contractions to `Spec F`
agree, and contraction along a localisation is injective. -/
theorem surjective_comap_awayMap_of_basicOpen_subset {F D : Type*} [CommRing F] [CommRing D]
    [Algebra F D] (z w : F)
    (hsub : (PrimeSpectrum.basicOpen z : Set (PrimeSpectrum F)) ⊆
      Set.range (PrimeSpectrum.comap (algebraMap F D)))
    (hunit : IsUnit (algebraMap F (Localization.Away w) z)) :
    Function.Surjective (PrimeSpectrum.comap (Localization.awayMap (algebraMap F D) w)) := by
  intro q₁
  have hwu : w ∉ (PrimeSpectrum.comap (algebraMap F (Localization.Away w)) q₁).asIdeal := by
    have hr : PrimeSpectrum.comap (algebraMap F (Localization.Away w)) q₁ ∈
        Set.range (PrimeSpectrum.comap (algebraMap F (Localization.Away w))) := ⟨q₁, rfl⟩
    rwa [PrimeSpectrum.localization_away_comap_range (Localization.Away w) w] at hr
  have hzu : z ∉ (PrimeSpectrum.comap (algebraMap F (Localization.Away w)) q₁).asIdeal :=
    fun hmem => q₁.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hunit)
  obtain ⟨q, hq⟩ := hsub hzu
  have hwq : algebraMap F D w ∉ q.asIdeal := by
    intro hmem
    apply hwu
    rwa [← hq]
  have hqrange : q ∈ Set.range (PrimeSpectrum.comap (algebraMap D (Localization.Away
      (algebraMap F D w)))) := by
    rwa [PrimeSpectrum.localization_away_comap_range (Localization.Away (algebraMap F D w))
      (algebraMap F D w)]
  obtain ⟨q₂, hq₂⟩ := hqrange
  refine ⟨q₂, PrimeSpectrum.localization_comap_injective (Localization.Away w)
    (Submonoid.powers w) ?_⟩
  have hsquare : (Localization.awayMap (algebraMap F D) w).comp
      (algebraMap F (Localization.Away w)) =
      (algebraMap D (Localization.Away (algebraMap F D w))).comp (algebraMap F D) :=
    IsLocalization.map_comp _
  rw [← PrimeSpectrum.comap_comp_apply, hsquare, PrimeSpectrum.comap_comp_apply, hq₂, hq]

/-- **Surjectivity of the covering after one shrinking of the base.** Let `F` be module-finite over
`A'` with a unique prime `t` over `p'`, let `D` be an `F`-algebra with a prime over `t` and with
open image on spectra. Then there is a single `a ∉ p'` such that `Spec D[1/a] → Spec F[1/a]` is
surjective.

The image contains a basic open neighbourhood `D(z)` of `t` by
`Stacks.EtaleCohomology.exists_notMem_basicOpen_subset_range_comap`, and `z` is pushed down to the
base by `Stacks.EtaleCohomology.exists_notMem_mem_radical_span_of_unique_prime`: in `F[1/a]` the
element `z` is already invertible, so every prime of `F[1/a]` lies in `D(z)` and is therefore hit
by a prime of `D`, which avoids `a` because its contraction does.

This supplies the one hypothesis of
`Stacks.EtaleCohomology.exists_notMem_bijective_awayMap_of_etale_pair` that is not automatic. -/
theorem exists_notMem_surjective_comap_awayMap
    {A' F D : Type*} [CommRing A'] [CommRing F] [CommRing D] [Algebra A' F] [Algebra A' D]
    [Algebra F D] [IsScalarTower A' F D] [Module.Finite A' F]
    (p' : Ideal A') [p'.IsPrime] (t : Ideal F) [t.IsPrime] [t.LiesOver p']
    (huniq : ∀ u : Ideal F, u.IsPrime → u.LiesOver p' → u = t)
    (s : Ideal D) [s.IsPrime] [s.LiesOver t]
    (hopen : IsOpen (Set.range (PrimeSpectrum.comap (algebraMap F D)))) :
    ∃ a ∉ p', Function.Surjective (PrimeSpectrum.comap
      (Localization.awayMap (algebraMap F D) (algebraMap A' F a))) := by
  obtain ⟨z, hzt, hsub⟩ :=
    exists_notMem_basicOpen_subset_range_comap (R := F) (S := D) (t := t) (s := s) hopen
  obtain ⟨a, hap, ha⟩ := exists_notMem_mem_radical_span_of_unique_prime p' t huniq hzt
  exact ⟨a, hap,
    surjective_comap_awayMap_of_basicOpen_subset z (algebraMap A' F a) hsub
      (isUnit_of_mem_radical_span ha)⟩

/-- **Bijectivity of the away map at one element of the base.** Let `S` be flat over `R`, let the
image of `Spec S → Spec R` contain the basic open set of `z`, let `R[1/r] → S[1/r]` be surjective,
and let `W` be a common multiple of `r` and of an element `v` in the radical of the ideal generated
by `z`. Then `R[1/W] → S[1/W]` is bijective.

Surjectivity is `Localization.awayMap_surjective_of_dvd` applied to `r ∣ W`. Injectivity comes from
`Stacks.EtaleCohomology.injective_awayMap_of_surjective_comap`: inverting `W` inverts `v`, hence
`z`, so every prime of `R[1/W]` lies in the basic open set of `z` and is therefore hit, by
`Stacks.EtaleCohomology.surjective_comap_awayMap_of_basicOpen_subset`.

This is the shape in which the finite case of property (B), [Stacks, Tag 04DQ], needs the
trivialisation: the element inverted must come from the *base*, and `W` is the product of the two
elements of the base that the two halves — surjectivity of the covering and surjectivity of the
algebra — are pushed down to. -/
theorem bijective_awayMap_of_dvd_of_basicOpen_subset {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] {r z v W : R}
    (hrW : r ∣ W) (hvW : v ∣ W) (hv : v ∈ (Ideal.span {z}).radical)
    (hsub : (PrimeSpectrum.basicOpen z : Set (PrimeSpectrum R)) ⊆
      Set.range (PrimeSpectrum.comap (algebraMap R S)))
    (hrsurj : Function.Surjective (Localization.awayMap (algebraMap R S) r)) :
    Function.Bijective (Localization.awayMap (algebraMap R S) W) := by
  have hunit : IsUnit (algebraMap R (Localization.Away W) v) := by
    obtain ⟨c, rfl⟩ := hvW
    have h2 := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (v * c)) (v * c)
    rw [map_mul] at h2
    exact isUnit_of_mul_isUnit_left h2
  exact ⟨injective_awayMap_of_surjective_comap W
      (surjective_comap_awayMap_of_basicOpen_subset z W hsub
        (isUnit_of_mem_radical_span_of_isUnit hv hunit)),
    Localization.awayMap_surjective_of_dvd _ hrW hrsurj⟩

/-- **The per-index trivialisation of the finite case of property (B), with the element inverted
taken from the base and no surjectivity assumed.** In the situation produced by the étale local
structure theorem [Stacks, Tag 00UL] — a base `A'` with a prime `p'`, a `P`-algebra `E` which is
étale, the factor `F = P[1/x]` of a decomposition of `P`, module-finite over `A'` and with `t` as
its *only* prime over `p'`, the factor `D = E[1/y]` of a decomposition of `E`, module-finite over
`F`, a prime `s` of `D` over `t`, with at most one prime of `D` over `p'` and `κ(s)/κ(p')` purely
inseparable — there is a single `a ∉ p'` such that `F[1/a] → D[1/a]` is an isomorphism, the element
`a` being inverted *through the base* `A'`.

This is the form the finite case of property (B), [Stacks, Tag 04DQ], needs: the étale
neighbourhood of the base it produces must be one scheme, so the finitely many inversions performed
over the finitely many indices of the decomposition must all be inversions of elements of `A'`.
Compared with
`Stacks.EtaleCohomology.exists_notMem_bijective_awayMap_of_etale_pair_of_liesOver` the hypothesis
that `Spec D → Spec F` be surjective is *gone*, and nothing replaces it: `D = E[1/y]` really can be
the zero ring away from `t`. The two halves are obtained separately and then multiplied together in
the base:

* surjectivity of `F[1/·] → D[1/·]` from
  `Stacks.EtaleCohomology.exists_notMem_surjective_awayMap_of_localRingHom_surjective`, whose
  hypothesis — surjectivity of `F_t → D_s` — is
  `Localization.localRingHom_surjective_of_primesOver_eq_singleton` and needs no surjectivity on
  spectra;
* injectivity from `Stacks.EtaleCohomology.injective_awayMap_of_surjective_comap`, whose hypothesis
  is arranged by `Stacks.EtaleCohomology.exists_notMem_basicOpen_subset_range_comap`, the étale
  image being open.

Both elements are pushed down to `A'` by
`Stacks.EtaleCohomology.exists_notMem_mem_radical_span_of_unique_prime`, which is what the extra
hypotheses `[Module.Finite A' F]` and `huniqF` are for, and
`Stacks.EtaleCohomology.bijective_awayMap_of_dvd_of_basicOpen_subset` combines them.

The conclusion holds not only for the element produced but for every multiple of it, which is what
lets the finitely many indices of the decomposition be handled by one shrinking of the base through
`Stacks.EtaleCohomology.exists_notMem_forall_dvd_of_forall_exists`; the two elements enter only
through divisibilities, so no further argument is needed for that. -/
theorem exists_notMem_forall_dvd_bijective_awayMap_algebraMap_of_etale_pair
    {A' P E F D : Type*} [CommRing A'] [CommRing P] [CommRing E] [CommRing F] [CommRing D]
    [Algebra A' P] [Algebra A' F] [Algebra A' D]
    [Algebra P E] [Algebra P F] [Algebra P D] [Algebra E D] [Algebra F D]
    [IsScalarTower A' P F] [IsScalarTower A' P D]
    [IsScalarTower P E D] [IsScalarTower P F D] [IsScalarTower A' F D]
    [Algebra.Etale P E] [Module.Finite F D] [Module.Finite A' F]
    (p' : Ideal A') [p'.IsPrime]
    (x : P) [IsLocalization.Away x F] (y : E) [IsLocalization.Away y D]
    (t : Ideal F) [t.IsPrime] [t.LiesOver p'] (s : Ideal D) [s.IsPrime] [s.LiesOver t]
    [s.LiesOver p']
    [Algebra (Localization.AtPrime p') (Localization.AtPrime t)]
    [Localization.AtPrime.IsLiesOverAlgebra p' t]
    [Algebra (Localization.AtPrime t) (Localization.AtPrime s)]
    [Localization.AtPrime.IsLiesOverAlgebra t s]
    [Algebra (Localization.AtPrime p') (Localization.AtPrime s)]
    [Localization.AtPrime.IsLiesOverAlgebra p' s]
    (huniqF : ∀ u : Ideal F, u.IsPrime → u.LiesOver p' → u = t)
    (huniq : ∀ q₁ q₂ : Ideal D, q₁.IsPrime → q₂.IsPrime → q₁.LiesOver p' → q₂.LiesOver p' →
      q₁ = q₂)
    (hres : IsPurelyInseparable p'.ResidueField s.ResidueField) :
    ∃ a ∉ p', ∀ a' : A', a ∣ a' → Function.Bijective
      (Localization.awayMap (algebraMap F D) (algebraMap A' F a')) := by
  have hEt : Algebra.Etale F D := etale_of_isLocalizationAway_pair x y
  have hunr : Algebra.IsUnramifiedAt F s := isUnramifiedAt_of_formallyUnramified F D s
  have hq : t.primesOver D = {s} := primesOver_eq_singleton_of_forall_eq p' huniq t s
  obtain ⟨r, hrt, hrsurj⟩ := exists_notMem_surjective_awayMap_of_localRingHom_surjective hq
    (Localization.localRingHom_surjective_of_primesOver_eq_singleton hq
      (bijective_algebraMap_residueField_of_isPurelyInseparable p' t s hres).2)
  obtain ⟨a₁, ha₁, hrad₁⟩ := exists_notMem_mem_radical_span_of_unique_prime p' t huniqF hrt
  obtain ⟨z, hzt, hsub⟩ :=
    exists_notMem_basicOpen_subset_range_comap (R := F) (S := D) (t := t) (s := s)
      (isOpen_range_comap_of_etale F D)
  obtain ⟨a₂, ha₂, hrad₂⟩ := exists_notMem_mem_radical_span_of_unique_prime p' t huniqF hzt
  obtain ⟨m, hm⟩ := hrad₁
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hm
  refine ⟨a₁ ^ m * a₂, fun hmem => ?_, ?_⟩
  · rcases ‹p'.IsPrime›.mem_or_mem hmem with h | h
    · exact ha₁ (‹p'.IsPrime›.mem_of_pow_mem m h)
    · exact ha₂ h
  · rintro a' ⟨k, rfl⟩
    refine bijective_awayMap_of_dvd_of_basicOpen_subset (r := r) (z := z)
      (v := algebraMap A' F a₂) ⟨u * (algebraMap A' F a₂ * algebraMap A' F k), ?_⟩
      ⟨algebraMap A' F a₁ ^ m * algebraMap A' F k, ?_⟩ hrad₂ hsub hrsurj
    · simp only [map_mul, map_pow]
      rw [← hu]
      ring
    · simp only [map_mul, map_pow]
      ring

/-- **The per-index trivialisation of the finite case of property (B), at the element produced.**
This is `exists_notMem_forall_dvd_bijective_awayMap_algebraMap_of_etale_pair` with the conclusion
read at the element it produces rather than at all of its multiples. -/
theorem exists_notMem_bijective_awayMap_algebraMap_of_etale_pair
    {A' P E F D : Type*} [CommRing A'] [CommRing P] [CommRing E] [CommRing F] [CommRing D]
    [Algebra A' P] [Algebra A' F] [Algebra A' D]
    [Algebra P E] [Algebra P F] [Algebra P D] [Algebra E D] [Algebra F D]
    [IsScalarTower A' P F] [IsScalarTower A' P D]
    [IsScalarTower P E D] [IsScalarTower P F D] [IsScalarTower A' F D]
    [Algebra.Etale P E] [Module.Finite F D] [Module.Finite A' F]
    (p' : Ideal A') [p'.IsPrime]
    (x : P) [IsLocalization.Away x F] (y : E) [IsLocalization.Away y D]
    (t : Ideal F) [t.IsPrime] [t.LiesOver p'] (s : Ideal D) [s.IsPrime] [s.LiesOver t]
    [s.LiesOver p']
    [Algebra (Localization.AtPrime p') (Localization.AtPrime t)]
    [Localization.AtPrime.IsLiesOverAlgebra p' t]
    [Algebra (Localization.AtPrime t) (Localization.AtPrime s)]
    [Localization.AtPrime.IsLiesOverAlgebra t s]
    [Algebra (Localization.AtPrime p') (Localization.AtPrime s)]
    [Localization.AtPrime.IsLiesOverAlgebra p' s]
    (huniqF : ∀ u : Ideal F, u.IsPrime → u.LiesOver p' → u = t)
    (huniq : ∀ q₁ q₂ : Ideal D, q₁.IsPrime → q₂.IsPrime → q₁.LiesOver p' → q₂.LiesOver p' →
      q₁ = q₂)
    (hres : IsPurelyInseparable p'.ResidueField s.ResidueField) :
    ∃ a ∉ p', Function.Bijective
      (Localization.awayMap (algebraMap F D) (algebraMap A' F a)) :=
  let ⟨a, hap, ha⟩ := exists_notMem_forall_dvd_bijective_awayMap_algebraMap_of_etale_pair
    p' x y t s huniqF huniq hres
  ⟨a, hap, ha a dvd_rfl⟩

end PerIndex

end Stacks.EtaleCohomology

end

