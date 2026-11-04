module

import Mathlib.Tactic.ReduceModChar
import Mathlib.RingTheory.Localization.Pi
import Mathlib.Algebra.Order.Ring.Star

public import StacksFrontier.RingTheory.MinimalPrimes.Reduced
public import StacksFrontier.RingTheory.Localization.FractionRing
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.IntegrallyClosed.Stability
public import StacksFrontier.RingTheory.IntegralClosure.Basic
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u

/-!
# Normality of a reduced ring with finitely many minimal primes

Let `R` be a reduced ring with finitely many minimal primes `𝔭₁, …, 𝔭ₙ`. Then `R` is a normal
ring (tag `00GV`: all its localizations at primes are normal domains) if and only if it is
integrally closed in its total ring of fractions `Q(R)`, if and only if it is a finite product
of normal domains, and in that case the product is the canonical one: `R → ∏ᵢ R/𝔭ᵢ` is an
isomorphism.

The two implications that hold for every ring are `034M` (a normal ring is integrally closed in
`Q(R)`) and `0CYA` (a finite product of normal rings is normal). The content is the passage from
"integrally closed in `Q(R)`" to the product decomposition. By `02LX` the total ring of fractions
is `Q(R) = R_{𝔭₁} × ⋯ × R_{𝔭ₙ}`, so `Q(R)` carries the orthogonal idempotents `eᵢ`. Each `eᵢ` is
a root of `X² - X`, hence integral over `R`, hence of the form `algebraMap R Q(R) r`; comparing
components, `r ∈ 𝔭ⱼ` for `j ≠ i` while `1 - r ∈ 𝔭ᵢ`. So distinct minimal primes are comaximal,
and the Chinese remainder theorem turns `R → ∏ᵢ R/𝔭ᵢ` into an isomorphism — injective because
`R` is reduced. Finally each factor `R/𝔭ᵢ` is integrally closed in its fraction field, by `0CY9`
applied to the product decomposition of `R` and of its total ring of fractions.

## Main results

* `isIntegrallyClosed_tfae_of_finite_minimalPrimes`: Stacks Tag 030C — for a reduced ring with
  finitely many minimal primes, being a normal ring, being integrally closed in the total ring of
  fractions, being a finite product of normal domains, and being the product of the quotients by
  the minimal primes with each quotient integrally closed, are all equivalent.

## Implementation notes

The idempotent argument, which is where the mathematics of the tag lives, is
`isCoprime_of_isIntegrallyClosedIn_pi`: it is stated for an arbitrary family of primes `q : ι →
Ideal R` indexed by any type, since neither finiteness nor an enumeration plays any role in it.
The enumeration is needed only to quote `02LX`, and is confined to
`isLocalization_pi_localization_atPrime`, which restates `02LX` for a product indexed by an
arbitrary finite type; applied to `ι = minimalPrimes R` and `q = Subtype.val` it removes all
index bookkeeping from the rest of the proof.

The following general facts used here are not in Mathlib.

* `nonZeroDivisors_pi`: the nonzerodivisors of a product are the product of the nonzerodivisors.
  With `IsLocalization.instForallPiUniv` this gives `isFractionRing_pi`: `∏ᵢ Frac(Aᵢ)` is a
  total ring of fractions of `∏ᵢ Aᵢ`. No finiteness of the index is needed — denominators are
  chosen componentwise and need no common bound.
* `isIntegrallyClosed_pi_iff`: a finite product is integrally closed in its total ring of
  fractions if and only if each factor is. This is `0CY9` combined with the previous item, and it
  is what identifies the factors `R/𝔭` of the decomposition as integrally closed.
* `IsIdempotentElem.isIntegral`, in `StacksFrontier.RingTheory.IntegralClosure.Pi`: an idempotent is
  integral over its base ring. Serre's criterion needs the same fact.
* `isNormalRing_of_ringEquiv`: normality is invariant under ring isomorphism, the transport
  `0CYA` needs in order to apply to a ring that is merely isomorphic to a product.

The total ring of fractions is Mathlib's `FractionRing R`, which for an arbitrary commutative ring
is `Localization (nonZeroDivisors R)` — the source's `Q(R)` — and `IsIntegrallyClosed R` is by
definition `IsIntegrallyClosedIn R (FractionRing R)`, no domain hypothesis anywhere. So the
source's item (2) is literally the Mathlib class, and `isIntegrallyClosed_iff_isIntegrallyClosedIn`
transports it to any other total ring of fractions `K` of `R`.

Mathlib has no predicate for a normal ring (its `IsIntegrallyClosed` file records this as a TODO,
citing this very tag), so item (1) is inlined as "`Localization.AtPrime 𝔭` is a domain and is
integrally closed, for every prime `𝔭`", the shape `isRegularRing_iff` uses for the same kind of
local condition. For the same reason a normal domain in item (3) is spelled `IsDomain` plus
`IsIntegrallyClosed`.

Two departures from the source's form, both strengthenings, so no direction of the equivalence is
weakened. First, item (3) quantifies over `n : ℕ` and a family `A : Fin n → Type u` in the
universe of `R`: this is the source's "finite product of normal domains", with the factors
produced in the universe where they live. Second, item (4) is added: it pins the canonical
decomposition that the source's proof actually constructs, namely that the componentwise
quotient map `R → ∏ 𝔭 ∈ minimalPrimes R, R/𝔭` is bijective and that each factor is integrally
closed. Item (4) implies item (3) by transporting the finiteness hypothesis to a `Fin n`, and it
is what a reader wants: an abstract isomorphism to *some* product does not say which product.
`IsDomain (R ⧸ 𝔭)` is omitted from item (4) because a minimal prime is prime, so it is an
instance.

Faithfulness. (1) Both hypotheses are used: `IsReduced R` makes the map of item (4) injective and
is what forbids `R = k[x]/(x²)`, integrally closed in `Q(R) = R` but not normal; `(minimalPrimes
R).Finite` is what makes `Q(R)` a finite product of fields, and without it (2) does not imply (3)
— items (1) and (2) hold in general for a normal ring by tag `034M`. (2) The scalars and base are
the source's: integrality in item (2) is over `R` inside `Q(R)`, in item (1) over `R_𝔭` inside its
own fraction field, and in items (3), (4) over each factor inside its own; no base change. (3) The
canonical map is pinned wherever the source names one: item (2) is a statement about
`algebraMap R (FractionRing R)`, and item (4) about `RingHom.pi fun 𝔭 ↦ Ideal.Quotient.mk 𝔭`,
not about the existence of an isomorphism. (4) Non-degenerate: `R = ℤ` satisfies all four items
(one minimal prime `⊥`), as does `R = ℤ × ℤ` (two), while the cusp `R = ℤ[x, y]/(y² - x³)` — a
domain, hence reduced with one minimal prime, so within the hypotheses — satisfies none of them,
`y/x` being integral over `R` but not in it. So the equivalence is not vacuous in either direction.

## References

* [StacksProject 030C](https://stacks.math.columbia.edu/tag/030C)
-/

/-! ### Total rings of fractions of products -/

/-- An element of a product is a (two-sided) nonzerodivisor iff each component is. -/
theorem nonZeroDivisors_pi {ι : Type*} {A : ι → Type*} [∀ i, MonoidWithZero (A i)] :
    nonZeroDivisors (∀ i, A i) = Submonoid.pi Set.univ fun i => nonZeroDivisors (A i) := by
  classical
  ext x
  simp only [Submonoid.mem_pi, Set.mem_univ, forall_const, mem_nonZeroDivisors_iff]
  refine ⟨fun h i => ⟨fun c hc => ?_, fun c hc => ?_⟩, fun h =>
    ⟨fun z hz => funext fun i => (h i).1 (z i) (congrFun hz i),
      fun z hz => funext fun i => (h i).2 (z i) (congrFun hz i)⟩⟩
  · have hs : x * Pi.single i c = 0 := by rw [← Pi.single_mul_right, hc, Pi.single_zero]
    simpa using congrFun (h.1 _ hs) i
  · have hs : Pi.single i c * x = 0 := by rw [← Pi.single_mul_left, hc, Pi.single_zero]
    simpa using congrFun (h.2 _ hs) i

/-- A product of total rings of fractions is a total ring of fractions of the product. -/
instance isFractionRing_pi {ι : Type*} {A K : ι → Type*}
    [∀ i, CommSemiring (A i)] [∀ i, CommSemiring (K i)]
    [∀ i, Algebra (A i) (K i)] [∀ i, IsFractionRing (A i) (K i)] :
    IsFractionRing (∀ i, A i) (∀ i, K i) := by
  rw [IsFractionRing, nonZeroDivisors_pi]
  infer_instance

/-- A finite product of rings is integrally closed in its total ring of fractions if and only if
each factor is. This is Stacks Tag `0CY9` for the total rings of fractions. -/
theorem isIntegrallyClosed_pi_iff {ι : Type*} [Finite ι] (A : ι → Type*)
    [∀ i, CommRing (A i)] :
    IsIntegrallyClosed (∀ i, A i) ↔ ∀ i, IsIntegrallyClosed (A i) := by
  rw [isIntegrallyClosed_iff_isIntegrallyClosedIn (∀ i, FractionRing (A i))]
  exact IsIntegralClosure.pi_iff

/-! ### Comaximality of the minimal primes -/

/-- If `r` dies in `R_𝔭` then `r ∈ 𝔭`: some `s ∉ 𝔭` annihilates `r`, and `𝔭` is prime. -/
private theorem mem_of_algebraMap_atPrime_eq_zero {R : Type*} [CommRing R] (p : Ideal R)
    [p.IsPrime] {r : R} (h : algebraMap R (Localization.AtPrime p) r = 0) : r ∈ p := by
  obtain ⟨s, hs⟩ := (algebraMap_eq_zero_iff_atPrime R p r).mp h
  exact mem_prime_of_smul_eq_zero R p r s (Ideal.mem_primeCompl_iff.mp s.2) hs

/-- If `R` is integrally closed in a product `∏ₖ R_{qₖ}` of localizations at primes, then `q i`
and `q j` are comaximal for `i ≠ j`. The `i`-th idempotent `Pi.single i 1` of the product is a
root of `X² - X`, hence integral over `R`, hence of the form `algebraMap R _ r`; comparing
components, `r ∈ q j` while `1 - r ∈ q i`, and `(1 - r) + r = 1`.

Neither finiteness of the index type nor injectivity of `q` is used. -/
private theorem isCoprime_of_isIntegrallyClosedIn_pi {R : Type*} [CommRing R] {ι : Type*}
    (q : ι → Ideal R) [∀ i, (q i).IsPrime]
    [IsIntegrallyClosedIn R (∀ k, Localization.AtPrime (q k))] {i j : ι} (hij : i ≠ j) :
    IsCoprime (q i) (q j) := by
  classical
  set e : ∀ k, Localization.AtPrime (q k) := Pi.single i 1
  have he : IsIdempotentElem e := by
    rw [IsIdempotentElem]
    funext k
    rcases eq_or_ne k i with rfl | hk
    · simp [e]
    · simp [e, Pi.single_eq_of_ne hk]
  have hint : IsIntegral R e := IsIdempotentElem.isIntegral he
  obtain ⟨r, hr⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral hint
  have hcomp : ∀ k, algebraMap R (Localization.AtPrime (q k)) r
      = e k := fun k => congrFun hr k
  refine Ideal.isCoprime_iff_exists.mpr ⟨1 - r, ?_, r, ?_, by ring⟩
  · exact mem_of_algebraMap_atPrime_eq_zero _ (by rw [map_sub, map_one, hcomp i]; simp [e])
  · exact mem_of_algebraMap_atPrime_eq_zero _
      (by rw [hcomp j]; simp [e, Pi.single_eq_of_ne (Ne.symm hij)])

/-- **Stacks Tag `02LX`** for an arbitrary finite indexing of the minimal primes: if `q`
enumerates the minimal primes of a reduced ring `R` without repetition, then `∏ᵢ R_{qᵢ}` is a
total ring of fractions of `R`. The hypothesis of `02LX` that the minimal primes cover the
zerodivisors is automatic for a reduced ring, by Tag `00EW`. -/
theorem isLocalization_pi_localization_atPrime {R : Type*} [CommRing R] [IsReduced R]
    {ι : Type*} [Finite ι] (q : ι → Ideal R) [∀ i, (q i).IsPrime]
    (hmem : ∀ i, q i ∈ minimalPrimes R) (hinj : Function.Injective q)
    (hsurj : ∀ p ∈ minimalPrimes R, ∃ i, q i = p) :
    IsLocalization (nonZeroDivisors R) (∀ i, Localization.AtPrime (q i)) := by
  set e := (Finite.equivFin ι).symm
  have hunion : (⋃ i, (q i : Set R)) = ⋃ p ∈ minimalPrimes R, (p : Set R) :=
    subset_antisymm (Set.iUnion_subset fun i => Set.subset_biUnion_of_mem (hmem i))
      (Set.iUnion₂_subset fun p hp => by
        obtain ⟨i, rfl⟩ := hsurj p hp
        exact Set.subset_iUnion (fun i => (q i : Set R)) i)
  -- `zeroDivisorsSet` (the complement of `nonZeroDivisors`) and `zeroDivisorSet` (an existential)
  -- are two spellings of the same set; `mem_zeroDivisorsSet_iff` identifies them.
  have hsets : zeroDivisorsSet R = zeroDivisorSet R :=
    Set.ext fun x => (mem_zeroDivisorsSet_iff x).trans mem_zeroDivisorSet.symm
  have hzd : zeroDivisorsSet R = ⋃ k, (q (e k) : Set R) := by
    rw [hsets, e.surjective.iUnion_comp fun i => (q i : Set R),
      ← iUnion_minimalPrimes_eq_zeroDivisors R, hunion]
  obtain ⟨f⟩ := total_fraction_ring_isoProd_localization_atPrime (Nat.card ι) (fun k => q (e k))
    (fun k => hmem _) (hinj.comp e.injective) hzd
  have : IsLocalization (nonZeroDivisors R) (∀ k, Localization.AtPrime (q (e k))) :=
    IsLocalization.isLocalization_of_algEquiv _ f
  exact IsLocalization.isLocalization_of_algEquiv _
    (AlgEquiv.piCongrLeft R (fun i => Localization.AtPrime (q i)) e)

/-- For a reduced ring with finitely many minimal primes that is integrally closed in its total
ring of fractions, distinct minimal primes are comaximal. -/
private theorem pairwise_isCoprime_minimalPrimes {R : Type u} [CommRing R] [IsReduced R]
    (hR : (minimalPrimes R).Finite) [IsIntegrallyClosed R] :
    Pairwise (Function.onFun IsCoprime fun p : minimalPrimes R => (p : Ideal R)) := by
  have hfin : Finite (minimalPrimes R) := hR
  have hprime : ∀ p : minimalPrimes R, (p : Ideal R).IsPrime := fun p => p.2.1.1
  have : IsLocalization (nonZeroDivisors R)
      (∀ p : minimalPrimes R, Localization.AtPrime (p : Ideal R)) :=
    isLocalization_pi_localization_atPrime _ (fun p => p.2) Subtype.val_injective
      fun p hp => ⟨⟨p, hp⟩, rfl⟩
  have : IsIntegrallyClosedIn R (∀ p : minimalPrimes R, Localization.AtPrime (p : Ideal R)) :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn _).mp ‹IsIntegrallyClosed R›
  exact fun p p' hpp' => isCoprime_of_isIntegrallyClosedIn_pi _ hpp'

/-- Chinese remainder theorem for the minimal primes: if the minimal primes of a reduced ring
with finitely many of them are pairwise comaximal, then `R → ∏_𝔭 R/𝔭` is bijective. Injectivity
is where `IsReduced R` enters: the minimal primes intersect in `0`. -/
private theorem bijective_pi_quotient_mk_minimalPrimes {R : Type u} [CommRing R] [IsReduced R]
    (hR : (minimalPrimes R).Finite)
    (hcop : Pairwise (Function.onFun IsCoprime fun p : minimalPrimes R => (p : Ideal R))) :
    Function.Bijective
      (RingHom.pi fun p : minimalPrimes R => Ideal.Quotient.mk (p : Ideal R)) := by
  have hfin : Finite (minimalPrimes R) := hR
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx => ?_, fun x => ?_⟩
  · rw [eq_zero_iff_mem_all_minimalPrimes R]
    intro p hp
    simpa [RingHom.pi_apply, Ideal.Quotient.eq_zero_iff_mem] using congrFun hx ⟨p, hp⟩
  · obtain ⟨r, hr⟩ := Ideal.pi_quotient_surjective hcop x
    exact ⟨r, funext hr⟩

/-! ### Normality is invariant under isomorphism -/

/-- Normality of a ring (Stacks Tag `00GV`) is invariant under ring isomorphism: a prime `𝔭` of
`R` is the contraction of a prime of `S`, and the two localizations agree. -/
private theorem isNormalRing_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (h : IsNormalRing S) : IsNormalRing R := by
  intro p _
  obtain ⟨hd, hi⟩ := h (p.comap (e.symm : S →+* R))
  let f : Localization.AtPrime p ≃+* Localization.AtPrime (p.comap (e.symm : S →+* R)) :=
    Localization.localRingEquiv p _ e (Ideal.comap_of_equiv e).symm
  exact ⟨Function.Injective.isDomain f f.injective, IsIntegrallyClosed.of_equiv f.symm⟩

/-! ### The theorem -/

/-- **Stacks 030C.** Let `R` be a reduced ring with finitely many minimal primes. Then the
following are equivalent: (1) `R` is a normal ring, i.e. all its localizations at primes are
normal domains; (2) `R` is integrally closed in its total ring of fractions; (3) `R` is a finite
product of normal domains; (4) the canonical map from `R` to the product of the quotients `R/𝔭`
by its minimal primes is bijective and each such quotient is integrally closed. -/
@[stacks 030C, ega "IV 5.13.5" "Noeth ⇒ product of doms", ega "IV 6.14.1.1" "(i)"]
theorem isIntegrallyClosed_tfae_of_finite_minimalPrimes {R : Type u} [CommRing R]
    [IsReduced R] (hR : (minimalPrimes R).Finite) :
    List.TFAE
      [ ∀ (p : Ideal R) [p.IsPrime],
          IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p),
        IsIntegrallyClosed R,
        ∃ (n : ℕ) (A : Fin n → Type u) (_ : ∀ i, CommRing (A i)),
          (∀ i, IsDomain (A i)) ∧ (∀ i, IsIntegrallyClosed (A i)) ∧
            Nonempty (R ≃+* ∀ i, A i),
        (∀ p ∈ minimalPrimes R, IsIntegrallyClosed (R ⧸ p)) ∧
          Function.Bijective
            (RingHom.pi fun p : minimalPrimes R => Ideal.Quotient.mk (p : Ideal R)) ] := by
  have hfin : Finite (minimalPrimes R) := hR
  have hprime : ∀ p : minimalPrimes R, (p : Ideal R).IsPrime := fun p => p.2.1.1
  tfae_have 1 → 2 := fun h => (isNormalRing_iff.mpr h).isIntegrallyClosed
  tfae_have 2 → 4 := by
    intro h
    have hbij := bijective_pi_quotient_mk_minimalPrimes hR (pairwise_isCoprime_minimalPrimes hR)
    refine ⟨fun p hp => ?_, hbij⟩
    have hic : IsIntegrallyClosed (∀ p : minimalPrimes R, R ⧸ (p : Ideal R)) :=
      IsIntegrallyClosed.of_equiv (RingEquiv.ofBijective _ hbij)
    exact (isIntegrallyClosed_pi_iff _).mp hic ⟨p, hp⟩
  tfae_have 4 → 3 := by
    rintro ⟨h1, h2⟩
    set ε := Finite.equivFin (minimalPrimes R)
    refine ⟨Nat.card (minimalPrimes R), fun k => R ⧸ ((ε.symm k : minimalPrimes R) : Ideal R),
      fun k => inferInstance, fun k => inferInstance, fun k => h1 _ (ε.symm k).2, ⟨?_⟩⟩
    exact (RingEquiv.ofBijective _ h2).trans
      (RingEquiv.piCongrLeft (fun p : minimalPrimes R => R ⧸ (p : Ideal R)) ε.symm).symm
  tfae_have 3 → 1 := by
    rintro ⟨n, A, hcr, hdom, hic, ⟨e⟩⟩
    have hn : ∀ k, IsNormalRing (A k) := by
      intro k p hp
      have : IsDomain (A k) := hdom k
      have : IsIntegrallyClosed (A k) := hic k
      exact ⟨inferInstance, isIntegrallyClosed_of_isLocalization (R := A k)
        (S := Localization.AtPrime p) p.primeCompl p.primeCompl_le_nonZeroDivisors⟩
    exact isNormalRing_of_ringEquiv (S := ∀ i, A i) e (isNormalRing_pi hn)
  tfae_finish

end
