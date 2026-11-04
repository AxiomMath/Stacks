module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Killing an ideal of nilpotents changes neither the spectrum nor heights

Let `I` be an ideal of a commutative ring `R` consisting of nilpotent elements, that is
`I ≤ nilradical R`. Every prime of `R` contains `I`, so contraction along `R → R ⧸ I` is an
order isomorphism `Spec (R ⧸ I) ≃ Spec R`; consequently the height of a prime is unchanged by
the quotient, and adding `I` to an ideal does not change its minimal primes.

## Main definitions

* `PrimeSpectrum.comapQuotientMkOrderIso`: the order isomorphism
  `Spec (R ⧸ I) ≃o Spec R` for `I ≤ nilradical R`.

## Main results

* `Ideal.height_comap_quotientMk_of_le_nilradical`: the height of a prime of `R ⧸ I` equals the
  height of its contraction to `R`.
* `Ideal.minimalPrimes_sup_of_le_nilradical`: `(J ⊔ I).minimalPrimes = J.minimalPrimes`.
* `Ideal.mem_minimalPrimes_comap_quotientMk_of_le_nilradical`: a minimal prime over the image of
  `J` in `R ⧸ I` contracts to a minimal prime over `J`.
* `Ideal.le_height_of_mem_minimalPrimes_map_quotientMk`: a height bound on the minimal primes of
  `J` in `R` is inherited by the minimal primes of its image in `R ⧸ I`.
* `Ideal.minimalPrimes_map_quotientMk_of_le_nilradical`: extension along `R → R ⧸ I` is a
  bijection from the minimal primes over `J` onto those over the image of `J`.
* `Ideal.exists_mem_minimalPrimes_map_quotientMk_height_eq`: if some minimal prime over `J` has
  height `e`, then so does some minimal prime over the image of `J` in `R ⧸ I`.

## Implementation notes

Bijectivity of the contraction is Mathlib's
`PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical`; what is added here is that it
reflects the order, which follows from `Ideal.map_comap_of_surjective` because the quotient map
is surjective. The height statement is then
`Order.height_orderIso` read through `PrimeSpectrum.height_eq_orderHeight`.

The statement about minimal primes is obtained from `Ideal.radical_minimalPrimes`: adding an
ideal of nilpotents does not change the radical, because `I ≤ nilradical R ≤ J.radical`.
-/

@[expose] public noncomputable section

universe u

variable {R : Type u} [CommRing R]

/-- **A ring isomorphism carries the nilradical to the nilradical.** This is
`Ideal.map_radical_of_surjective` at the zero ideal. -/
theorem Ideal.map_nilradical {S : Type*} [CommRing S] (e : R ≃+* S) :
    (nilradical R).map (e : R →+* S) = nilradical S := by
  rw [nilradical, nilradical, Ideal.zero_eq_bot, Ideal.zero_eq_bot,
    Ideal.map_radical_of_surjective e.surjective (by rw [RingHom.ker_coe_equiv]),
    Ideal.map_bot]

/-- **A ring isomorphism induces one of the reductions.** -/
def RingEquiv.quotientNilradical {S : Type*} [CommRing S] (e : R ≃+* S) :
    (R ⧸ nilradical R) ≃+* (S ⧸ nilradical S) :=
  Ideal.quotientEquiv _ _ e (Ideal.map_nilradical e).symm

/-- The isomorphism `RingEquiv.quotientNilradical e` sends the class of `x` to the class of
`e x`. -/
@[simp]
theorem RingEquiv.quotientNilradical_mk {S : Type*} [CommRing S] (e : R ≃+* S) (x : R) :
    e.quotientNilradical (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (e x) :=
  rfl

/-- **Contraction along a quotient by nilpotents is an order isomorphism of spectra.** If
`I ≤ nilradical R` then every prime of `R` contains `I`, so the primes of `R ⧸ I` and of `R`
correspond, and the correspondence is an isomorphism of posets. -/
@[ega "0 16.1.2" "special case", ega "I 1.1.12" "partial"]
def PrimeSpectrum.comapQuotientMkOrderIso {I : Ideal R} (hI : I ≤ nilradical R) :
    PrimeSpectrum (R ⧸ I) ≃o PrimeSpectrum R where
  toEquiv := Equiv.ofBijective _ (PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical hI)
  map_rel_iff' {p q} := by
    change Ideal.comap (Ideal.Quotient.mk I) p.asIdeal ≤ Ideal.comap (Ideal.Quotient.mk I) q.asIdeal
      ↔ p ≤ q
    refine ⟨fun h => ?_, fun h => Ideal.comap_mono h⟩
    rw [← PrimeSpectrum.asIdeal_le_asIdeal,
      ← Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective p.asIdeal,
      ← Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective q.asIdeal]
    exact Ideal.map_mono h

/-- The order isomorphism `PrimeSpectrum.comapQuotientMkOrderIso hI` sends a prime of `R ⧸ I`
to its contraction along `R → R ⧸ I`. -/
@[simp]
theorem PrimeSpectrum.comapQuotientMkOrderIso_apply {I : Ideal R} (hI : I ≤ nilradical R)
    (p : PrimeSpectrum (R ⧸ I)) :
    PrimeSpectrum.comapQuotientMkOrderIso hI p = PrimeSpectrum.comap (Ideal.Quotient.mk I) p :=
  rfl

/-- **A quotient by nilpotents preserves heights.** The height of a prime of `R ⧸ I` is the
height of the prime of `R` it contracts to. -/
theorem Ideal.height_comap_quotientMk_of_le_nilradical {I : Ideal R} (hI : I ≤ nilradical R)
    (q : Ideal (R ⧸ I)) [q.IsPrime] :
    (q.comap (Ideal.Quotient.mk I)).height = q.height := by
  have h := Order.height_orderIso (PrimeSpectrum.comapQuotientMkOrderIso hI)
    (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum (R ⧸ I))
  rwa [← PrimeSpectrum.height_eq_orderHeight, ← PrimeSpectrum.height_eq_orderHeight] at h

/-- **Adding an ideal of nilpotents does not change the radical.** -/
theorem Ideal.radical_sup_of_le_nilradical {I : Ideal R} (hI : I ≤ nilradical R) (J : Ideal R) :
    (J ⊔ I).radical = J.radical := by
  refine le_antisymm ?_ (Ideal.radical_mono le_sup_left)
  rw [← Ideal.radical_idem J]
  exact Ideal.radical_mono (sup_le (Ideal.le_radical) (hI.trans (Ideal.radical_mono bot_le)))

/-- **Adding an ideal of nilpotents does not change the minimal primes.** -/
theorem Ideal.minimalPrimes_sup_of_le_nilradical {I : Ideal R} (hI : I ≤ nilradical R)
    (J : Ideal R) : (J ⊔ I).minimalPrimes = J.minimalPrimes := by
  rw [← Ideal.radical_minimalPrimes, Ideal.radical_sup_of_le_nilradical hI,
    Ideal.radical_minimalPrimes]

/-- **A minimal prime over the image of an ideal in a quotient by nilpotents contracts to a
minimal prime over the ideal.** -/
theorem Ideal.mem_minimalPrimes_comap_quotientMk_of_le_nilradical {I : Ideal R}
    (hI : I ≤ nilradical R) {J : Ideal R} {q : Ideal (R ⧸ I)}
    (hq : q ∈ (J.map (Ideal.Quotient.mk I)).minimalPrimes) :
    q.comap (Ideal.Quotient.mk I) ∈ J.minimalPrimes := by
  have h := Ideal.minimalPrimes_comap_of_surjective
    (f := Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective hq
  rwa [Ideal.comap_map_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
    Ideal.minimalPrimes_sup_of_le_nilradical hI] at h

/-- **A height bound on the minimal primes of an ideal passes to a quotient by nilpotents.** If
every minimal prime over `J` has height at least `n`, then so does every minimal prime over the
image of `J` in `R ⧸ I`. -/
theorem Ideal.le_height_of_mem_minimalPrimes_map_quotientMk {I : Ideal R}
    (hI : I ≤ nilradical R) {J : Ideal R} {n : ℕ∞}
    (hJ : ∀ p ∈ J.minimalPrimes, n ≤ p.height) {q : Ideal (R ⧸ I)}
    (hq : q ∈ (J.map (Ideal.Quotient.mk I)).minimalPrimes) : n ≤ q.height := by
  have : q.IsPrime := hq.isPrime
  rw [← Ideal.height_comap_quotientMk_of_le_nilradical hI q]
  exact hJ _ (Ideal.mem_minimalPrimes_comap_quotientMk_of_le_nilradical hI hq)

/-- **The minimal primes over an ideal and over its image in a quotient by nilpotents
correspond.** Extension along `R → R ⧸ I` is a bijection from the minimal primes over `J` to
those over `J·(R ⧸ I)`. -/
theorem Ideal.minimalPrimes_map_quotientMk_of_le_nilradical {I : Ideal R}
    (hI : I ≤ nilradical R) (J : Ideal R) :
    (J.map (Ideal.Quotient.mk I)).minimalPrimes =
      Ideal.map (Ideal.Quotient.mk I) '' J.minimalPrimes := by
  rw [Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective J, Ideal.mk_ker,
    Ideal.minimalPrimes_sup_of_le_nilradical hI]

/-- **An exact height on a minimal prime passes to a quotient by nilpotents.** If some minimal
prime over `J` has height `e`, then some minimal prime over the image of `J` in `R ⧸ I` has
height `e`. -/
theorem Ideal.exists_mem_minimalPrimes_map_quotientMk_height_eq {I : Ideal R}
    (hI : I ≤ nilradical R) {J : Ideal R} {p : Ideal R} (hp : p ∈ J.minimalPrimes) {e : ℕ∞}
    (hph : p.height = e) :
    ∃ q : Ideal (R ⧸ I), q ∈ (J.map (Ideal.Quotient.mk I)).minimalPrimes ∧ q.height = e := by
  refine ⟨p.map (Ideal.Quotient.mk I), ?_, ?_⟩
  · rw [Ideal.minimalPrimes_map_quotientMk_of_le_nilradical hI]
    exact ⟨p, hp, rfl⟩
  · have hqmem : p.map (Ideal.Quotient.mk I) ∈ (J.map (Ideal.Quotient.mk I)).minimalPrimes := by
      rw [Ideal.minimalPrimes_map_quotientMk_of_le_nilradical hI]
      exact ⟨p, hp, rfl⟩
    have : (p.map (Ideal.Quotient.mk I)).IsPrime := hqmem.isPrime
    have hcomap : (p.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = p := by
      rw [Ideal.comap_map_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
      have : p.IsPrime := hp.isPrime
      exact sup_eq_left.mpr (hI.trans (nilradical_le_prime p))
    rw [← Ideal.height_comap_quotientMk_of_le_nilradical hI, hcomap, hph]

end
