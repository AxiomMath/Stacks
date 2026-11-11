module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-!
# A connected ring which is locally a domain

Let `R` be a nonzero Noetherian ring whose localization at every maximal ideal is a domain and
which has no idempotents besides `0` and `1`. Then `R` is a domain.

The ring is reduced, since reducedness is local at the maximal ideals. A maximal ideal `𝔪`
contains a single minimal prime, the kernel of `R → R_𝔪`, because `R_𝔪` is a domain; so two
distinct minimal primes are comaximal. If `𝔭` is a minimal prime and `Q` is the intersection of
the others, then `𝔭 + Q = R` and `𝔭 ∩ Q` is the nilradical, which is zero. Writing `1 = a + b`
with `a ∈ 𝔭` and `b ∈ Q` makes `a` an idempotent, which cannot be `1`; so `a = 0`, `Q = R` and
`𝔭 = 0` is prime.

## Main results

* `isDomain_of_isDomain_localization_of_isIdempotentElem`: a nonzero Noetherian ring whose
  localizations at maximal ideals are domains, and whose only idempotents are `0` and `1`, is a
  domain.
-/

@[expose] public section

namespace Ideal

variable {R : Type*} [CommRing R]

/-- Two minimal primes contained in a maximal ideal `𝔪` are equal when `R_𝔪` is a domain: both
are the kernel of `R → R_𝔪`. -/
theorem eq_of_mem_minimalPrimes_of_le_of_isDomain_localization {m p q : Ideal R} [m.IsMaximal]
    [IsDomain (Localization.AtPrime m)] (hp : p ∈ minimalPrimes R) (hq : q ∈ minimalPrimes R)
    (hpm : p ≤ m) (hqm : q ≤ m) : p = q := by
  have key : ∀ r : Ideal R, r ∈ minimalPrimes R → r ≤ m →
      r = (⊥ : Ideal (Localization.AtPrime m)).comap
        (algebraMap R (Localization.AtPrime m)) := by
    intro r hr hrm
    have : r.IsPrime := hr.1.1
    have hdisj : Disjoint (m.primeCompl : Set R) r := by
      simpa [Ideal.primeCompl, ← le_compl_iff_disjoint_left] using hrm
    have hle : (⊥ : Ideal (Localization.AtPrime m)).comap
        (algebraMap R (Localization.AtPrime m)) ≤ r := by
      calc _ ≤ (r.map (algebraMap R (Localization.AtPrime m))).comap
            (algebraMap R (Localization.AtPrime m)) := Ideal.comap_mono bot_le
        _ = r := IsLocalization.under_map_of_isPrime_disjoint m.primeCompl _ ‹_› hdisj
    exact le_antisymm (hr.2 ⟨Ideal.comap_isPrime _ _, bot_le⟩ hle) hle
  rw [key p hp hpm, key q hq hqm]

/-- **A connected ring which is locally a domain is a domain.** A nonzero Noetherian ring whose
localization at every maximal ideal is a domain and whose only idempotents are `0` and `1` is a
domain. -/
theorem isDomain_of_isDomain_localization_of_isIdempotentElem [IsNoetherianRing R]
    [Nontrivial R] (hloc : ∀ (m : Ideal R) [m.IsMaximal], IsDomain (Localization.AtPrime m))
    (hidem : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) : IsDomain R := by
  classical
  have hred : IsReduced R := isReduced_ofLocalizationMaximal R fun m hm => by
    have := hloc m
    infer_instance
  have hcop : ∀ p q : Ideal R, p ∈ minimalPrimes R → q ∈ minimalPrimes R → p ≠ q →
      IsCoprime p q := by
    intro p q hp hq hpq
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have := hloc m
    exact hpq (eq_of_mem_minimalPrimes_of_le_of_isDomain_localization hp hq
      (le_sup_left.trans hle) (le_sup_right.trans hle))
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := m) bot_le
  let s := (minimalPrimes.finite_of_isNoetherianRing R).toFinset.erase p
  let Q : Ideal R := ⨅ q ∈ s, q
  have hpQ : IsCoprime p Q := Ideal.isCoprime_biInf fun q hq => by
    obtain ⟨hqp, hq⟩ := Finset.mem_erase.1 hq
    exact hcop p q hp ((minimalPrimes.finite_of_isNoetherianRing R).mem_toFinset.1 hq)
      (Ne.symm hqp)
  have hinf : ∀ x ∈ p, x ∈ Q → x = 0 := by
    intro x hxp hxQ
    have hrad : x ∈ (⊥ : Ideal R).radical := by
      rw [← Ideal.sInf_minimalPrimes]
      refine Submodule.mem_sInf.2 fun q hq => ?_
      by_cases hqp : q = p
      · exact hqp ▸ hxp
      · exact (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hxQ q)
          (Finset.mem_erase.2 ⟨hqp, (minimalPrimes.finite_of_isNoetherianRing R).mem_toFinset.2
            hq⟩)
    obtain ⟨n, hn⟩ := hrad
    exact IsReduced.eq_zero x ⟨n, by simpa using hn⟩
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 hpQ
  have hab0 : a * b = 0 :=
    hinf _ (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_left _ _ hb)
  have hidema : IsIdempotentElem a := by
    change a * a = a
    calc a * a = a * (a + b) - a * b := by ring
      _ = a := by rw [hab, hab0]; ring
  have hpprime : p.IsPrime := hp.1.1
  rcases hidem a hidema with rfl | rfl
  · have hb1 : b = 1 := by simpa using hab
    have hp0 : p = ⊥ := by
      refine eq_bot_iff.2 fun x hx => ?_
      exact (Submodule.mem_bot R).2 (hinf x hx (by
        simpa [hb1] using Ideal.mul_mem_left Q x hb))
    rw [hp0] at hpprime
    exact IsDomain.of_bot_isPrime R
  · exact absurd (p.eq_top_of_isUnit_mem ha isUnit_one) hpprime.ne_top

end Ideal

end
