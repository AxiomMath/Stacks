module

public import StacksFrontier.RingTheory.LocalCohomology.Cutoff.Attainment

/-!
# The cutoff step of Stacks 0BJW, with the formal-fibre hypothesis only along `V(I)`

Let `A` be a universally catenary Noetherian ring, `I ⊆ A` an ideal and `M` a finite
`A`-module. This file proves the two cutoff steps of Stacks 0BJW — the two bounds of Stacks 0BJT
survive localizing at a prime and completing — with the formal-fibres hypothesis imposed only at
the primes of `V(I)`, as in Stacks 0BJY, rather than at every prime of `A`.

## Main results

* `Stacks.LocalCohomology.lt_localCohomologyCutoff_adicCompletion_localization_zeroLocus` —
  the cutoff step of Stacks 0BJW's first clause, formal fibres only along `V(I)`.
* `Stacks.LocalCohomology.exists_localCohomologyCutoff_adicCompletion_localization_eq_zeroLocus`
  — the cutoff step of Stacks 0BJW's second clause, formal fibres only along `V(I)`.

## References

* [Stacks Project, Tag 0BJT](https://stacks.math.columbia.edu/tag/0BJT)
* [Stacks Project, Tag 0BJW](https://stacks.math.columbia.edu/tag/0BJW)
* [Stacks Project, Tag 0BJY](https://stacks.math.columbia.edu/tag/0BJY)
-/

@[expose] public section

universe u v

namespace Stacks.LocalCohomology

section Completion

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
  (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M] (n : ℕ)

omit [IsNoetherianRing A] in
/-- At a prime not containing `I`, the extension of `I` to the localization at that prime is the
whole ring. -/
private theorem ideal_map_atPrime_eq_top_of_notLe (p : PrimeSpectrum A) (hp : ¬ I ≤ p.asIdeal) :
    I.map (algebraMap A (Localization.AtPrime p.asIdeal)) = ⊤ := by
  by_contra htop
  have hne : I.map (algebraMap A (Localization.AtPrime p.asIdeal)) ≠ ⊤ := htop
  rw [IsLocalization.map_algebraMap_ne_top_iff_disjoint p.asIdeal.primeCompl
    (Localization.AtPrime p.asIdeal), Set.disjoint_left] at hne
  exact hp fun x hx ↦ by_contra fun hxp ↦ hne (Ideal.mem_primeCompl_iff.mpr hxp) hx

omit [IsNoetherianRing A] [Module.Finite A M] in
/-- At a prime outside `V(I)`, every `n` is less than the cutoff of the completed localization at
that prime. -/
private theorem lt_localCohomologyCutoff_adicCompletion_localization_of_notLe
    (p : PrimeSpectrum A) (hp : ¬ I ≤ p.asIdeal) :
    (n : ℕ∞) < localCohomologyCutoff
      (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (Localization.AtPrime p.asIdeal))
      ((I.map (algebraMap A (Localization.AtPrime p.asIdeal))).map
        (algebraMap (Localization.AtPrime p.asIdeal)
          (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
            (Localization.AtPrime p.asIdeal))))
      (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M)) := by
  rw [ideal_map_atPrime_eq_top_of_notLe A I p hp, Ideal.map_top, localCohomologyCutoff_top]
  exact ENat.natCast_lt_top n

/-- **The cutoff step of Stacks 0BJW's first clause, formal fibres only along `V(I)`.** If the
cutoff of `M` exceeds `n` and the formal fibres of the local rings of `A` at the primes of
`V(I)` satisfy `(S_n)`, then the cutoff still exceeds `n` after localizing at any prime and
completing. -/
public theorem lt_localCohomologyCutoff_adicCompletion_localization_zeroLocus
    (hA : Ring.IsUniversallyCatenary A)
    (hformal : ∀ p : PrimeSpectrum A, I ≤ p.asIdeal →
      FormalFibersHavePropertySk (Localization.AtPrime p.asIdeal) n)
    (hn : (n : ℕ∞) < localCohomologyCutoff A I M) (p : PrimeSpectrum A) :
    (n : ℕ∞) < localCohomologyCutoff
      (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (Localization.AtPrime p.asIdeal))
      ((I.map (algebraMap A (Localization.AtPrime p.asIdeal))).map
        (algebraMap (Localization.AtPrime p.asIdeal)
          (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
            (Localization.AtPrime p.asIdeal))))
      (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M)) := by
  by_cases hp : I ≤ p.asIdeal
  · exact lt_localCohomologyCutoff_adicCompletion (Localization.AtPrime p.asIdeal)
      (I.map (algebraMap A (Localization.AtPrime p.asIdeal)))
      (LocalizedModule p.asIdeal.primeCompl M) n
      (Ring.IsUniversallyCatenary.localization p.asIdeal.primeCompl _ hA) (hformal p hp)
      (hn.trans_le (localCohomologyCutoff_le_localization I M p.asIdeal))
  · exact lt_localCohomologyCutoff_adicCompletion_localization_of_notLe A I M n p hp

end Completion

/-- **The cutoff step of Stacks 0BJW's second clause, formal fibres only along `V(I)`.** If the
cutoff `s` of `M` is finite and the formal fibres of the local rings of `A` at the primes of
`V(I)` satisfy `(S_{s-1})`, then `s` is realised exactly: there is a prime `𝔮 ∈ V(I)` for which
the completion of `A_𝔮` at its maximal ideal, with the extended ideal and the completed module,
again has cutoff `s`. -/
public theorem exists_localCohomologyCutoff_adicCompletion_localization_eq_zeroLocus
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hA : Ring.IsUniversallyCatenary A) (hs : localCohomologyCutoff A I M < ⊤)
    (hformal : ∀ p : PrimeSpectrum A, I ≤ p.asIdeal →
      FormalFibersHavePropertySk (Localization.AtPrime p.asIdeal)
        ((localCohomologyCutoff A I M).toNat - 1)) :
    ∃ q : PrimeSpectrum A, I ≤ q.asIdeal ∧
      localCohomologyCutoff
          (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal))
            (Localization.AtPrime q.asIdeal))
          ((I.map (algebraMap A (Localization.AtPrime q.asIdeal))).map
            (algebraMap (Localization.AtPrime q.asIdeal)
              (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal))
                (Localization.AtPrime q.asIdeal))))
          (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal))
            (LocalizedModule q.asIdeal.primeCompl M)) =
        localCohomologyCutoff A I M := by
  set s := localCohomologyCutoff A I M
  obtain ⟨q, hq, hloc⟩ := exists_localCohomologyCutoff_localization_eq A I M hs
  have hks : s ≤ ((s.toNat - 1 + 1 : ℕ) : ℕ∞) := by
    calc s = (s.toNat : ℕ∞) := (ENat.natCast_toNat (ne_top_of_lt hs)).symm
      _ ≤ ((s.toNat - 1 + 1 : ℕ) : ℕ∞) := by exact_mod_cast (by omega : s.toNat ≤ s.toNat - 1 + 1)
  exact ⟨q, hq, (localCohomologyCutoff_adicCompletion_eq (Localization.AtPrime q.asIdeal)
    (I.map (algebraMap A (Localization.AtPrime q.asIdeal)))
    (LocalizedModule q.asIdeal.primeCompl M) (s.toNat - 1)
    (Ring.IsUniversallyCatenary.localization q.asIdeal.primeCompl _ hA) (hformal q hq)
    (hloc.trans_le hks)).trans hloc⟩

end Stacks.LocalCohomology

end
