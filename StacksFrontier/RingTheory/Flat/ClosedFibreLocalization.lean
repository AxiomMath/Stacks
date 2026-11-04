module

public import StacksFrontier.RingTheory.Flat.FlatAtPointCriteria
public import StacksFrontier.RingTheory.Flat.FlatLocusAway
public import StacksFrontier.RingTheory.Flat.UniversallyInjectiveBaseChange

/-!
# Flatness of the localization at the elements regular on the closed fibre

Let `R → S` be a ring map with `R` local, let `N` be an `S`-module and write
`Σ ⊆ S` for the elements acting injectively on the closed fibre `N / 𝔪_R N`. This file proves
that `Σ⁻¹N` is flat over `R` as soon as `N_p` is flat over `R` for every associated prime `p` of
the closed fibre.

This is the first of the two steps in the converse implication of Stacks 05UA; the second is
Stacks 0AT4.

## Main results

* `Module.Flat.localizedModule_primeCompl_of_le`: flatness over a base ring of a localization at
  a prime passes to localizations at smaller primes.
* `Stacks.Flatness.flat_localizedModule_nonZeroSMulDivisors_closedFibre`: `Σ⁻¹N` is flat over
  `R` whenever `N_p` is flat over `R` at every associated prime `p` of `N / 𝔪_R N`.

## Implementation notes

The statement `Module.flat_localizedModule_iff_forall_flat_atPrime` reduces flatness of `Σ⁻¹N`
to flatness of `N_q` at every prime `q` of `S` disjoint from `Σ`. Stacks 05DE, in the form
`Stacks.UniversalInjectivity.range_under_localization_nonZeroSMulDivisors`, says that such a `q`
is contained in an associated prime `p` of the closed fibre; and `N_q` is a further localization
of `N_p`, hence flat over `R` as soon as `N_p` is. So the hypothesis is needed only at the
associated primes, which is exactly what condition (2) of Stacks 05UA provides.

The closed fibre is spelled, as in
`StacksFrontier/RingTheory/Flat/UniversallyInjectiveBaseChange.lean`, as the quotient of `N` by
`Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) • ⊤`, so that it is a module over the
closed-fibre ring `S / 𝔪_R S`; the associated primes are the strict associated primes
`assStacks` of Stacks 00LA.

## References

* [Stacks Project, Tag 05DE](https://stacks.math.columbia.edu/tag/05DE)
* [Stacks Project, Tag 05UA](https://stacks.math.columbia.edu/tag/05UA)
-/

@[expose] public section

open IsLocalRing

/-- **Flatness over a base ring at a prime passes to smaller primes.** For a ring map `A → B`,
a `B`-module `M` and ideals `q ≤ p` of `B`, the localization `M_q` is a further localization of
`M_p` over `B`, so it is flat over `A` as soon as `M_p` is. -/
theorem Module.Flat.localizedModule_primeCompl_of_le {A B M : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    {q p : Ideal B} [q.IsPrime] [p.IsPrime] (hqp : q ≤ p)
    (h : Module.Flat A (LocalizedModule p.primeCompl M)) :
    Module.Flat A (LocalizedModule q.primeCompl M) := by
  have hle : p.primeCompl ≤ q.primeCompl := fun _ hx =>
    Ideal.mem_primeCompl_iff.mpr fun hxq => Ideal.mem_primeCompl_iff.mp hx (hqp hxq)
  have : Module.Flat A (LocalizedModule p.primeCompl M) := h
  exact Module.Flat.of_isLocalizedModule_of_tower q.primeCompl
    (IsLocalizedModule.liftOfLE p.primeCompl q.primeCompl hle
      (LocalizedModule.mkLinearMap p.primeCompl M)
      (LocalizedModule.mkLinearMap q.primeCompl M))

namespace Stacks.Flatness

variable {R S N : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
  [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
  [IsNoetherianRing (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R))]
  [Module.Finite (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R))
    (N ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N)))]

include R S N in
/-- **The localization step in the converse of Stacks 05UA.** Let `R → S` be a ring map with `R`
local, let `N` be an `S`-module whose closed fibre `N / 𝔪_R N` is finite over the Noetherian
closed-fibre ring `S / 𝔪_R S`, and let `Σ ⊆ S` be the elements acting injectively on that closed
fibre. If `N_p` is flat over `R` for every associated prime `p` of the closed fibre, then `Σ⁻¹N`
is flat over `R`.

By Stacks 05DE every prime of `S` disjoint from `Σ` is contained in an associated prime of the
closed fibre, and flatness over `R` of a localization at a prime passes to smaller primes; so the
pointwise criterion `Module.flat_localizedModule_iff_forall_flat_atPrime` applies. -/
theorem flat_localizedModule_nonZeroSMulDivisors_closedFibre
    (hflat : ∀ p : Ideal S, ∀ _ : p.IsPrime,
      p ∈ assStacks S (N ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N))) →
        Module.Flat R (LocalizedModule p.primeCompl N)) :
    Module.Flat R (LocalizedModule
      (nonZeroSMulDivisors S
        (N ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N)))) N) := by
  refine Module.flat_localizedModule_of_forall_flat_atPrime ?_
  intro q hq hqle
  have : q.IsPrime := hq
  have hdis : Disjoint
      ((nonZeroSMulDivisors S
        (N ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N))) :
          Submonoid S) : Set S) ((q : Ideal S) : Set S) :=
    Set.disjoint_left.mpr fun _ hx hxq => hqle hx hxq
  have hQ : (Ideal.map (algebraMap S (Localization
      (nonZeroSMulDivisors S
        (N ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N)))))) q).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ _ q hq hdis
  have hmem : q ∈ Set.range (fun Q : PrimeSpectrum (Localization
      (nonZeroSMulDivisors S
        (N ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N))))) =>
      Q.asIdeal.under S) :=
    ⟨⟨_, hQ⟩, IsLocalization.under_map_of_isPrime_disjoint _ _ hq hdis⟩
  rw [UniversalInjectivity.range_under_localization_nonZeroSMulDivisors
    (R := R) (S := S) (N := N)] at hmem
  obtain ⟨p, hp, hqp⟩ := hmem.2
  have : p.IsPrime := hp.1
  exact Module.Flat.localizedModule_primeCompl_of_le hqp (hflat p hp.1 hp)

end Stacks.Flatness

end
