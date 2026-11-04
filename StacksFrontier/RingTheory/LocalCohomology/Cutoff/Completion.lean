module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.Catenary.Basic
public import StacksFrontier.RingTheory.Depth.Dimension
public import StacksFrontier.RingTheory.Equidimensional.FlatLocal
public import StacksFrontier.RingTheory.LocalCohomology.CutoffCompletion
public import StacksFrontier.RingTheory.LocalCohomology.FinitenessCutoff

/-!
# The local cohomology cutoff after completion

For a universally catenary Noetherian local ring `A` and a finite `A`-module `M`, passing to the
`m`-adic completion cannot increase the local cohomology finiteness cutoff
`s_{A,I}(M)` of Stacks 0BJR: the cutoff of `M̂` over `Â` with respect to the extended ideal
`I Â` is at most `s_{A,I}(M)`.

The proof compares the two cutoffs pair of primes by pair of primes. Given an admissible pair
`𝔭' ⊆ 𝔮'` of primes of `Â`, one produces an admissible pair `𝔭 ⊆ 𝔮` downstairs by contracting,
and `Stacks.LocalCohomology.pairwiseCutoffValue_eq_under_completion` expresses the summand of
`𝔭', 𝔮'` in terms of that of `𝔭, 𝔮` together with correction terms coming from the two local
formal fibres. Choosing `𝔭'` and `𝔮'` minimal over the extensions of `𝔭` and `𝔮` makes every
correction term vanish, so the two summands agree.

## Main results

* `Stacks.LocalCohomology.localCohomologyCutoff_adicCompletion_le` — completion does not increase
  the cutoff.

## Implementation notes

The completed ideal is the extension of `I` along the canonical map to the maximal-ideal-adic
completion, and the completed module is Mathlib's `AdicCompletion` of the module. For a finite
module over a Noetherian ring the latter is the base change `Â ⊗[A] M`, which is the form the
pairwise comparison is stated in; `FormalGlueing.adicCompletionTensorEquiv` is that
identification.

## References

* [Stacks Project, Tag 0BJT](https://stacks.math.columbia.edu/tag/0BJT)
-/

@[expose] public section

namespace Stacks.LocalCohomology

universe u v

open scoped TensorProduct

/-- The local cohomology cutoff does not decrease along a linear equivalence of modules. -/
private lemma localCohomologyCutoff_le_of_linearEquiv
    (R : Type*) [CommRing R] (J : Ideal R) {N N' : Type*}
    [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N'] (e : N ≃ₗ[R] N') :
    localCohomologyCutoff R J N ≤ localCohomologyCutoff R J N' := by
  rw [le_localCohomologyCutoff_iff]
  intro p q hp hq hpq
  rw [← Module.depth_eq_depth_of_linearEquiv _ (localizedEquiv p.asIdeal.primeCompl e)]
  exact localCohomologyCutoff_le R J N p q hp hq hpq

/-- The local cohomology cutoff is invariant under a linear equivalence of modules. -/
private lemma localCohomologyCutoff_eq_of_linearEquiv
    (R : Type*) [CommRing R] (J : Ideal R) {N N' : Type*}
    [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N'] (e : N ≃ₗ[R] N') :
    localCohomologyCutoff R J N = localCohomologyCutoff R J N' :=
  (localCohomologyCutoff_le_of_linearEquiv R J e).antisymm
    (localCohomologyCutoff_le_of_linearEquiv R J e.symm)

/-- A prime minimal over `J` becomes a height-zero prime in `R ⧸ J`. -/
private alias height_map_quotient_eq_zero_of_mem_minimalPrimes :=
  Stacks.KrullDimension.FibreHeight.height_map_quotient_eq_zero_of_mem_minimalPrimes

/-- If `P` is minimal over the extension of `J` to `S`, then the maximal ideal of `S` localized
at `P` is minimal over the extension of `J` to that localization. -/
private lemma minimalPrimes_map_to_localization {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (J : Ideal R) (P : Ideal S) [P.IsPrime]
    (h : P ∈ (J.map (algebraMap R S)).minimalPrimes) :
    IsLocalRing.maximalIdeal (Localization.AtPrime P) ∈
      (J.map (algebraMap R (Localization.AtPrime P))).minimalPrimes := by
  have h' : IsLocalRing.maximalIdeal (Localization.AtPrime P) ∈
      ((J.map (algebraMap R S)).map
        (algebraMap S (Localization.AtPrime P))).minimalPrimes := by
    rwa [IsLocalization.minimalPrimes_map P.primeCompl
      (Localization.AtPrime P), Set.mem_preimage,
      Localization.AtPrime.under_maximalIdeal]
  simpa only [Ideal.map_map, IsScalarTower.algebraMap_eq R S
    (Localization.AtPrime P)] using h'

/-- A Noetherian local ring whose maximal ideal has height zero has depth zero. -/
private lemma depth_self_eq_zero_of_maximalIdeal_height_eq_zero
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (h : (IsLocalRing.maximalIdeal R).height = 0) :
    Module.depth R (IsLocalRing.maximalIdeal R) R = 0 := by
  apply le_antisymm _ bot_le
  have hd := Module.depth_le_supportDim R (IsLocalRing.maximalIdeal R) R
    (by simpa using (IsLocalRing.maximalIdeal.isMaximal R).ne_top)
  rw [Module.supportDim_self_eq_ringKrullDim,
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h] at hd
  exact_mod_cast hd

/-- If the maximal ideal of a Noetherian local ring `R` is minimal over `J`, then its image in
`R ⧸ J` has depth zero on `R ⧸ J`. -/
private lemma depth_quotient_map_maximalIdeal_eq_zero {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] {J : Ideal R}
    (h : IsLocalRing.maximalIdeal R ∈ J.minimalPrimes) :
    Module.depth (R ⧸ J) ((IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk J)) (R ⧸ J) =
      0 := by
  have : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top h.1.2)
  have : IsLocalRing (R ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hmax : (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk J) =
      IsLocalRing.maximalIdeal (R ⧸ J) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  rw [hmax]
  exact depth_self_eq_zero_of_maximalIdeal_height_eq_zero _
    (hmax ▸ height_map_quotient_eq_zero_of_mem_minimalPrimes h)

/-- **Stacks 0BJT.** Completion at the maximal ideal cannot increase the local cohomology
finiteness cutoff of a finite module over a universally catenary Noetherian local ring. -/
@[stacks 0BJT "cutoff_completion_le"]
public theorem localCohomologyCutoff_adicCompletion_le
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hA : Ring.IsUniversallyCatenary A) :
    localCohomologyCutoff (AdicCompletion (IsLocalRing.maximalIdeal A) A)
        (I.map (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))
        (AdicCompletion (IsLocalRing.maximalIdeal A) M) ≤
      localCohomologyCutoff A I M := by
  let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
  have : Module.FaithfullyFlat A Ahat :=
    AdicCompletion.faithfullyFlat_of_le_ringJacobson _ (by
      rw [← Ideal.jacobson_bot]
      exact IsLocalRing.maximalIdeal_le_jacobson _)
  rw [← localCohomologyCutoff_eq_of_linearEquiv Ahat
    (I.map (algebraMap A Ahat))
    (FormalGlueing.adicCompletionTensorEquiv A (IsLocalRing.maximalIdeal A) M),
    le_localCohomologyCutoff_iff]
  intro p q hp hq hpq
  have : p.asIdeal.IsPrime := p.isPrime
  have : q.asIdeal.IsPrime := q.isPrime
  obtain ⟨Q₀, hQ₀, hQ₀q⟩ :=
    Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B := Ahat) q.asIdeal
  have : Q₀.IsPrime := hQ₀
  obtain ⟨Q, hQ, hQQ₀⟩ := Ideal.exists_minimalPrimes_le
    (J := Q₀) (Ideal.map_le_iff_le_comap.mpr hQ₀q.over.le)
  have : Q.IsPrime := hQ.1.1
  have hQq : Q.LiesOver q.asIdeal :=
    FlatLocalCatenary.liesOver_of_mem_minimalPrimes q.asIdeal Q hQ
  have hpQ : p.asIdeal.map (algebraMap A Ahat) ≤ Q :=
    Ideal.map_le_iff_le_comap.mpr (hpq.trans_eq hQq.over)
  obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le hpQ
  have : P.IsPrime := hP.1.1
  have hPp : P.LiesOver p.asIdeal :=
    FlatLocalCatenary.liesOver_of_mem_minimalPrimes p.asIdeal P hP
  let p' : PrimeSpectrum Ahat := ⟨P, inferInstance⟩
  let q' : PrimeSpectrum Ahat := ⟨Q, inferInstance⟩
  have hpcomap : PrimeSpectrum.comap (algebraMap A Ahat) p' = p :=
    PrimeSpectrum.ext hPp.over.symm
  have hqcomap : PrimeSpectrum.comap (algebraMap A Ahat) q' = q :=
    PrimeSpectrum.ext hQq.over.symm
  have hp' : ¬ I.map (algebraMap A Ahat) ≤ p'.asIdeal := fun h =>
    hp ((Ideal.map_le_iff_le_comap.mp h).trans_eq hPp.over.symm)
  have hq' : I.map (algebraMap A Ahat) ≤ q'.asIdeal :=
    (Ideal.map_mono hq).trans hQ.1.2
  refine (localCohomologyCutoff_le Ahat (I.map (algebraMap A Ahat))
    (Ahat ⊗[A] M) p' q' hp' hq' hPQ).trans_eq ?_
  rw [pairwiseCutoffValue_eq_under_completion A hA I M p' q' hp' hq' hPQ, hpcomap, hqcomap]
  simp only [p', q']
  have hPloc : IsLocalRing.maximalIdeal (Localization.AtPrime P) ∈
      (p.asIdeal.map (algebraMap A (Localization.AtPrime P))).minimalPrimes :=
    minimalPrimes_map_to_localization p.asIdeal P hP
  rw [height_map_quotient_eq_zero_of_mem_minimalPrimes
      (minimalPrimes_map_to_localization q.asIdeal Q hQ),
    height_map_quotient_eq_zero_of_mem_minimalPrimes hPloc,
    depth_quotient_map_maximalIdeal_eq_zero hPloc]
  simp

end Stacks.LocalCohomology

end
