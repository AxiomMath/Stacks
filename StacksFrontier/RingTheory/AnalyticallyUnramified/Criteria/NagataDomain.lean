module

import StacksFrontier.RingTheory.KrullDimension.IntegralExtension
import StacksFrontier.RingTheory.Nagata.QuasiFinite
import StacksFrontier.RingTheory.Serre.Defs

public import StacksFrontier.RingTheory.AnalyticallyUnramified.Criteria.CuttingByNonzerodivisor

@[expose] public section

/-!
# A Nagata local domain is analytically unramified

Let `(R, 𝔪)` be a local domain which is a Nagata ring. Then `R` is analytically unramified: its
completion `R^ = lim_n R ⧸ 𝔪ⁿ` is reduced. A Nagata ring is Noetherian by definition
(Tag 032R(2)), so the source's Noetherian hypothesis is absorbed rather than restated.

The proof is the source's induction on `dim R`. In dimension zero the maximal ideal is `⊥`, the
completion is then `R` itself (`IsAdicComplete.bot`), and `R`, being a domain, is reduced. For the
inductive step one first replaces `R` by the integral closure `S` of `R` in `Frac R`: it is a
/-- Reducedness passes to a subring: an injective ring map into a reduced ring. -/
private theorem isReduced_of_injective {A B : Type*} [CommRing A] [CommRing B] [IsReduced B]
    (f : A →+* B) (hf : Function.Injective f) : IsReduced A :=
  ⟨fun a ha => hf (by rw [map_zero]; exact IsReduced.eq_zero _ (ha.map f))⟩


finite `R`-module because `R` is N-2, it is again Nagata (Tag 032T), it is normal, and
`dim S = dim R` (Tag 00OK). Completion of `R` base changes to `S`: the ring `S ⊗[R] R^` is the
product of the completions of the local rings `S_𝔮` at the primes `𝔮` of `S` lying over `𝔪`
(Tag 07N9), and `R^` injects into that product because `R → S` is injective and `R^` is flat over
`R`. So it suffices that each `S_𝔮` — a normal Nagata local domain of dimension at most `dim R` —
be analytically unramified.

For a normal `R` and a nonzero `x ∈ 𝔪`, Tag 031T says that `R ⧸ xR` has no embedded primes and
that every associated prime `𝔭` of `R ⧸ xR` has height one. Height one makes `𝔭` minimal over `xR`
(a strictly smaller prime would be `⊥`, which does not contain `x`) and makes `R_𝔭` a
one-dimensional normal Noetherian local domain, hence a regular local ring (Tag 00PD). Moreover
`R ⧸ 𝔭` is a Nagata local domain (Tag 032T) of dimension smaller than `dim R`, hence analytically
unramified by the inductive hypothesis. Tag 0330 then concludes.

## Main results

* `Stacks.AnalyticallyUnramified.NagataDomain.solution`: the proof of
  `IsAnalyticallyUnramified.of_isNagataRing`.

## Implementation notes

The induction runs on a natural number `d` bounding `ringKrullDim R`, which exists because a
Noetherian local ring has finite Krull dimension (`instFiniteRingKrullDimOfIsLocalRing`). Its step
is split in two: `normalCase` treats a normal Nagata local domain of dimension at most `d + 1`
given the statement in dimension at most `d`, and `isAnalyticallyUnramified_of_forall_primesOver`
descends reducedness along `R → S` for an arbitrary finite extension `S` with `R → S` injective.

A Nagata ring is N-2 on its prime quotients, so N-2 for a Nagata *domain* `R` itself is only
available through the prime `⊥`: `isJapaneseRing_of_isNagataRing` transports
`IsJapaneseRing (R ⧸ ⊥)` along the isomorphism `R ⧸ ⊥ ≅ R`, by `isJapaneseRing_of_quasiFinite`.

The localization lemma `isNagata_of_isLocalization` (Tag 032U) is stated against `IsNagataRing`
of Definition 032R(2), so it applies with no bridging.

## References

* [Stacks Project, Tag 0331](https://stacks.math.columbia.edu/tag/0331)
* [Stacks Project, Tag 0330](https://stacks.math.columbia.edu/tag/0330)
* [Stacks Project, Tag 031T](https://stacks.math.columbia.edu/tag/031T)
* [Stacks Project, Tag 032R](https://stacks.math.columbia.edu/tag/032R)
* [Stacks Project, Tag 032T](https://stacks.math.columbia.edu/tag/032T)
* [Stacks Project, Tag 032U](https://stacks.math.columbia.edu/tag/032U)
* [Stacks Project, Tag 00OK](https://stacks.math.columbia.edu/tag/00OK)
* [Stacks Project, Tag 00PD](https://stacks.math.columbia.edu/tag/00PD)
* [Stacks Project, Tag 07N9](https://stacks.math.columbia.edu/tag/07N9)
-/

namespace Stacks.AnalyticallyUnramified.NagataDomain

universe u
open IsLocalRing TensorProduct

/-- A reduced local ring whose maximal ideal is `⊥` — a field, up to the reducedness already
assumed — is its own completion, so its completion is reduced. -/
private theorem isReduced_adicCompletion_of_maximalIdeal_eq_bot (A : Type*) [CommRing A]
    [IsLocalRing A] [IsReduced A] (hm : maximalIdeal A = ⊥) :
    IsReduced (AdicCompletion (maximalIdeal A) A) := by
  rw [hm]
  have hcoe :
    (algebraMap A (AdicCompletion (⊥ : Ideal A) A) : A → AdicCompletion (⊥ : Ideal A) A) =
      AdicCompletion.of (⊥ : Ideal A) A := by
    funext r
    simp [AdicCompletion.algebraMap_apply]
  have hbij : Function.Bijective (algebraMap A (AdicCompletion (⊥ : Ideal A) A)) := by
    rw [hcoe]
    exact (AdicCompletion.ofLinearEquiv (⊥ : Ideal A) A).bijective
  refine ⟨fun y hy => ?_⟩
  obtain ⟨a, rfl⟩ := hbij.surjective y
  obtain ⟨n, hn⟩ := hy
  rw [← map_pow] at hn
  have han : a ^ n = 0 := hbij.injective (by rw [hn, map_zero])
  rw [IsReduced.eq_zero a ⟨n, han⟩, map_zero]

/-- **A Nagata domain is N-2.** `IsNagataRing R` gives N-2 for the quotients `R ⧸ 𝔭`; at `𝔭 = ⊥`
that is N-2 for `R` itself, transported along the isomorphism `R ⧸ ⊥ ≅ R`. -/
private theorem isJapaneseRing_of_isNagataRing (R : Type u) [CommRing R] [IsDomain R]
    (hR : IsNagataRing R) : IsJapaneseRing R := by
  have : IsNoetherianRing R := hR.1
  have : (⊥ : Ideal R).IsPrime := Ideal.isPrime_bot
  have hJ : IsJapaneseRing (R ⧸ (⊥ : Ideal R)) := hR.2 ⊥
  have : IsDomain (R ⧸ (⊥ : Ideal R)) := Ideal.Quotient.isDomain _
  have hinj : Function.Injective (Ideal.Quotient.mk (⊥ : Ideal R)) := by
    intro a b hab
    simpa [sub_eq_zero] using Ideal.Quotient.eq.mp hab
  let e : R ≃+* (R ⧸ (⊥ : Ideal R)) := RingEquiv.ofBijective _ ⟨hinj, Ideal.Quotient.mk_surjective⟩
  let _ : Algebra (R ⧸ (⊥ : Ideal R)) R := (e.symm : (R ⧸ (⊥ : Ideal R)) →+* R).toAlgebra
  have hmap : ∀ y : R ⧸ (⊥ : Ideal R), algebraMap (R ⧸ (⊥ : Ideal R)) R y = e.symm y := fun y =>
    congrFun (congrArg _ (RingHom.algebraMap_toAlgebra _)) y
  have : Module.Finite (R ⧸ (⊥ : Ideal R)) R := by
    refine Module.Finite.of_surjective (Algebra.linearMap (R ⧸ (⊥ : Ideal R)) R) ?_
    intro r
    exact ⟨e r, by simp [Algebra.linearMap_apply, hmap]⟩
  have : FaithfulSMul (R ⧸ (⊥ : Ideal R)) R :=
    (faithfulSMul_iff_algebraMap_injective (R ⧸ (⊥ : Ideal R)) R).mpr fun a b hab =>
      e.symm.injective (by rwa [← hmap, ← hmap])
  have := Module.Finite.finiteType (R := R ⧸ (⊥ : Ideal R)) R
  exact isJapaneseRing_of_quasiFinite hJ

/-- An associated prime of `A ⧸ I` contains `I`. -/
theorem le_of_mem_associatedPrimes {A : Type*} [CommRing A] {I : Ideal A} {p : Ideal A}
    (hp : p ∈ associatedPrimes A (A ⧸ I)) : I ≤ p := by
  refine le_trans ?_ (IsAssociatedPrime.annihilator_le hp)
  rw [Submodule.le_annihilator_iff, eq_bot_iff]
  refine (Submodule.smul_le (R := A) (A := A) (M := A ⧸ I)).mpr fun a ha m _ => ?_
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [Submodule.mem_bot, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (I.mul_mem_right w ha)

/-- In a domain, a prime of height one containing a nonzero element `x` is minimal over `xA`: a
strictly smaller prime would have height zero, hence be `⊥`, which does not contain `x`. -/
theorem mem_minimalPrimes_of_height_eq_one {A : Type*} [CommRing A] [IsDomain A] {x : A}
    (hx : x ≠ 0) {p : Ideal A} [p.IsPrime] (hxp : x ∈ p) (hp : p.height = 1) :
    p ∈ (Ideal.span {x}).minimalPrimes := by
  refine ⟨⟨inferInstance, by rwa [Ideal.span_le, Set.singleton_subset_iff]⟩, ?_⟩
  rintro q ⟨hq, hxq⟩ hqp
  by_contra hnle
  have : q.IsPrime := hq
  have : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
  have hlt : q < p := lt_of_le_of_ne hqp fun h => hnle (le_of_eq h.symm)
  have hbq : (⊥ : Ideal A) < q := by
    refine lt_of_le_of_ne bot_le fun h => hx ?_
    have hxq' : x ∈ q := hxq (Ideal.mem_span_singleton_self x)
    rw [← h] at hxq'
    simpa using hxq'
  have h1 : (1 : ℕ∞) ≤ q.height := by
    refine le_trans ?_ (Ideal.height_add_one_le_of_lt_of_isPrime hbq)
    simp
  have h2 : q.height + 1 ≤ p.height := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  rw [hp] at h2
  have h3 : (1 : ℕ∞) + 1 ≤ q.height + 1 := by gcongr
  exact absurd (le_trans h3 h2) (by decide)

/-- **The normal case.** A normal Nagata local domain of dimension at most `d + 1` is analytically
unramified, given the statement for Nagata local domains of dimension at most `d`. This is the
source's application of Tag 0330 to a nonzero `x ∈ 𝔪`, with Tag 031T supplying the associated
primes of `A ⧸ xA`, Tag 00PD their regularity and Tag 032T the Nagata property of `A ⧸ 𝔭`. -/
private theorem normalCase (d : ℕ)
    (IH :
      ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsDomain B],
        IsNagataRing B → ringKrullDim B ≤ ((d : ℕ) : WithBot ℕ∞) → IsAnalyticallyUnramified B)
    (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A] [IsIntegrallyClosed A]
    (hA : IsNagataRing A) (hd : ringKrullDim A ≤ ((d : ℕ) : WithBot ℕ∞) + (1 : ℕ)) :
    IsAnalyticallyUnramified A := by
  have hN : IsNoetherianRing A := hA.1
  by_cases hm : maximalIdeal A = ⊥
  · exact isReduced_adicCompletion_of_maximalIdeal_eq_bot A hm
  obtain ⟨x, hxm, hx0⟩ := (Submodule.ne_bot_iff _).mp hm
  have hx : x ∈ nonZeroDivisors A := mem_nonZeroDivisors_of_ne_zero hx0
  have h031T :=
    (associatedPrimes_minimal_and_height_eq_one_and_iInf_localization_eq_bot (R := A)
          (FractionRing A)).1
      x hx0
  refine IsAnalyticallyUnramified.of_associatedPrimes_quotient_span_singleton hx hxm ?_ ?_
  · intro p hp
    have : p.IsPrime := hp.1
    exact
      mem_minimalPrimes_of_height_eq_one hx0
        (le_of_mem_associatedPrimes hp (Ideal.mem_span_singleton_self x)) (h031T p hp).2
  · intro p _ _ hp
    have hh : p.height = 1 := (h031T p hp).2
    constructor
    · have : IsIntegrallyClosed (Localization.AtPrime p) :=
        isIntegrallyClosed_of_isLocalization _ p.primeCompl p.primeCompl_le_nonZeroDivisors
      have hdim : ringKrullDim (Localization.AtPrime p) = 1 := by
        rw [IsLocalization.AtPrime.ringKrullDim_eq_height p, hh]
        rfl
      have h5 :
        IsNoetherianRing (Localization.AtPrime p) ∧
          IsLocalRing (Localization.AtPrime p) ∧
          IsDomain (Localization.AtPrime p) ∧
          IsIntegrallyClosed (Localization.AtPrime p) ∧
          ringKrullDim (Localization.AtPrime p) = 1 :=
        ⟨inferInstance, inferInstance, inferInstance, inferInstance, hdim⟩
      have h3 :
        IsRegularLocalRing (Localization.AtPrime p) ∧ ringKrullDim (Localization.AtPrime p) = 1 :=
        ((isDiscreteValuationRing_tfae (Localization.AtPrime p)).out 5 3).mp h5
      exact h3.1
    · have : IsDomain (A ⧸ p) := Ideal.Quotient.isDomain p
      have hdq : ringKrullDim (A ⧸ p) ≤ ((d : ℕ) : WithBot ℕ∞) := by
        have h1 : ringKrullDim (A ⧸ p) ≤ ringKrullDim (A ⧸ Ideal.span {x}) :=
          ringKrullDim_le_of_surjective (Ideal.Quotient.factor (le_of_mem_associatedPrimes hp))
            (Ideal.Quotient.factor_surjective _)
        have h2 : ringKrullDim (A ⧸ Ideal.span {x}) + 1 ≤ ringKrullDim A :=
          ringKrullDim_quotient_succ_le_of_nonZeroDivisor hx
        refine ENat.WithBot.add_le_add_natCast_right_iff (c := 1) |>.mp ?_
        calc
          ringKrullDim (A ⧸ p) + ((1 : ℕ) : WithBot ℕ∞) ≤
              ringKrullDim (A ⧸ Ideal.span {x}) + ((1 : ℕ) : WithBot ℕ∞) :=
            by gcongr
          _ ≤ ringKrullDim A := by simpa using h2
          _ ≤ ((d : ℕ) : WithBot ℕ∞) + ((1 : ℕ) : WithBot ℕ∞) := by simpa using hd
      exact IH (A ⧸ p) (isNagataRing_of_quasiFinite hA) hdq

/-- **Descent along a finite extension.** If `S` is a finite `R`-algebra with `R → S` injective and
the completion of every local ring of `S` at a prime over `𝔪` is reduced, then `R` is analytically
unramified: `R^` injects into `S ⊗[R] R^` by flatness of `R^`, and that ring is the product of
those completions by Tag 07N9. -/
private theorem isAnalyticallyUnramified_of_forall_primesOver (R S : Type u) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    [FaithfulSMul R S]
    (h :
      ∀ q : ((maximalIdeal R).primesOver S),
        IsReduced
          (AdicCompletion (maximalIdeal (Localization.AtPrime q.1)) (Localization.AtPrime q.1))) :
    IsAnalyticallyUnramified R := by
  have : IsLocalization.AtPrime R (maximalIdeal R) :=
    IsLocalization.of_le_isUnit fun _ hx => notMem_maximalIdeal.mp hx
  obtain ⟨e⟩ :=
    AdicCompletion.nonempty_algEquiv_pi_primesOver (S := S) (maximalIdeal R) R
      (fun q => Localization.AtPrime q.1)
  have : IsReduced (S ⊗[R] AdicCompletion (maximalIdeal R) R) :=
    isReduced_of_injective e.toAlgHom (by simpa using e.injective)
  have : Module.Flat R (AdicCompletion (maximalIdeal R) R) := AdicCompletion.flat_of_isNoetherian _
  have h1 :
    Function.Injective ((Algebra.linearMap R S).rTensor (AdicCompletion (maximalIdeal R) R)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (FaithfulSMul.algebraMap_injective R S)
  refine
    isReduced_of_injective
      (Algebra.TensorProduct.includeRight (R := R) (A := S) (B :=
          AdicCompletion (maximalIdeal R) R)).toRingHom
      ?_
  intro y z hyz
  refine (TensorProduct.lid R (AdicCompletion (maximalIdeal R) R)).symm.injective (h1 ?_)
  simp only [TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul, Algebra.linearMap_apply,
    map_one]
  simpa [Algebra.TensorProduct.includeRight_apply] using hyz

/-- The induction on the dimension: a Nagata local domain of dimension at most `d` is analytically
unramified. -/
private theorem main (d : ℕ) (R : Type u) [CommRing R] [IsLocalRing R] [IsDomain R]
    (hR : IsNagataRing R) (hd : ringKrullDim R ≤ ((d : ℕ) : WithBot ℕ∞)) :
    IsAnalyticallyUnramified R := by
  induction d generalizing R with
  | zero =>
    have : IsNoetherianRing R := hR.1
    have : Ring.KrullDimLE 0 R := Ring.krullDimLE_iff.mpr hd
    have : (⊥ : Ideal R).IsPrime := Ideal.isPrime_bot
    exact
      isReduced_adicCompletion_of_maximalIdeal_eq_bot R
        (Ring.KrullDimLE.eq_maximalIdeal_of_isPrime (⊥ : Ideal R)).symm
  | succ n ih =>
    have hN : IsNoetherianRing R := hR.1
    have hfin : Module.Finite R ↥(integralClosure R (FractionRing R)) :=
      (isJapaneseRing_of_isNagataRing R hR).finite (FractionRing R)
    have := Module.Finite.finiteType (R := R) ↥(integralClosure R (FractionRing R))
    have hSnag : IsNagataRing ↥(integralClosure R (FractionRing R)) :=
      isNagataRing_of_quasiFinite hR
    have : IsIntegrallyClosed ↥(integralClosure R (FractionRing R)) :=
      integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing R)
    have hdimS :
      ringKrullDim ↥(integralClosure R (FractionRing R)) ≤
        ((n : ℕ) : WithBot ℕ∞) + ((1 : ℕ) : WithBot ℕ∞) := by
      rw [← Algebra.IsIntegral.ringKrullDim_eq R ↥(integralClosure R (FractionRing R))]
      simpa using hd
    refine
      isAnalyticallyUnramified_of_forall_primesOver R ↥(integralClosure R (FractionRing R))
        fun q => ?_
    have : IsIntegrallyClosed (Localization.AtPrime q.1) :=
      isIntegrallyClosed_of_isLocalization _ q.1.primeCompl q.1.primeCompl_le_nonZeroDivisors
    have hq : IsNagataRing (Localization.AtPrime q.1) :=
      isNagata_of_isLocalization _ q.1.primeCompl _ hSnag
    have hdimq :
      ringKrullDim (Localization.AtPrime q.1) ≤
        ((n : ℕ) : WithBot ℕ∞) + ((1 : ℕ) : WithBot ℕ∞) := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height q.1]
      exact le_trans Ideal.height_le_ringKrullDim_of_isPrime hdimS
    exact normalCase n (fun C _ _ _ hC hdC => ih C hC hdC) (Localization.AtPrime q.1) hq hdimq

/-- **Stacks Tag 0331.** -/
public theorem solution {R : Type*} [CommRing R] [IsLocalRing R] [IsDomain R]
    (hR : IsNagataRing R) : IsAnalyticallyUnramified R := by
  have : IsNoetherianRing R := hR.1
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim R ≤ ((d : ℕ) : WithBot ℕ∞) := by
    have h1 : ringKrullDim R ≠ ⊤ := ringKrullDim_ne_top
    have h2 : ringKrullDim R ≠ ⊥ := ringKrullDim_ne_bot
    lift ringKrullDim R to ℕ∞ using h2 with y hy
    lift y to ℕ using (by simpa using h1) with n
    exact ⟨n, by simp⟩
  exact main d R hR hd

end Stacks.AnalyticallyUnramified.NagataDomain

/-- **Stacks Tag 0331.** A local ring `(R, 𝔪)` which is a domain and a Nagata ring is
analytically unramified: its completion `R^ = lim_n R ⧸ 𝔪ⁿ` is reduced.

The source also assumes `R` Noetherian; that is the first conjunct of `IsNagataRing R`. -/
@[stacks 0331 "Nagata is `IsNagataRing` of Definition 032R(2), whose first conjunct is \
  `IsNoetherianRing R`, so the source's Noetherian hypothesis is absorbed rather than restated; \
  analytically unramified is the predicate of Tag 032X, reducedness of the `𝔪`-adic completion."]
public theorem IsAnalyticallyUnramified.of_isNagataRing {R : Type*} [CommRing R] [IsLocalRing R]
    [IsDomain R] (hR : IsNagataRing R) : IsAnalyticallyUnramified R :=
  Stacks.AnalyticallyUnramified.NagataDomain.solution hR

end
