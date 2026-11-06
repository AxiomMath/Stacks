module

import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Support
import StacksFrontier.RingTheory.AdicCompletion.QuotientCompletionMap

public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.FlatBaseChange
public import StacksFrontier.RingTheory.AnalyticallyUnramified.Defs
import StacksFrontier.RingTheory.AdicCompletion.AnalyticallyUnramified
public import StacksFrontier.RingTheory.Nagata.CompleteLocalRing
public import StacksFrontier.RingTheory.Kaehler.SmoothRingMapsInTheNoetherianCase

@[expose] public section

/-!
# Cutting a Noetherian local ring by a nonzerodivisor

Let `(R, 𝔪)` be a Noetherian local ring and let `x ∈ 𝔪` be a nonzerodivisor. If the module `R ⧸ xR`
has no embedded primes and every associated prime `𝔭` of `R ⧸ xR` has `R_𝔭` regular and is
analytically unramified, then `R` is analytically unramified.

The proof is the source's. Absence of embedded primes makes each associated prime `𝔭` of `R ⧸ xR`
minimal over `xR`, hence of height one by Krull's principal ideal theorem, so regularity of `R_𝔭`
makes its maximal ideal principal and `R_𝔭` a discrete valuation ring. Flat base change along
`R → R^` identifies `Ass_{R^}(R^ ⧸ xR^)` with the union of the sets `Ass_{R^}(R^ ⧸ 𝔭R^)`
(Stacks 0312), and each of those consists of primes `𝔮` with `(R^)_𝔮` a discrete valuation ring
(Stacks 032Z), in particular a domain (Stacks 00NP). So an element `y` of `R^` with `y² = 0` dies
in every `(R^)_𝔮` for `𝔮 ∈ Ass_{R^}(R^ ⧸ xR^)`, hence dies in `R^ ⧸ xR^` (Stacks 0311): `y = x y'`
with `(y')² = 0` because `x` stays a nonzerodivisor in `R^`. Iterating, `y ∈ ⋂ₙ xⁿ R^ ⊆ ⋂ₙ 𝔪^n R^`,
which is `0` by Krull's intersection theorem.

## Main results

* `Stacks.AnalyticallyUnramified.CuttingCriterion.solution`: the proof of
  `IsAnalyticallyUnramified.of_associatedPrimes_quotient_span_singleton`.

## Implementation notes

Reducedness of `R^` is deduced from the vanishing of square-zero elements alone
(`isReduced_of_forall_mul_self_eq_zero`), which is the form in which the source's argument produces
it; the reduction is the usual halving of the nilpotency exponent.

Analytic unramifiedness of `𝔭` in the sense of Stacks 032X — reducedness of `(R ⧸ 𝔭)^` — has to be
turned into reducedness of `R^ ⧸ 𝔭R^`, which is what Stacks 032Z consumes. That identification
`(R ⧸ I)^ = R^ ⧸ I R^`, exactness of completion (Stacks 00MB) in the shape the argument uses it, is
not in Mathlib; it is
`nonempty_ringEquiv_adicCompletion_quotient`, proved from the levelwise surjections
`R ⧸ 𝔪ⁿ → (R ⧸ I) ⧸ 𝔪_{R ⧸ I}ⁿ` in `StacksFrontier.RingTheory.AdicCompletion.QuotientCompletionMap`.

## References

* [Stacks Project, Tag 0330](https://stacks.math.columbia.edu/tag/0330)
* [Stacks Project, Tag 032Z](https://stacks.math.columbia.edu/tag/032Z)
* [Stacks Project, Tag 0312](https://stacks.math.columbia.edu/tag/0312)
* [Stacks Project, Tag 0311](https://stacks.math.columbia.edu/tag/0311)
* [Stacks Project, Tag 00NP](https://stacks.math.columbia.edu/tag/00NP)
* [Stacks Project, Tag 00IP](https://stacks.math.columbia.edu/tag/00IP)
-/

@[expose] public section

namespace Stacks.AnalyticallyUnramified.CuttingCriterion

open IsLocalRing TensorProduct

/-! ### Reducedness from square-zero elements -/

/-- A commutative ring in which every element with vanishing square is zero is reduced: halving the
nilpotency exponent reduces a nilpotent element to a square-zero one. -/
private theorem isReduced_of_forall_mul_self_eq_zero {A : Type*} [CommRing A]
    (h : ∀ y : A, y * y = 0 → y = 0) : IsReduced A := by
  constructor
  have key : ∀ n : ℕ, ∀ a : A, a ^ n = 0 → a = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      match n with
      | 0 =>
        intro a ha
        rw [pow_zero] at ha
        calc
          a = a * 1 := by ring
          _ = a * 0 := by rw [ha]
          _ = 0 := by ring
      | 1 =>
        intro a ha; simpa using ha
      | (m + 2) =>
        intro a ha
        have hm1 : (m + 3) / 2 < m + 2 := by omega
        have hsq : a ^ ((m + 3) / 2) * a ^ ((m + 3) / 2) = 0 := by
          rw [← pow_add,
            show (m + 3) / 2 + (m + 3) / 2 = (m + 2) + (2 * ((m + 3) / 2) - (m + 2)) by omega,
            pow_add, ha, zero_mul]
        exact ih _ hm1 a (h _ hsq)
  intro a ha
  obtain ⟨n, hn⟩ := ha
  exact key n a hn

/-! ### The completion of a quotient

The identification `(R ⧸ I)^ = R^ ⧸ I R^` is `nonempty_ringEquiv_adicCompletion_quotient`; it is
used here to read analytic unramifiedness of `R ⧸ I` off reducedness of `R^ ⧸ I R^`.
-/

/-- Analytic unramifiedness of `R ⧸ I` says that `R^ ⧸ I R^` is reduced. -/
private theorem analyticallyUnramifiedPrime_of_isAnalyticallyUnramified_quotient {R : Type*}
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R) [IsLocalRing (R ⧸ I)]
    (h : IsAnalyticallyUnramified (R ⧸ I)) : AnalyticallyUnramifiedPrime I := by
  obtain ⟨e⟩ := nonempty_ringEquiv_adicCompletion_quotient I
  have : IsReduced (AdicCompletion (maximalIdeal (R ⧸ I)) (R ⧸ I)) := h
  exact isReduced_of_injective e.symm e.symm.injective

/-! ### The associated primes of `R ⧸ xR` are height one, and their localizations are DVRs -/

/-- If `x` is a nonzerodivisor of a Noetherian ring `R` and `p` is a prime minimal over `xR` whose
localization is regular, then `R_p` is a discrete valuation ring. Krull's principal ideal theorem
pins the height of `p` at `1`, so regularity makes the maximal ideal of `R_p` principal, and it is
generated by a nonzerodivisor because `R_p` is a domain. -/
private theorem exists_isDiscreteValuationRing_localization_atPrime {R : Type*} [CommRing R]
    [IsNoetherianRing R] {x : R} (hx : x ∈ nonZeroDivisors R) (p : Ideal R) [p.IsPrime]
    (hpmin : p ∈ (Ideal.span {x}).minimalPrimes)
    (hreg : IsRegularLocalRing (Localization.AtPrime p)) :
    ∃ _ : IsDomain (Localization.AtPrime p), IsDiscreteValuationRing (Localization.AtPrime p) := by
  have := hreg
  have hdom : IsDomain (Localization.AtPrime p) :=
    IsRegularLocalRing.isDomain (Localization.AtPrime p)
  have hxp : x ∈ p := hpmin.1.2 (Ideal.mem_span_singleton_self x)
  -- the image of `x` in `R_p` is nonzero
  have hxA0 : algebraMap R (Localization.AtPrime p) x ≠ 0 := by
    intro h
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl _ x).mp h
    have hs0 : (s : R) = 0 := (mul_right_mem_nonZeroDivisors_eq_zero_iff hx).mp hs
    exact s.2 (hs0 ▸ p.zero_mem)
  have hmne : maximalIdeal (Localization.AtPrime p) ≠ ⊥ := by
    intro h
    refine hxA0 ?_
    have hmem : algebraMap R (Localization.AtPrime p) x ∈ maximalIdeal (Localization.AtPrime p) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff _ p x).mpr hxp
    rw [h] at hmem
    simpa using hmem
  -- Krull's principal ideal theorem: `p` has height at most one
  have hh : p.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {x}) p hpmin
  have hcast :
    ((maximalIdeal (Localization.AtPrime p)).spanFinrank : WithBot ℕ∞) =
      (p.height : WithBot ℕ∞) := by
    rw [hreg.spanFinrank_maximalIdeal,
      IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)]
  have hsf : (maximalIdeal (Localization.AtPrime p)).spanFinrank ≤ 1 := by
    have h1 : ((maximalIdeal (Localization.AtPrime p)).spanFinrank : ℕ∞) ≤ (1 : ℕ∞) := by
      have h2 : ((maximalIdeal (Localization.AtPrime p)).spanFinrank : ℕ∞) = p.height := by
        exact_mod_cast hcast
      rw [h2]; exact hh
    exact_mod_cast h1
  have hsf1 : (maximalIdeal (Localization.AtPrime p)).spanFinrank = 1 := by
    rcases Nat.lt_or_ge (maximalIdeal (Localization.AtPrime p)).spanFinrank 1 with h1 | h1
    · exfalso
      have h0 : (maximalIdeal (Localization.AtPrime p)).spanFinrank = 0 := by omega
      rw [←
        Submodule.FG.spanRank_eq_iff (maximalIdeal (Localization.AtPrime p)).fg_of_isNoetherianRing
          0] at h0
      exact hmne (Submodule.spanRank_eq_zero_iff_eq_bot.mp h0)
    · omega
  obtain ⟨t, ht⟩ := ((Submodule.spanFinrank_eq_one_iff _).mp hsf1).1
  have htne : t ≠ 0 := by
    intro h
    have hb : (Localization.AtPrime p ∙ (0 : Localization.AtPrime p)) = ⊥ :=
      Submodule.span_singleton_eq_bot.mpr rfl
    rw [h, hb] at ht
    exact hmne ht
  refine ⟨hdom, ?_⟩
  obtain ⟨_, hdvr⟩ :=
    l5_assemble (Localization.AtPrime p) t (mem_nonZeroDivisors_of_ne_zero htne) ht.symm hmne
  exact hdvr

/-! ### The associated primes of `R^ ⧸ xR^` -/

/-- Over a Noetherian ring the source's set of associated primes of Tag 00LA — the primes that
*are* the annihilator of an element — is Mathlib's `associatedPrimes`. Stacks 0312 states both of
its index sets in the source's spelling, while `LinearEquiv.AssociatedPrimes.eq` and Tag 032Z are
stated with `associatedPrimes`, so this is the translation between the two. -/
private theorem mem_setOf_colon_iff_mem_associatedPrimes {S X : Type*} [CommRing S]
    [IsNoetherianRing S] [AddCommGroup X] [Module S X] {q : Ideal S} :
    q ∈ {q' : Ideal S | q'.IsPrime ∧ ∃ w : X, (⊥ : Submodule S X).colon {w} = q'} ↔
      q ∈ associatedPrimes S X :=
  (and_congr_right fun _ => exists_congr fun _ => eq_comm).trans
    (Submodule.isAssociatedPrime_iff (N := (⊥ : Submodule S X)) (I := q)).symm

/-- Every associated prime `q` of the `R^`-module `R^ ⧸ xR^` has `(R^)_q` a domain. By flat base
change (Stacks 0312) `q` is an associated prime of `R^ ⧸ pR^` for some associated prime `p` of
`R ⧸ xR`; that `p` has `R_p` a discrete valuation ring and is analytically unramified, so
Stacks 032Z makes `(R^)_q` a discrete valuation ring, hence (Stacks 00NP) a domain. -/
private theorem exists_isDomain_localization_atPrime_of_mem_associatedPrimes {R : Type*}
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {x : R} (hx : x ∈ nonZeroDivisors R)
    (hemb : associatedPrimes R (R ⧸ Ideal.span {x}) ⊆ (Ideal.span {x}).minimalPrimes)
    (hp :
      ∀ (p : Ideal R) [p.IsPrime] [IsLocalRing (R ⧸ p)],
        p ∈ associatedPrimes R (R ⧸ Ideal.span {x}) →
          IsRegularLocalRing (Localization.AtPrime p) ∧ IsAnalyticallyUnramified (R ⧸ p))
    (q : Ideal (AdicCompletion (maximalIdeal R) R))
    (hq :
      q ∈
        associatedPrimes (AdicCompletion (maximalIdeal R) R)
          (AdicCompletion (maximalIdeal R) R ⧸
            Ideal.span {algebraMap R (AdicCompletion (maximalIdeal R) R) x})) :
    ∃ _ : q.IsPrime, IsDomain (Localization.AtPrime q) := by
  have hN := isNoetherianRing_adicCompletion R
  have hflat : Module.Flat R (AdicCompletion (maximalIdeal R) R) :=
    AdicCompletion.flat_of_isNoetherian (maximalIdeal R)
  -- identify `R^ ⧸ xR^` with `R^ ⊗_R (R ⧸ xR)`
  have hspan :
    Ideal.span {algebraMap R (AdicCompletion (maximalIdeal R) R) x} =
      (Ideal.span {x}).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
    rw [Ideal.map_span]
    simp
  have e :
    (AdicCompletion (maximalIdeal R) R ⧸
        Ideal.span {(algebraMap R (AdicCompletion (maximalIdeal R) R)) x}) ≃ₗ[AdicCompletion (maximalIdeal R) R]
      (AdicCompletion (maximalIdeal R) R) ⊗[R] (R ⧸ Ideal.span {x}) :=
    (Submodule.quotEquivOfEq _ _ hspan).trans
      (Ideal.qoutMapEquivTensorQout (AdicCompletion (maximalIdeal R) R))
  rw [LinearEquiv.AssociatedPrimes.eq e, ← mem_setOf_colon_iff_mem_associatedPrimes,
    (associatedPrimes.tensorProduct_of_flat (R := R) (S := AdicCompletion (maximalIdeal R) R) (M :=
          R ⧸ Ideal.span {x}) (N := AdicCompletion (maximalIdeal R) R)).2
      inferInstance] at hq
  obtain ⟨p, hpass, hq'⟩ := Set.mem_iUnion₂.mp hq
  -- rewrite the `p`-quotient as an ideal quotient
  have e2 :
    (AdicCompletion (maximalIdeal R) R ⧸
        ((p.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) •
          (⊤ :
            Submodule (AdicCompletion (maximalIdeal R) R)
              (AdicCompletion (maximalIdeal R) R)))) ≃ₗ[AdicCompletion (maximalIdeal R) R]
      (AdicCompletion (maximalIdeal R) R ⧸
        p.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) :=
    Submodule.quotEquivOfEq _ _ (by simp [smul_eq_mul])
  rw [mem_setOf_colon_iff_mem_associatedPrimes, LinearEquiv.AssociatedPrimes.eq e2] at hq'
  -- unpack the hypotheses at `p`
  have hpp : p.IsPrime := hpass.1
  have hpne : p ≠ ⊤ := hpp.ne_top
  have hploc : IsLocalRing (R ⧸ p) := isLocalRing_quotient hpne
  obtain ⟨hreg, hunr⟩ := hp p hpass
  obtain ⟨hdomp, hdvrp⟩ :=
    exists_isDiscreteValuationRing_localization_atPrime hx p (hemb hpass) hreg
  have := hdomp
  have hAU : AnalyticallyUnramifiedPrime p :=
    analyticallyUnramifiedPrime_of_isAnalyticallyUnramified_quotient p hunr
  obtain ⟨hqp, hqdom, _⟩ := exists_isDiscreteValuationRing_atPrime_of_analyticallyUnramified p hdvrp
    hAU q hq'
  exact ⟨hqp, hqdom⟩

/-! ### The divisibility step -/

/-- A square-zero element of `R^` lies in `xR^`: it dies in `(R^)_q` for every associated prime `q`
of `R^ ⧸ xR^`, those localizations being domains, hence dies in `R^ ⧸ xR^` by Stacks 0311. -/
private theorem mem_span_of_mul_self_eq_zero {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {x : R} (hx : x ∈ nonZeroDivisors R)
    (hemb : associatedPrimes R (R ⧸ Ideal.span {x}) ⊆ (Ideal.span {x}).minimalPrimes)
    (hp :
      ∀ (p : Ideal R) [p.IsPrime] [IsLocalRing (R ⧸ p)],
        p ∈ associatedPrimes R (R ⧸ Ideal.span {x}) →
          IsRegularLocalRing (Localization.AtPrime p) ∧ IsAnalyticallyUnramified (R ⧸ p))
    (y : AdicCompletion (maximalIdeal R) R) (hy : y * y = 0) :
    y ∈ Ideal.span {algebraMap R (AdicCompletion (maximalIdeal R) R) x} := by
  have hN := isNoetherianRing_adicCompletion R
  have hz :
    (assMap (AdicCompletion (maximalIdeal R) R)
          (AdicCompletion (maximalIdeal R) R ⧸
            Ideal.span {algebraMap R (AdicCompletion (maximalIdeal R) R) x}))
        (Ideal.Quotient.mk _ y) =
      0 := by
    funext qq
    obtain ⟨q, hq⟩ := qq
    obtain ⟨hqp, hqdom⟩ :=
      exists_isDomain_localization_atPrime_of_mem_associatedPrimes hx hemb hp q hq
    have := hqp
    have := hqdom
    have h0 : algebraMap (AdicCompletion (maximalIdeal R) R) (Localization.AtPrime q) y = 0 := by
      have hsq :
        (algebraMap (AdicCompletion (maximalIdeal R) R) (Localization.AtPrime q) y) *
            (algebraMap (AdicCompletion (maximalIdeal R) R) (Localization.AtPrime q) y) =
          0 := by
        rw [← map_mul, hy, map_zero]
      exact mul_self_eq_zero.mp hsq
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl _ y).mp h0
    simp only [assMap, LinearMap.pi_apply, LocalizedModule.mkLinearMap_apply, Pi.zero_apply]
    rw [show
        (0 :
            LocalizedModule q.primeCompl
              (AdicCompletion (maximalIdeal R) R ⧸
                Ideal.span {algebraMap R (AdicCompletion (maximalIdeal R) R) x})) =
          LocalizedModule.mk 0 1
        from (LocalizedModule.zero_mk 1).symm,
      LocalizedModule.mk_eq]
    refine ⟨s, ?_⟩
    have hsy :
      (s : AdicCompletion (maximalIdeal R) R) •
          (Ideal.Quotient.mk (Ideal.span {algebraMap R (AdicCompletion (maximalIdeal R) R) x}) y) =
        0 := by
      have hkey :
        (s : AdicCompletion (maximalIdeal R) R) •
            (Ideal.Quotient.mk (Ideal.span {algebraMap R (AdicCompletion (maximalIdeal R) R) x})
              y) =
          Ideal.Quotient.mk (Ideal.span {algebraMap R (AdicCompletion (maximalIdeal R) R) x})
            ((s : AdicCompletion (maximalIdeal R) R) * y) :=
        rfl
      rw [hkey, hs, map_zero]
    simp only [one_smul, smul_zero]
    exact hsy
  have hker :=
    zero_at_ass_zero (AdicCompletion (maximalIdeal R) R)
      (AdicCompletion (maximalIdeal R) R ⧸
        Ideal.span {algebraMap R (AdicCompletion (maximalIdeal R) R) x})
  have hy0 :
    (Ideal.Quotient.mk (Ideal.span {algebraMap R (AdicCompletion (maximalIdeal R) R) x}) y) = 0 :=
    hker (by rw [hz, map_zero])
  exact (Ideal.Quotient.eq_zero_iff_mem).mp hy0

/-! ### The main result -/

/-- **Stacks Tag 0330.** -/
public theorem solution {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {x : R}
    (hx : x ∈ nonZeroDivisors R) (hxm : x ∈ maximalIdeal R)
    (hemb : associatedPrimes R (R ⧸ Ideal.span {x}) ⊆ (Ideal.span {x}).minimalPrimes)
    (hp :
      ∀ (p : Ideal R) [p.IsPrime] [IsLocalRing (R ⧸ p)],
        p ∈ associatedPrimes R (R ⧸ Ideal.span {x}) →
          IsRegularLocalRing (Localization.AtPrime p) ∧ IsAnalyticallyUnramified (R ⧸ p)) :
    IsAnalyticallyUnramified R := by
  have hN := isNoetherianRing_adicCompletion R
  have hflat : Module.Flat R (AdicCompletion (maximalIdeal R) R) :=
    AdicCompletion.flat_of_isNoetherian (maximalIdeal R)
  have hx' :
    algebraMap R (AdicCompletion (maximalIdeal R) R) x ∈
      nonZeroDivisors (AdicCompletion (maximalIdeal R) R) :=
    algebraMap_mem_nonZeroDivisors_of_flat hx
  have hxm' :
    algebraMap R (AdicCompletion (maximalIdeal R) R) x ∈
      maximalIdeal (AdicCompletion (maximalIdeal R) R) := by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.mem_map_of_mem _ hxm
  show IsReduced (AdicCompletion (maximalIdeal R) R)
  refine isReduced_of_forall_mul_self_eq_zero ?_
  -- the divisibility step, with the square-zero condition carried along
  have core :
    ∀ y : AdicCompletion (maximalIdeal R) R,
      y * y = 0 → ∃ z, y = algebraMap R (AdicCompletion (maximalIdeal R) R) x * z ∧ z * z = 0 := by
    intro y hy
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp (mem_span_of_mul_self_eq_zero hx hemb hp y hy)
    refine
      ⟨z, by
        rw [← hz]; ring, ?_⟩
    have h2 :
      (z * z) *
          (algebraMap R (AdicCompletion (maximalIdeal R) R) x *
            algebraMap R (AdicCompletion (maximalIdeal R) R) x) =
        0 := by
      rw [← hz] at hy; linear_combination hy
    have h3 := (mul_right_mem_nonZeroDivisors_eq_zero_iff (mul_mem hx' hx')).mp h2
    exact h3
  have hpow :
    ∀ (n : ℕ) (y : AdicCompletion (maximalIdeal R) R),
      y * y = 0 → ∃ z, y = algebraMap R (AdicCompletion (maximalIdeal R) R) x ^ n * z := by
    intro n
    induction n with
    | zero =>
      intro y _; exact ⟨y, by ring⟩
    | succ n ih =>
      intro y hy
      obtain ⟨w, hw, hw2⟩ := core y hy
      obtain ⟨z, hz⟩ := ih w hw2
      exact
        ⟨z, by
          rw [hw, hz]; ring⟩
  intro y hy
  have hmem : ∀ n : ℕ, y ∈ (maximalIdeal (AdicCompletion (maximalIdeal R) R)) ^ n := by
    intro n
    obtain ⟨z, hz⟩ := hpow n y hy
    rw [hz]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hxm' n)
  have hbot :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (AdicCompletion (maximalIdeal R) R))
      (maximalIdeal.isMaximal (AdicCompletion (maximalIdeal R) R)).ne_top
  have hy0 : y ∈ (⊥ : Ideal (AdicCompletion (maximalIdeal R) R)) := by
    rw [← hbot, Submodule.mem_iInf]
    exact hmem
  simpa using hy0

end Stacks.AnalyticallyUnramified.CuttingCriterion

end

/-!
# A cutting criterion for analytic unramifiedness

Let `(R, 𝔪)` be a Noetherian local ring and let `x ∈ 𝔪` be a nonzerodivisor. Cutting by `x`
reduces analytic unramifiedness of `R` to analytic unramifiedness in codimension one: if `R ⧸ xR`
has no embedded primes and every associated prime `𝔭` of the module `R ⧸ xR` is such that `R_𝔭` is
regular and `𝔭` is analytically unramified — that is, `R ⧸ 𝔭` has reduced completion — then `R`
itself is analytically unramified.

The mechanism is that a square-zero element of `R^` is divisible by `x` infinitely often. Absence
of embedded primes makes each associated prime `𝔭` of `R ⧸ xR` minimal over `xR`, hence of height
one, so that regularity of `R_𝔭` makes it a discrete valuation ring; analytic unramifiedness of
`𝔭` then makes `(R^)_𝔮` a discrete valuation ring for every `𝔮 ∈ Ass_{R^}(R^ ⧸ 𝔭R^)`
(Stacks 032Z). Flat base change along `R → R^` computes `Ass_{R^}(R^ ⧸ xR^)` as the union of these
sets (Stacks 0312), so a `y` with `y² = 0` dies in each `(R^)_𝔮` — those being domains — and
therefore dies in `R^ ⧸ xR^` (Stacks 0311). Writing `y = x y'` and cancelling the nonzerodivisor
`x` gives `(y')² = 0`, so the argument repeats and `y ∈ ⋂ₙ xⁿ R^ = 0` by the Krull intersection
theorem (Stacks 00IP).

## Main results

* `IsAnalyticallyUnramified.isReduced`: an analytically unramified Noetherian local ring is
  reduced, because `R → R^` is injective.
* `IsAnalyticallyUnramified.of_associatedPrimes_quotient_span_singleton`: the criterion above.

## Implementation notes

*The domain hypothesis is dropped.* The source assumes `R` a Noetherian local domain and `x ≠ 0`;
what its proof consumes of the two is exactly that `x` is a nonzerodivisor (used twice: `x` stays
a nonzerodivisor in `R^` by flatness, and `x` lies outside every minimal prime of `R`, which is
what makes a prime minimal over `xR` have height one). So the hypothesis here is
`x ∈ nonZeroDivisors R`, which on a domain is `x ≠ 0` (`mem_nonZeroDivisors_iff_ne_zero`) and
recovers the source's statement verbatim. Nothing else in the route sees `IsDomain R`; the
conclusion is a statement about the ring `R^`, not about a fraction field.

*No embedded primes.* Stacks has no predicate for this yet, and the condition is stated as
`associatedPrimes R (R ⧸ Ideal.span {x}) ⊆ (Ideal.span {x}).minimalPrimes`, i.e. every associated
prime of the module `R ⧸ xR` is a minimal prime over `xR`. Since `Supp(R ⧸ xR) = V(xR)`, that is
literally "every associated prime is a minimal point of the support", which for a finite module
over a Noetherian ring is equivalent to "no associated prime is embedded", i.e. to every
associated prime being minimal among the associated primes: minimality in `Ass` and minimality in
`Supp` pick out the same primes by Stacks 02CE. The `minimalPrimes` form is the one the source's
proof uses ("each `𝔭ᵢ` is a minimal prime over `(x)`") and the one a user can act on.

*Regularity and analytic unramifiedness at `𝔭`.* Both conditions on `𝔭` are packed into one
hypothesis quantified over primes rather than over the set `associatedPrimes R (R ⧸ xR)`, so that
`𝔭` carries the `IsPrime` instance that `Localization.AtPrime 𝔭` needs. Regularity is assumed for
the concrete `Localization.AtPrime 𝔭`, which is the *weakest* form of the hypothesis and hence
gives the strongest statement — regularity transfers along the isomorphism to any other
`IsLocalization.AtPrime` model. Following Stacks 032X, "`𝔭` is analytically unramified" is the
composite `IsAnalyticallyUnramified (R ⧸ 𝔭)`; this needs `IsLocalRing (R ⧸ 𝔭)`, which holds for
every prime of a local ring but is not a Mathlib instance, so it is an instance binder of the
hypothesis, as in Stacks 032Y.

Faithfulness. (1) No hypothesis is dead. `x ∈ 𝔪` is what the Krull intersection step needs, and
without it `x` may be a unit, making the hypotheses on `Ass(R ⧸ xR) = ∅` vacuous and the
conclusion false for any Noetherian local domain with non-reduced completion;
`x ∈ nonZeroDivisors R` is used in the two places listed above; absence of embedded primes is what
upgrades "`R_𝔭` regular" to "`R_𝔭` a discrete valuation ring" by pinning the height at one, which
is what Stacks 032Z consumes; regularity of `R_𝔭` and analytic unramifiedness of `𝔭` are the two
inputs of that lemma, applied once for each associated prime. (2) The scalars and base are the
source's: `Ass` is taken over `R` and of `R ⧸ xR` as an `R`-module, `𝔭` and `xR` are ideals of `R`,
and the completion in both the hypothesis and the conclusion is the adic completion of the ring
named at its own maximal ideal — `R ⧸ 𝔭` along `𝔪/𝔭` in the hypothesis, `R` along `𝔪` in the
conclusion — never a base change of one along the other. (3) The maps the source names are pinned,
not merely asserted to exist: the completion is `AdicCompletion (maximalIdeal ·) ·` inside
`IsAnalyticallyUnramified` rather than an unnamed complete separated receiver, and `R_𝔭` is the
localization at `𝔭` rather than some abstract regular local ring dominating `R`. (4) The
instantiation is not degenerate: `R = k[[t]]` with `x = t` satisfies every hypothesis — `t` is a
nonzerodivisor in `𝔪`, `Ass(k[[t]] ⧸ (t)) = {𝔪}` with `𝔪` minimal over `(t)`, `R_𝔪 = R` is
regular, and `R ⧸ 𝔪 = k` is analytically unramified — and the conclusion, `k[[t]]` analytically
unramified, is true and not automatic, there being Noetherian local domains whose completion is
non-reduced.

## References

* [Stacks Project, Tag 0330](https://stacks.math.columbia.edu/tag/0330)
* [Stacks Project, Tag 032Z](https://stacks.math.columbia.edu/tag/032Z)
* [Stacks Project, Tag 032X](https://stacks.math.columbia.edu/tag/032X)

## Tags

analytically unramified, associated prime, embedded prime, regular local ring, completion
-/

@[expose] public section

open IsLocalRing

/-- **An analytically unramified Noetherian local ring is reduced.** The map `R → R^` is
injective, by Krull's intersection theorem, so a nilpotent of `R` is a nilpotent of `R^`. -/
public theorem IsAnalyticallyUnramified.isReduced {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (h : IsAnalyticallyUnramified R) : IsReduced R := by
  have h' : IsReduced (AdicCompletion (IsLocalRing.maximalIdeal R) R) := h
  have key :
    ∀ r : R,
      algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r =
        AdicCompletion.of (IsLocalRing.maximalIdeal R) R r :=
    fun r => by simp [AdicCompletion.algebraMap_apply]
  have hinj : Function.Injective (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) :=
    fun a b hab => AdicCompletion.of_injective _ _ (by rwa [← key, ← key])
  refine ⟨fun x hx => hinj ?_⟩
  rw [map_zero]
  exact h'.eq_zero _ (hx.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)))

/-- **Stacks Tag 0330.** Let `(R, 𝔪)` be a Noetherian local ring and let `x ∈ 𝔪` be a
nonzerodivisor. If `R ⧸ xR` has no embedded primes — every associated prime of the module `R ⧸ xR`
is minimal over `xR` — and every associated prime `𝔭` of `R ⧸ xR` has `R_𝔭` regular and is
analytically unramified, then `R` is analytically unramified.

The source assumes `R` a domain and `x ≠ 0`; only `x ∈ nonZeroDivisors R` is used, and it is what
those two amount to. -/
@[stacks 0330 "The source's `R` a domain with `x ≠ 0` is generalized to `x` a nonzerodivisor, \
  which is all the proof uses; `R ⧸ xR` having no embedded primes is spelled as every associated \
  prime of `R ⧸ xR` being minimal over `xR`, there being no predicate for it in this library."]
public theorem IsAnalyticallyUnramified.of_associatedPrimes_quotient_span_singleton {R : Type*}
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {x : R} (hx : x ∈ nonZeroDivisors R)
    (hxm : x ∈ maximalIdeal R)
    (hemb : associatedPrimes R (R ⧸ Ideal.span {x}) ⊆ (Ideal.span {x}).minimalPrimes)
    (hp :
      ∀ (p : Ideal R) [p.IsPrime] [IsLocalRing (R ⧸ p)],
        p ∈ associatedPrimes R (R ⧸ Ideal.span {x}) →
          IsRegularLocalRing (Localization.AtPrime p) ∧ IsAnalyticallyUnramified (R ⧸ p)) :
    IsAnalyticallyUnramified R :=
  Stacks.AnalyticallyUnramified.CuttingCriterion.solution (x := x) hx hxm hemb hp

end
