module

import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE
import StacksFrontier.RingTheory.IntegralClosure.Pi
public import StacksFrontier.RingTheory.LocalRing.FiniteModification
import StacksFrontier.RingTheory.Depth.Defs.Defs

@[expose] public section

universe u

/-!
# Serre's criterion for normality

Let `R` be a Noetherian ring. This file proves that `R` is a normal ring — every localization
`R_𝔭` at a prime is a domain integrally closed in its fraction field — if and only if `R` has
properties `(R_1)` and `(S_2)`.

## Main results

* `Stacks.Serre.NormalityCriterion.solution`: the proof of [StacksProject 031S].

## References

* [StacksProject 031S](https://stacks.math.columbia.edu/tag/031S)
-/

@[expose] public section

namespace Stacks.Serre.NormalityCriterion

open IsLocalRing RingTheory.Sequence Polynomial



/-! ### Generalities -/

/-- In a domain the zero ideal is a minimal prime. -/
private lemma bot_mem_minimalPrimes (S : Type u) [CommRing S] [IsDomain S] :
    (⊥ : Ideal S) ∈ minimalPrimes S :=
  ⟨⟨inferInstance, le_rfl⟩, fun _ _ _ => bot_le⟩

/-- A local domain whose maximal ideal vanishes is zero-dimensional. -/
private lemma ringKrullDim_eq_zero_of_maximalIdeal_eq_bot (S : Type u) [CommRing S] [IsDomain S]
    [IsLocalRing S] (h : maximalIdeal S = ⊥) : ringKrullDim S = 0 := by
  have hh : (maximalIdeal S).height = 0 :=
    Ideal.height_eq_zero_iff.2 (h ▸ bot_mem_minimalPrimes S)
  have := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := S)
  rw [hh] at this
  simpa using this.symm

/-- A zero-dimensional Noetherian local domain is a regular local ring. -/
@[ega "0 17.1.4" "(i)"]
private lemma isRegularLocalRing_of_ringKrullDim_eq_zero (S : Type u) [CommRing S]
    [IsNoetherianRing S] [IsLocalRing S] [IsDomain S] (h : ringKrullDim S = 0) :
    IsRegularLocalRing S := by
  have hh : (maximalIdeal S).height = 0 := by
    have := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := S)
    rw [h] at this
    exact_mod_cast this
  have hmin : maximalIdeal S ∈ minimalPrimes S := Ideal.height_eq_zero_iff.1 hh
  obtain ⟨-, hmindown⟩ := hmin
  have hm0 : maximalIdeal S = ⊥ :=
    le_antisymm (hmindown ⟨inferInstance, bot_le⟩ bot_le) bot_le
  refine ⟨?_⟩
  rw [hm0, Submodule.spanFinrank_bot, h]
  rfl

/-- A Noetherian local domain with nonzero maximal ideal has positive depth. -/
private lemma one_le_depth_of_maximalIdeal_ne_bot (S : Type u) [CommRing S]
    [IsLocalRing S] [IsDomain S] (h : maximalIdeal S ≠ ⊥) :
    1 ≤ Module.depth S (maximalIdeal S) S := by
  obtain ⟨x, hxm, hx0⟩ : ∃ x ∈ maximalIdeal S, x ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    exact h (le_antisymm (fun a ha => (Submodule.mem_bot S).2 (hcon a ha)) bot_le)
  have hxreg : IsSMulRegular S x := by
    simpa [IsSMulRegular, Function.Injective] using
      fun a b (hab : x * a = x * b) => mul_left_cancel₀ hx0 hab
  have : Nontrivial (QuotSMulTop x S) := nontrivial_quotSMulTop_of_mem_maximalIdeal S hxm
  have hreg : IsRegular S [x] := (isRegular_cons_iff S x []).2 ⟨hxreg, IsRegular.nil S _⟩
  simpa using Module.le_depth_of_isRegular (maximalIdeal S) (M := S) (rs := [x])
    (by simpa using hxm) hreg

/-- The inequality `min {2, a} ≤ b` in `ℕ∞` from its two nontrivial instances. -/
private lemma min_two_le_of_forall {a b : ℕ∞} (h1 : 1 ≤ a → 1 ≤ b) (h2 : 2 ≤ a → 2 ≤ b) :
    min 2 a ≤ b := by
  rcases le_or_gt 2 a with hc | hc
  · rw [min_eq_left hc]
    exact h2 hc
  · rw [min_eq_right hc.le]
    rcases eq_or_ne a 0 with rfl | h0
    · exact zero_le
    · have ha1 : a = 1 := le_antisymm (ENat.lt_two_iff.1 hc) (Order.one_le_iff_ne_zero.2 h0)
      rw [ha1]
      exact h1 ha1.ge

/-- Assembling the two nontrivial cases of the inequality `min {2, dim R} ≤ depth R`. -/
private lemma min_two_le_depth (S : Type u) [CommRing S] [IsLocalRing S]
    (h1 : 1 ≤ ringKrullDim S → 1 ≤ Module.depth S (maximalIdeal S) S)
    (h2 : 2 ≤ ringKrullDim S → 2 ≤ Module.depth S (maximalIdeal S) S) :
    min 2 (ringKrullDim S) ≤ (Module.depth S (maximalIdeal S) S : WithBot ℕ∞) := by
  have hh : (((maximalIdeal S).height : ℕ∞) : WithBot ℕ∞) = ringKrullDim S :=
    IsLocalRing.maximalIdeal_height_eq_ringKrullDim
  have hmin : min (2 : WithBot ℕ∞) (((maximalIdeal S).height : ℕ∞) : WithBot ℕ∞)
      = ((min 2 (maximalIdeal S).height : ℕ∞) : WithBot ℕ∞) := by norm_cast
  rw [← hh, hmin]
  refine WithBot.coe_le_coe.2 (min_two_le_of_forall (fun hc => h1 ?_) (fun hc => h2 ?_))
  · rw [← hh]
    exact WithBot.coe_le_coe.2 hc
  · rw [← hh, show (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) from rfl]
    exact WithBot.coe_le_coe.2 hc

/-! ### Ruling out a small finite extension over a normal domain -/

/-- Let `S` be an integrally closed domain and `S ⊆ S'` a module-finite extension such that
some nonzero `x ∈ S`, acting regularly on `S'`, satisfies `x S' ⊆ S`. Then `S = S'`.

This is the step of [StacksProject 031S] that excludes case (4) of Lemma 0BHZ: the conductor
condition puts `S'` inside the fraction field of `S`, where integrality forces `S' = S`. -/
private lemma surjective_algebraMap_of_isIntegrallyClosed {S : Type u} [CommRing S] [IsDomain S]
    [IsIntegrallyClosed S] {S' : Type u} [CommRing S'] [Algebra S S'] [Module.Finite S S']
    (hinj : Function.Injective (algebraMap S S')) {x : S} (hx : x ≠ 0)
    (hxreg : IsSMulRegular S' x)
    (hcond : ∀ y : S', ∃ a : S, algebraMap S S' a = algebraMap S S' x * y) :
    Function.Surjective (algebraMap S S') := by
  have : Algebra.IsIntegral S S' := Algebra.IsIntegral.of_finite S S'
  intro y
  obtain ⟨a, ha⟩ := hcond y
  obtain ⟨p, hpm, hpe⟩ := Algebra.IsIntegral.isIntegral (R := S) y
  have key : Polynomial.eval a (p.scaleRoots x) = 0 := by
    apply hinj
    rw [map_zero, ← Polynomial.eval₂_at_apply (algebraMap S S') a, ha,
      Polynomial.scaleRoots_eval₂_mul, hpe, mul_zero]
  have hinjK : Function.Injective (algebraMap S (FractionRing S)) :=
    IsFractionRing.injective S (FractionRing S)
  have hxK : algebraMap S (FractionRing S) x ≠ 0 := fun h =>
    hx (hinjK (by simpa using h))
  set k : FractionRing S := algebraMap S (FractionRing S) a / algebraMap S (FractionRing S) x
    with hkdef
  have hk : algebraMap S (FractionRing S) x * k = algebraMap S (FractionRing S) a := by
    rw [hkdef, mul_div_cancel₀ _ hxK]
  have hint : IsIntegral S k := by
    refine ⟨p, hpm, ?_⟩
    have h1 : Polynomial.eval₂ (algebraMap S (FractionRing S))
        (algebraMap S (FractionRing S) x * k) (p.scaleRoots x) = 0 := by
      rw [hk, Polynomial.eval₂_at_apply, key, map_zero]
    rw [Polynomial.scaleRoots_eval₂_mul] at h1
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd h (pow_ne_zero _ hxK)
    · exact h
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have hab : x * b = a := hinjK (by rw [map_mul, hb, hk])
  refine ⟨b, hxreg ?_⟩
  show x • algebraMap S S' b = x • y
  rw [Algebra.smul_def, Algebra.smul_def, ← map_mul, hab, ha]

/-- A Noetherian local integrally closed domain of dimension at least `2` has depth at least
`2`: cases (1), (2) and (4) of Lemma 0BHZ are excluded. -/
@[ega "IV 5.8.6" "(ii), special case", sga "2 XI 3.11" "necessity: (ii)"]
private lemma two_le_depth_of_isIntegrallyClosed (S : Type u) [CommRing S] [IsNoetherianRing S]
    [IsLocalRing S] [IsDomain S] [IsIntegrallyClosed S] (hdim : 2 ≤ ringKrullDim S) :
    2 ≤ Module.depth S (maximalIdeal S) S := by
  obtain ⟨i, hi, -⟩ :=
    IsLocalRing.existsUnique_isArtinianRing_or_isRegularLocalRing_or_two_le_depth_or_exists_finite S
  have hmne : maximalIdeal S ≠ ⊥ := by
    intro h
    rw [ringKrullDim_eq_zero_of_maximalIdeal_eq_bot S h] at hdim
    norm_num at hdim
  fin_cases i
  · -- `S` is Artinian, hence zero-dimensional.
    have : Ring.KrullDimLE 0 S := (isArtinianRing_iff_krullDimLE_zero).1 hi
    rw [Ring.krullDimLE_iff] at this
    exact absurd (hdim.trans (by simpa using this)) (by simp)
  · -- `S` is regular of dimension `1`.
    rw [hi.2] at hdim
    simp at hdim
  · simpa using hi
  · -- The small finite extension of case (4) cannot exist.
    exfalso
    obtain ⟨S', _, _, hnt, hfin, hnbij, hass, n, hker, hcok⟩ := hi
    have hinj : Function.Injective (algebraMap S S') := by
      rcases Submodule.mul_eq_bot.1 hker with h | h
      · exact absurd (le_antisymm (fun a ha => IsReduced.eq_zero a
          ⟨n, (Submodule.mem_bot S).1 (h ▸ Ideal.pow_mem_pow ha n)⟩) bot_le) hmne
      · rw [RingHom.injective_iff_ker_eq_bot]
        exact h
    obtain ⟨x, hxm, hxreg⟩ : ∃ x ∈ maximalIdeal S, IsSMulRegular S' x :=
      (Ideal.exists_mem_isSMulRegular_iff_forall_associatedPrimes_not_le (maximalIdeal S) S'
        (associatedPrimes.finite S S')).2 fun _ hq hle =>
          hass (((maximalIdeal.isMaximal S).eq_of_le hq.1.ne_top hle) ▸ hq)
    have hx0 : x ≠ 0 := by
      rintro rfl
      obtain ⟨c, hc⟩ := exists_ne (0 : S')
      exact hc (hxreg (by simp))
    refine hnbij ⟨hinj, ?_⟩
    refine surjective_algebraMap_of_isIntegrallyClosed hinj (pow_ne_zero n hx0)
      (hxreg.pow n) fun y => ?_
    obtain ⟨a, ha⟩ := hcok (Submodule.smul_mem_smul (Ideal.pow_mem_pow hxm n) Submodule.mem_top)
    exact ⟨a, by simpa [Algebra.smul_def] using ha⟩

/-! ### Normal implies `(R_1)` and `(S_2)` -/

/-- The local ring at a prime of height at most `1` has dimension `0` or `1`. -/
private lemma ringKrullDim_atPrime_eq_zero_or_one {R : Type u} [CommRing R] (p : Ideal R)
    [p.IsPrime] (hp : p.height ≤ 1) :
    ringKrullDim (Localization.AtPrime p) = 0 ∨ ringKrullDim (Localization.AtPrime p) = 1 := by
  have hdim : ringKrullDim (Localization.AtPrime p) = (p.height : WithBot ℕ∞) :=
    IsLocalization.AtPrime.ringKrullDim_eq_height p _
  rcases eq_or_ne p.height 0 with h0 | h0
  · exact .inl (by rw [hdim, h0]; rfl)
  · exact .inr (by rw [hdim, le_antisymm hp (Order.one_le_iff_ne_zero.2 h0)]; rfl)

private lemma isRegularLocalRing_of_height_le_one {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] [IsDomain (Localization.AtPrime p)]
    [IsIntegrallyClosed (Localization.AtPrime p)] (hp : p.height ≤ 1) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  rcases ringKrullDim_atPrime_eq_zero_or_one p hp with hd0 | hd1
  · exact isRegularLocalRing_of_ringKrullDim_eq_zero _ hd0
  · have h5 : IsNoetherianRing (Localization.AtPrime p) ∧ IsLocalRing (Localization.AtPrime p) ∧
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) ∧
        ringKrullDim (Localization.AtPrime p) = 1 :=
      ⟨inferInstance, inferInstance, inferInstance, inferInstance, hd1⟩
    have hiff := (isDiscreteValuationRing_tfae (Localization.AtPrime p)).out 5 3
    exact (hiff.1 h5).1

/-- A normal Noetherian ring has properties `(R_1)` and `(S_2)`.

At a prime `𝔭` the local ring `S = R_𝔭` is a Noetherian local normal domain. If `dim S ≤ 1` it
is regular: for `dim S = 0` the maximal ideal is the minimal prime `(0)`, and for `dim S = 1` it
is a discrete valuation ring by Lemma 00PD. For `(S_2)` only the cases `dim S = 1` and
`dim S ≥ 2` are nontrivial: in the first a nonzero element of the maximal ideal is a
one-term regular sequence, and in the second Lemma 0BHZ leaves `depth S ≥ 2` as the only
alternative. -/
@[sga "2 XI 3.11" "necessity: (i) and (ii)"]
private lemma forward {R : Type u} [CommRing R] [IsNoetherianRing R]
    (h : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    (∀ (p : Ideal R) [p.IsPrime], p.height ≤ 1 →
        IsRegularLocalRing (Localization.AtPrime p)) ∧
      ∀ (p : Ideal R) [p.IsPrime],
        min 2 (ringKrullDim (Localization.AtPrime p)) ≤
          (Module.depth (Localization.AtPrime p)
            (IsLocalRing.maximalIdeal (Localization.AtPrime p))
            (Localization.AtPrime p) : WithBot ℕ∞) := by
  refine ⟨fun p _ hp => ?_, fun p _ => ?_⟩
  · obtain ⟨hd, hi⟩ := h p
    exact isRegularLocalRing_of_height_le_one p hp
  · obtain ⟨hd, hi⟩ := h p
    refine min_two_le_depth _ (fun h1 => ?_) (fun h2 => ?_)
    · refine one_le_depth_of_maximalIdeal_ne_bot _ fun hb => ?_
      rw [ringKrullDim_eq_zero_of_maximalIdeal_eq_bot _ hb] at h1
      norm_num at h1
    · exact two_le_depth_of_isIntegrallyClosed _ h2

/-! ### Regular local rings of dimension at most one -/

/-- A field is a normal domain. -/
private lemma isDomain_and_isIntegrallyClosed_of_isField (S : Type u) [CommRing S]
    (h : IsField S) : IsDomain S ∧ IsIntegrallyClosed S := by
  let _i : Field S := h.toField
  exact ⟨inferInstance, inferInstance⟩

/-- A regular local ring of dimension `0` is a field: its maximal ideal has span rank `0`. -/
private lemma isField_of_isRegularLocalRing_of_ringKrullDim_eq_zero (S : Type u) [CommRing S]
    [IsRegularLocalRing S] (hd : ringKrullDim S = 0) : IsField S := by
  have h2 : ((Submodule.spanFinrank (maximalIdeal S) : ℕ) : WithBot ℕ∞) = 0 :=
    (IsRegularLocalRing.spanFinrank_maximalIdeal (R := S)).trans hd
  have h3 : Submodule.spanFinrank (maximalIdeal S) = 0 := by exact_mod_cast h2
  have hfg : (maximalIdeal S).FG := IsNoetherian.noetherian _
  exact IsLocalRing.isField_iff_maximalIdeal_eq.2
    ((Submodule.spanFinrank_eq_zero_iff_eq_bot hfg).1 h3)

/-- Property `(R_1)` already gives normality at a prime of height at most `1`: the local ring is
a field when the height is `0` and a discrete valuation ring by Lemma 00PD when it is `1`. -/
private lemma normal_atPrime_of_height_le_one {R : Type u} [CommRing R]
    (p : Ideal R) [p.IsPrime] (h : IsRegularLocalRing (Localization.AtPrime p))
    (hp : p.height ≤ 1) :
    IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  rcases ringKrullDim_atPrime_eq_zero_or_one p hp with hd0 | hd1
  · exact isDomain_and_isIntegrallyClosed_of_isField _
      (isField_of_isRegularLocalRing_of_ringKrullDim_eq_zero _ hd0)
  · have hiff := (isDiscreteValuationRing_tfae (Localization.AtPrime p)).out 3 1
    obtain ⟨hdom, hdvr⟩ := hiff.1 ⟨h, hd1⟩
    exact ⟨hdom, inferInstance⟩

/-! ### Reducedness from reducedness away from the closed point -/

/-- The maximal ideal lies in the radical of an ideal contained in no other prime. -/
private lemma maximalIdeal_le_radical_of_forall_not_le {S : Type u} [CommRing S] [IsLocalRing S]
    (I : Ideal S) (h : ∀ q : Ideal S, q.IsPrime → q ≠ maximalIdeal S → ¬ I ≤ q) :
    maximalIdeal S ≤ I.radical := by
  rw [Ideal.radical_eq_sInf]
  refine le_sInf ?_
  rintro q ⟨hIq, hq⟩
  by_cases hqm : q = maximalIdeal S
  · exact hqm ▸ le_rfl
  · exact (h q hq hqm hIq).elim

/-- A Noetherian local ring is reduced as soon as its localizations at the non-maximal primes are
reduced and its maximal ideal contains a nonzerodivisor.

If `a` is nilpotent then `a` dies in every `S_𝔮` with `𝔮 ≠ 𝔪`, so no prime other than `𝔪`
contains the annihilator of `a`; hence `𝔪` is the radical of that annihilator, a power of `𝔪`
kills `a`, and the corresponding power of the nonzerodivisor forces `a = 0`. -/
private lemma isReduced_of_forall_isReduced_localization (S : Type u) [CommRing S]
    [IsNoetherianRing S] [IsLocalRing S]
    (ht : ∃ t ∈ maximalIdeal S, t ∈ nonZeroDivisors S)
    (h : ∀ q : Ideal S, ∀ _ : q.IsPrime, q ≠ maximalIdeal S →
      IsReduced (Localization.AtPrime q)) :
    IsReduced S := by
  refine ⟨fun a ha => ?_⟩
  by_contra hne
  set I : Ideal S := (Submodule.span S {a}).annihilator with hI
  have hmle : maximalIdeal S ≤ I.radical := by
    refine maximalIdeal_le_radical_of_forall_not_le I fun q hq hqm hIq => ?_
    have hred := h q hq hqm
    have h0 : algebraMap S (Localization.AtPrime q) a = 0 :=
      IsReduced.eq_zero _ (ha.map _)
    rw [IsLocalization.map_eq_zero_iff q.primeCompl] at h0
    obtain ⟨⟨s, hs⟩, hsa⟩ := h0
    refine hs (hIq ?_)
    rw [hI, Submodule.mem_annihilator_span_singleton]
    simpa [smul_eq_mul] using hsa
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hmle (IsNoetherian.noetherian _)
  obtain ⟨t, htm, ht'⟩ := ht
  have hta : a * t ^ n = 0 := by
    have hmem : t ^ n ∈ I := hn (Ideal.pow_mem_pow htm n)
    rw [hI, Submodule.mem_annihilator_span_singleton] at hmem
    simpa [smul_eq_mul, mul_comm] using hmem
  exact hne ((mem_nonZeroDivisors_iff.1 (pow_mem ht' n)).2 a hta)

/-- A positive depth produces a nonzerodivisor in the maximal ideal. -/
private lemma exists_mem_nonZeroDivisors_of_one_le_depth (S : Type u) [CommRing S]
    [IsLocalRing S] (h : 1 ≤ Module.depth S (maximalIdeal S) S) :
    ∃ t ∈ maximalIdeal S, t ∈ nonZeroDivisors S := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  rw [Module.depth] at h
  split at h
  · rename_i hm
    exact (maximalIdeal.isMaximal S).ne_top (by simpa using hm)
  · refine absurd h (not_le.2 (lt_of_le_of_lt (b := (0 : ℕ∞))
      (iSup₂_le fun rs hrs => ?_) zero_lt_one))
    rcases rs with _ | ⟨t, ts⟩
    · simp
    · exfalso
      obtain ⟨hmem, hreg⟩ := hrs
      have ht : IsSMulRegular S t := ((isRegular_cons_iff S t ts).1 hreg).1
      refine hcon t (hmem t (by simp)) (mem_nonZeroDivisors_iff.2 ⟨?_, ?_⟩)
      · intro x hx
        exact ht (by simpa [smul_eq_mul] using hx)
      · intro x hx
        exact ht (by simpa [smul_eq_mul, mul_comm] using hx)

/-! ### Bookkeeping in `ℕ∞` -/

/-- In `ℕ∞`, an element not below `1` is at least `2`. -/
private lemma two_le_of_not_le_one {a : ℕ∞} (h : ¬ a ≤ 1) : 2 ≤ a :=
  not_lt.1 fun hlt => h (ENat.lt_two_iff.1 hlt)

/-- Reading `(S_2)` at a prime of dimension at least `2` as `2 ≤ depth`. -/
private lemma two_le_depth_of_min_le (S : Type u) [CommRing S] [IsLocalRing S]
    (h : min 2 (ringKrullDim S) ≤ (Module.depth S (maximalIdeal S) S : WithBot ℕ∞))
    (hd : 2 ≤ ringKrullDim S) : 2 ≤ Module.depth S (maximalIdeal S) S := by
  rw [min_eq_left hd, show (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) from rfl] at h
  exact WithBot.coe_le_coe.1 h

/-! ### `(R_1)` and `(S_2)` imply normal -/

/-- Case (4) of Lemma 0BHZ is excluded by depth at least `2`, by the uniqueness in that lemma. -/
private lemma not_exists_finite_of_two_le_depth (S : Type u) [CommRing S] [IsNoetherianRing S]
    [IsLocalRing S] (hdep : 2 ≤ Module.depth S (maximalIdeal S) S)
    (S' : Type u) [CommRing S'] [Algebra S S'] (hnt : Nontrivial S') (hfin : Module.Finite S S')
    (hnbij : ¬ Function.Bijective (algebraMap S S'))
    (hass : maximalIdeal S ∉ associatedPrimes S S') (n : ℕ)
    (hker : maximalIdeal S ^ n * RingHom.ker (algebraMap S S') = ⊥)
    (hcok : maximalIdeal S ^ n • (⊤ : Submodule S S') ≤
      LinearMap.range (Algebra.linearMap S S')) : False := by
  obtain ⟨i, -, huniq⟩ :=
    IsLocalRing.existsUnique_isArtinianRing_or_isRegularLocalRing_or_two_le_depth_or_exists_finite S
  have h3 : (2 : Fin 4) = i := huniq 2 (by simpa using hdep)
  have h4 : (3 : Fin 4) = i := huniq 3
    ⟨S', inferInstance, inferInstance, hnt, hfin, hnbij, hass, n, hker, hcok⟩
  exact absurd (h3.trans h4.symm) (by decide)

/-- The primes of `R_𝔭` other than the maximal one are the primes `𝔮 < 𝔭` of `R`, and the
localization of `R_𝔭` at such a prime is `R_𝔮`.

This is the transfer of the inductive hypothesis from `R` to `R_𝔭` in the proof of
[StacksProject 031S]; the underlying identification is Mathlib's
`IsLocalization.localizationLocalizationAtPrimeIsoLocalization`, and `P ≠ 𝔪R_𝔭` becomes
`P ∩ R < 𝔭` because contraction along a localization map is injective on ideals
(`IsLocalization.map_under`) and carries the maximal ideal to `𝔭`. -/
private lemma normal_localization_atPrime_of_forall_lt {R : Type u} [CommRing R]
    [IsNoetherianRing R] (p : Ideal R) [p.IsPrime]
    (h : ∀ q : Ideal R, ∀ _ : q.IsPrime, q < p →
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) :
    ∀ P : Ideal (Localization.AtPrime p), ∀ _ : P.IsPrime,
      P ≠ maximalIdeal (Localization.AtPrime p) →
      IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P) := by
  intro P hP hPne
  have : (P.comap (algebraMap R (Localization.AtPrime p))).IsPrime := hP.comap _
  have hle : P.comap (algebraMap R (Localization.AtPrime p)) ≤ p := by
    have h1 : P ≤ maximalIdeal (Localization.AtPrime p) := IsLocalRing.le_maximalIdeal hP.ne_top
    have h2 : P.under R ≤ (maximalIdeal (Localization.AtPrime p)).under R := Ideal.comap_mono h1
    rwa [IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime p) p] at h2
  have hne : P.comap (algebraMap R (Localization.AtPrime p)) ≠ p := by
    intro hEq
    refine hPne ?_
    have h3 := IsLocalization.map_under p.primeCompl (Localization.AtPrime p) P
    rw [show P.under R = p from hEq, IsLocalization.AtPrime.map_eq_maximalIdeal] at h3
    exact h3.symm
  obtain ⟨hd, hi⟩ := h _ ‹_› (lt_of_le_of_ne hle hne)
  have e := IsLocalization.localizationLocalizationAtPrimeIsoLocalization (M := p.primeCompl) P
  exact ⟨MulEquiv.isDomain _ e.symm.toRingEquiv.toMulEquiv,
    IsIntegrallyClosed.of_equiv e.toRingEquiv⟩

/-! ### Conductors -/

/-- A finitely generated submodule all of whose elements die in a localization is annihilated by
a single element of the submonoid. -/
private lemma exists_mem_forall_mul_eq_zero_of_fg {S : Type u} [CommRing S] (W : Submonoid S)
    (A : Type u) [CommRing A] [Algebra S A] [IsLocalization W A] (I : Ideal S) (hI : I.FG)
    (h : ∀ c ∈ I, algebraMap S A c = 0) : ∃ s ∈ W, ∀ c ∈ I, s * c = 0 := by
  refine Submodule.fg_induction
    (motive := fun I _ => (∀ c ∈ I, algebraMap S A c = 0) → ∃ s ∈ W, ∀ c ∈ I, s * c = 0)
    (fun x hx => ?_) (fun N₁ N₂ h₁ h₂ ih₁ ih₂ hsup => ?_) I hI h
  · obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff W A x).1
      (hx x (Submodule.mem_span_singleton_self x))
    refine ⟨s, s.2, fun c hc => ?_⟩
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hc
    simp only [smul_eq_mul]
    linear_combination d * hs
  · obtain ⟨s₁, hs₁, hz₁⟩ := ih₁ fun c hc => hsup c (Submodule.mem_sup_left hc)
    obtain ⟨s₂, hs₂, hz₂⟩ := ih₂ fun c hc => hsup c (Submodule.mem_sup_right hc)
    refine ⟨s₁ * s₂, mul_mem hs₁ hs₂, fun c hc => ?_⟩
    obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := Submodule.mem_sup.1 hc
    linear_combination s₂ * hz₁ c₁ hc₁ + s₁ * hz₂ c₂ hc₂

/-- If every element of a finitely generated module is carried into a submodule by some power of
`s`, then one power of `s` carries the whole module into it. -/
private lemma exists_pow_smul_mem {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M]
    (T : Submodule S M) (s : S) (hfg : (⊤ : Submodule S M).FG)
    (h : ∀ y : M, ∃ n : ℕ, s ^ n • y ∈ T) : ∃ n : ℕ, ∀ y : M, s ^ n • y ∈ T := by
  classical
  obtain ⟨t, ht⟩ := hfg
  choose f hf using h
  refine ⟨t.sup f, fun y => ?_⟩
  have hle : (⊤ : Submodule S M) ≤ T.comap (LinearMap.lsmul S M (s ^ t.sup f)) := by
    rw [← ht, Submodule.span_le]
    intro z hz
    have hz' : s ^ t.sup f • z = s ^ (t.sup f - f z) • (s ^ f z • z) := by
      rw [smul_smul, ← pow_add, Nat.sub_add_cancel (Finset.le_sup (Finset.mem_coe.1 hz))]
    simpa [hz'] using T.smul_mem _ (hf z)
  simpa using hle (Submodule.mem_top (x := y))

/-- If `s x` lies in `S` then a power of `s` carries any element of `S[x]` into `S`. -/
private lemma exists_pow_mul_eq_algebraMap {S Q : Type*} [CommRing S] [CommRing Q] [Algebra S Q]
    {x : Q} {s a : S} (hsa : algebraMap S Q s * x = algebraMap S Q a) {y : Q}
    (hy : y ∈ Algebra.adjoin S ({x} : Set Q)) :
    ∃ (n : ℕ) (b : S), algebraMap S Q (s ^ n) * y = algebraMap S Q b := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
  obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).1 hy
  refine ⟨p.natDegree, Polynomial.eval a (p.scaleRoots s), ?_⟩
  rw [Polynomial.aeval_def, map_pow, ← Polynomial.eval₂_at_apply (algebraMap S Q) a, ← hsa,
    Polynomial.scaleRoots_eval₂_mul]

/-- The heart of (2) `⇒` (1) in [StacksProject 031S]. Let `S` be a Noetherian local ring of depth
at least `2`, let `Q` be a localization of `S` at its nonzerodivisors, and let `x ∈ Q` be integral
over `S` with conductor `(S : x)` contained in no prime other than `𝔪`. Then `x ∈ S`.

Otherwise `S' = S[x]` is a finite extension as in case (4) of Lemma 0BHZ: it is not an
isomorphism because `x ∉ S`, the map `S → S'` is injective because `S' ⊆ Q`, the maximal ideal is
not an associated prime of `S'` because a nonzerodivisor of `S` inside `𝔪` is invertible on `Q`,
and a power of `𝔪` annihilates `S'/S` because the conductor has radical `𝔪`. That contradicts
`depth(S) ≥ 2`. -/
private lemma exists_algebraMap_eq_of_conductor (S : Type u) [CommRing S] [IsNoetherianRing S]
    [IsLocalRing S] (Q : Type u) [CommRing Q] [Algebra S Q]
    [IsLocalization (nonZeroDivisors S) Q] (hdep : 2 ≤ Module.depth S (maximalIdeal S) S)
    {x : Q} (hxint : IsIntegral S x)
    (hcond : ∀ q : Ideal S, ∀ _ : q.IsPrime, q ≠ maximalIdeal S →
      ∃ s ∈ q.primeCompl, ∃ a : S, algebraMap S Q s * x = algebraMap S Q a) :
    ∃ c : S, algebraMap S Q c = x := by
  by_contra hcon
  simp only [not_exists] at hcon
  have hinjQ : Function.Injective (algebraMap S Q) := IsLocalization.injective Q le_rfl
  have hfin : Module.Finite S (Algebra.adjoin S ({x} : Set Q)) :=
    Algebra.finite_adjoin_simple_of_isIntegral hxint
  have hntQ : Nontrivial Q := hinjQ.nontrivial
  have hntS' : Nontrivial (Algebra.adjoin S ({x} : Set Q)) := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h7 := congrArg (fun z : Algebra.adjoin S ({x} : Set Q) => (z : Q)) h
    simp at h7
  have hcoe : ∀ c : S,
      ((algebraMap S (Algebra.adjoin S ({x} : Set Q)) c :
        Algebra.adjoin S ({x} : Set Q)) : Q) = algebraMap S Q c := fun c => rfl
  have hinj : Function.Injective (algebraMap S (Algebra.adjoin S ({x} : Set Q))) := fun c d hcd =>
    hinjQ (by rw [← hcoe, ← hcoe, hcd])
  have hnbij : ¬ Function.Bijective (algebraMap S (Algebra.adjoin S ({x} : Set Q))) := by
    intro hbij
    obtain ⟨c, hc⟩ := hbij.2 ⟨x, Algebra.self_mem_adjoin_singleton S x⟩
    exact hcon c (by rw [← hcoe c, hc])
  obtain ⟨t, htm, ht⟩ := exists_mem_nonZeroDivisors_of_one_le_depth S (le_trans (by norm_num) hdep)
  have htu : IsUnit (algebraMap S Q t) := IsLocalization.map_units Q ⟨t, ht⟩
  have hregt : ∀ y : Algebra.adjoin S ({x} : Set Q), t • y = 0 → y = 0 := by
    intro y hy
    have h1 : algebraMap S Q t * (y : Q) = 0 := by
      have h2 := congrArg (fun z : Algebra.adjoin S ({x} : Set Q) => (z : Q)) hy
      simpa [Algebra.smul_def, hcoe] using h2
    exact Subtype.ext (by simpa using htu.mul_right_eq_zero.1 h1)
  have hass : maximalIdeal S ∉ associatedPrimes S (Algebra.adjoin S ({x} : Set Q)) := by
    intro hmem
    obtain ⟨-, y, hy⟩ := Submodule.isAssociatedPrime_iff.1 hmem
    have hty : t • y = 0 := by
      have h3 := Submodule.mem_colon.1 (hy ▸ htm) y (Set.mem_singleton y)
      simpa using h3
    rw [hregt y hty] at hy
    rw [show ((⊥ : Submodule S (Algebra.adjoin S ({x} : Set Q))).colon
      {(0 : Algebra.adjoin S ({x} : Set Q))}) = ⊤ from by ext c; simp] at hy
    exact (maximalIdeal.isMaximal S).ne_top hy
  have hker : RingHom.ker (algebraMap S (Algebra.adjoin S ({x} : Set Q))) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).1 hinj
  have hrad : maximalIdeal S ≤
      ((LinearMap.range (Algebra.linearMap S (Algebra.adjoin S ({x} : Set Q)))).colon
        Set.univ).radical := by
    refine maximalIdeal_le_radical_of_forall_not_le _ fun q hq hqm hCq => ?_
    obtain ⟨s, hsq, a, hsa⟩ := hcond q hq hqm
    have hpt : ∀ y : Algebra.adjoin S ({x} : Set Q), ∃ n : ℕ,
        s ^ n • y ∈ LinearMap.range (Algebra.linearMap S (Algebra.adjoin S ({x} : Set Q))) := by
      intro y
      obtain ⟨m, b, hb⟩ := exists_pow_mul_eq_algebraMap hsa y.2
      refine ⟨m, ⟨b, Subtype.ext ?_⟩⟩
      simpa [Algebra.smul_def, hcoe] using hb.symm
    obtain ⟨n, hn⟩ := exists_pow_smul_mem _ s (Module.finite_def.1 hfin) hpt
    exact hsq (hq.mem_of_pow_mem n (hCq (Submodule.mem_colon.2 fun y _ => hn y)))
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  refine not_exists_finite_of_two_le_depth S hdep (Algebra.adjoin S ({x} : Set Q)) hntS'
    hfin hnbij hass N ?_ ?_
  · rw [hker, Ideal.mul_bot]
  · rw [Submodule.smul_le]
    intro c hc y _
    exact Submodule.mem_colon.1 (hN hc) y (Set.mem_univ y)

/-! ### Domainhood from depth two -/

/-- Over a Noetherian local ring `S` of depth at least `2` whose localizations at the non-maximal
primes are domains there is no decomposition `u v = 0` of a nonzerodivisor `u + v` into two
nonzero factors.

Indeed `e = u/(u + v)` is then an idempotent of the total ring of fractions `Q`: it is integral
over `S`; it does not lie in `S`, because an idempotent of a local ring is `0` or `1` while
`u ≠ 0 ≠ v`; and its conductor is contained in no prime `𝔮 ≠ 𝔪`, because in the domain `S_𝔮` one
of `u` and `v` dies and the element of `S ∖ 𝔮` witnessing that carries `e` into `S`. This
contradicts `Stacks.Serre.NormalityCriterion.exists_algebraMap_eq_of_conductor`. -/
private lemma false_of_mul_eq_zero_of_add_mem_nonZeroDivisors (S : Type u) [CommRing S]
    [IsNoetherianRing S] [IsLocalRing S] (Q : Type u) [CommRing Q] [Algebra S Q]
    [IsLocalization (nonZeroDivisors S) Q] (hdep : 2 ≤ Module.depth S (maximalIdeal S) S)
    (hloc : ∀ q : Ideal S, ∀ _ : q.IsPrime, q ≠ maximalIdeal S →
      IsDomain (Localization.AtPrime q))
    {u v : S} (hu : u ≠ 0) (hv : v ≠ 0) (huv0 : u * v = 0)
    (hnzd : u + v ∈ nonZeroDivisors S) : False := by
  have hinjQ : Function.Injective (algebraMap S Q) := IsLocalization.injective Q le_rfl
  obtain ⟨w, hw⟩ : IsUnit (algebraMap S Q (u + v)) := IsLocalization.map_units Q ⟨u + v, hnzd⟩
  set y : Q := ((w⁻¹ : Qˣ) : Q) with hydef
  have hyw : algebraMap S Q (u + v) * y = 1 := by rw [← hw, hydef, Units.mul_inv]
  set e : Q := algebraMap S Q u * y with hedef
  have hkey : algebraMap S Q u * algebraMap S Q (u + v)
      = algebraMap S Q u * algebraMap S Q u := by
    rw [← map_mul, ← map_mul]
    congr 1
    rw [mul_add, huv0, add_zero]
  have hee : e * e = e := by
    calc e * e = algebraMap S Q u * algebraMap S Q u * (y * y) := by rw [hedef]; ring
      _ = algebraMap S Q u * algebraMap S Q (u + v) * (y * y) := by rw [hkey]
      _ = algebraMap S Q u * (algebraMap S Q (u + v) * y) * y := by ring
      _ = e := by rw [hyw, hedef]; ring
  have hewu : e * algebraMap S Q (u + v) = algebraMap S Q u := by
    calc e * algebraMap S Q (u + v)
        = algebraMap S Q u * (algebraMap S Q (u + v) * y) := by rw [hedef]; ring
      _ = algebraMap S Q u := by rw [hyw, mul_one]
  have heint : IsIntegral S e := (isIdempotentElem_iff.mpr hee).isIntegral
  have hxnot : ∀ c : S, algebraMap S Q c ≠ e := by
    intro c hc
    have hcc : c * c = c := hinjQ (by rw [map_mul, hc, hee])
    have hcase : c = 0 ∨ c = 1 := by
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self c with hcu | hcu
      · exact Or.inr (hcu.mul_left_cancel (by rw [hcc, mul_one]))
      · have h5 : (1 - c) * (1 - c) = (1 - c) * 1 := by rw [mul_one]; linear_combination hcc
        exact Or.inl (by linear_combination -hcu.mul_left_cancel h5)
    rcases hcase with rfl | rfl
    · refine hu (hinjQ ?_)
      rw [map_zero, ← hewu, ← hc, map_zero, zero_mul]
    · refine hv (hinjQ ?_)
      rw [map_zero]
      have h6 : algebraMap S Q (u + v) = algebraMap S Q u := by
        rw [← hewu, ← hc, map_one, one_mul]
      rw [map_add] at h6
      linear_combination h6
  have hcond : ∀ q : Ideal S, ∀ _ : q.IsPrime, q ≠ maximalIdeal S →
      ∃ s ∈ q.primeCompl, ∃ a : S, algebraMap S Q s * e = algebraMap S Q a := by
    intro q hq hqm
    have := hloc q hq hqm
    have h0 : algebraMap S (Localization.AtPrime q) u *
        algebraMap S (Localization.AtPrime q) v = 0 := by
      rw [← map_mul, huv0, map_zero]
    rcases mul_eq_zero.1 h0 with h | h
    · obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl _ u).1 h
      refine ⟨s, s.2, 0, ?_⟩
      rw [map_zero, hedef, ← mul_assoc, ← map_mul, hs, map_zero, zero_mul]
    · obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl _ v).1 h
      refine ⟨s, s.2, s, ?_⟩
      have hsu : (s : S) * u = (s : S) * (u + v) := by rw [mul_add]; linear_combination -hs
      calc algebraMap S Q (s : S) * e
          = algebraMap S Q ((s : S) * u) * y := by rw [hedef, map_mul]; ring
        _ = algebraMap S Q ((s : S) * (u + v)) * y := by rw [hsu]
        _ = algebraMap S Q (s : S) * (algebraMap S Q (u + v) * y) := by rw [map_mul]; ring
        _ = algebraMap S Q (s : S) := by rw [hyw, mul_one]
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_conductor S Q hdep heint hcond
  exact hxnot c hc

/-- A reduced Noetherian local ring of depth at least `2` whose localizations at the non-maximal
primes are domains is a domain.

If `a b = 0` with `a ≠ 0` and `b ≠ 0`, put `I = (0 : a)` and `J = (0 : I)`, so that `I J = 0`,
`b ∈ I` and `a ∈ J`. No prime `𝔮 ≠ 𝔪` contains `I + J`: in the domain `S_𝔮` either `a` dies, and
then a single element of `S ∖ 𝔮` killing it lies in `I`, or every element of `I` dies, and then a
single element of `S ∖ 𝔮` killing the finitely generated `I` lies in `J`. Hence `𝔪^n ⊆ I + J`, and
writing `t^n = u + v` with `u ∈ I`, `v ∈ J` for a nonzerodivisor `t ∈ 𝔪` contradicts
`Stacks.Serre.NormalityCriterion.false_of_mul_eq_zero_of_add_mem_nonZeroDivisors`. -/
private lemma isDomain_of_two_le_depth (S : Type u) [CommRing S] [IsNoetherianRing S]
    [IsLocalRing S] (hdep : 2 ≤ Module.depth S (maximalIdeal S) S)
    (hloc : ∀ q : Ideal S, ∀ _ : q.IsPrime, q ≠ maximalIdeal S →
      IsDomain (Localization.AtPrime q)) :
    IsDomain S := by
  have hnzd : NoZeroDivisors S := by
    constructor
    intro a b hab
    by_contra hcon
    obtain ⟨ha, hb⟩ := not_or.1 hcon
    set I : Ideal S := (Submodule.span S {a}).annihilator with hIdef
    set J : Ideal S := I.annihilator with hJdef
    have hmemI : ∀ c : S, c ∈ I ↔ c * a = 0 := fun c => by
      rw [hIdef, Submodule.mem_annihilator_span_singleton, smul_eq_mul]
    have hbI : b ∈ I := (hmemI b).2 (by rwa [mul_comm])
    have hIJ : ∀ u ∈ I, ∀ v ∈ J, u * v = 0 := fun u hu v hv => by
      rw [mul_comm]
      exact Submodule.mem_annihilator.1 hv u hu
    have hrad : maximalIdeal S ≤ (I ⊔ J).radical := by
      refine maximalIdeal_le_radical_of_forall_not_le _ fun q hq hqm hq1 => ?_
      have := hloc q hq hqm
      have hIq : I ≤ q := le_trans le_sup_left hq1
      have hJq : J ≤ q := le_trans le_sup_right hq1
      by_cases hA : algebraMap S (Localization.AtPrime q) a = 0
      · obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl _ a).1 hA
        exact s.2 (hIq ((hmemI (s : S)).2 hs))
      · have hkill : ∀ c ∈ I, algebraMap S (Localization.AtPrime q) c = 0 := by
          intro c hc
          have h0 : algebraMap S (Localization.AtPrime q) c *
              algebraMap S (Localization.AtPrime q) a = 0 := by
            rw [← map_mul, (hmemI c).1 hc, map_zero]
          exact (mul_eq_zero.1 h0).resolve_right hA
        obtain ⟨s, hs, hz⟩ := exists_mem_forall_mul_eq_zero_of_fg q.primeCompl
          (Localization.AtPrime q) I (IsNoetherian.noetherian I) hkill
        refine hs (hJq (Submodule.mem_annihilator.2 fun d hd => ?_))
        rw [smul_eq_mul]
        exact hz d hd
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
    obtain ⟨t, htm, ht⟩ :=
      exists_mem_nonZeroDivisors_of_one_le_depth S (le_trans (by norm_num) hdep)
    have htN : t ^ N ∈ nonZeroDivisors S := pow_mem ht N
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (hN (Ideal.pow_mem_pow htm N))
    have hune : u ≠ 0 := by
      intro h0
      have htJ : t ^ N ∈ J := by rwa [← huv, h0, zero_add]
      exact hb ((mem_nonZeroDivisors_iff.1 htN).2 b (hIJ b hbI _ htJ))
    have hvne : v ≠ 0 := by
      intro h0
      have htI : t ^ N ∈ I := by rwa [← huv, h0, add_zero]
      exact ha ((mem_nonZeroDivisors_iff.1 htN).1 a ((hmemI _).1 htI))
    exact false_of_mul_eq_zero_of_add_mem_nonZeroDivisors S (FractionRing S) hdep hloc hune hvne
      (hIJ u hu v hv) (by rwa [huv])
  exact NoZeroDivisors.to_isDomain S

/-- A reduced Noetherian local ring of depth at least `2` all of whose localizations at
non-maximal primes are normal domains is integrally closed in its total ring of fractions.

This is the `d ≥ 2` case of (2) `⇒` (1) in [StacksProject 031S]. For `x` in the total ring of
fractions `Q(S) = FractionRing S` integral over `S`, the ring `S' = S[x]` is module-finite over
`S`; the hypothesis on the non-maximal primes gives `S_𝔮 = S'_𝔮` for every `𝔮 ≠ 𝔪`, so a power of
`𝔪` annihilates `S'/S`, and `not_exists_finite_of_two_le_depth` rules that out. -/
private lemma isIntegrallyClosed_of_two_le_depth (S : Type u) [CommRing S] [IsNoetherianRing S]
    [IsLocalRing S] [IsReduced S] (hdep : 2 ≤ Module.depth S (maximalIdeal S) S)
    (hloc : ∀ P : Ideal S, ∀ _ : P.IsPrime, P ≠ maximalIdeal S →
      IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P)) :
    IsIntegrallyClosed S := by
  have : IsDomain S := isDomain_of_two_le_depth S hdep fun q hq hqm => (hloc q hq hqm).1
  rw [isIntegrallyClosed_iff (FractionRing S)]
  intro x hx
  refine exists_algebraMap_eq_of_conductor S (FractionRing S) hdep hx fun q hq hqm => ?_
  have := (hloc q hq hqm).1
  have := (hloc q hq hqm).2
  obtain ⟨c, hc⟩ :=
    IsIntegrallyClosed.isIntegral_iff.1 (hx.tower_top (A := Localization.AtPrime q))
  obtain ⟨⟨a, s⟩, hsa⟩ := IsLocalization.surj q.primeCompl c
  refine ⟨s, s.2, a, ?_⟩
  have h2 := congrArg (algebraMap (Localization.AtPrime q) (FractionRing S)) hsa
  rw [map_mul, hc, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h2
  rw [mul_comm]
  exact h2

/-- A Noetherian ring with properties `(R_1)` and `(S_2)` is normal.

The source's argument, by strong induction on the height of the prime `𝔭`. If `height 𝔭 ≤ 1`
then `(R_1)` makes `R_𝔭` regular, hence a field or a discrete valuation ring, hence a normal
domain. If `height 𝔭 ≥ 2` then `(S_2)` gives `depth R_𝔭 ≥ 2`; the induction hypothesis makes
every localization of `R_𝔭` at a non-maximal prime a normal domain, whence `R_𝔭` is reduced,
integrally closed in its total ring of fractions, and a domain. Note that the source's appeal to
Lemma 031R for reducedness is replaced by `isReduced_of_forall_isReduced_localization`, which
only needs the induction hypothesis and `depth R_𝔭 ≥ 1`. -/
@[ega "IV 7.3.9" "(i)", sga "2 XI 3.11" "sufficiency"]
private lemma backward {R : Type u} [CommRing R] [IsNoetherianRing R]
    (hR1 : ∀ (p : Ideal R) [p.IsPrime], p.height ≤ 1 →
        IsRegularLocalRing (Localization.AtPrime p))
    (hS2 : ∀ (p : Ideal R) [p.IsPrime],
        min 2 (ringKrullDim (Localization.AtPrime p)) ≤
          (Module.depth (Localization.AtPrime p)
            (IsLocalRing.maximalIdeal (Localization.AtPrime p))
            (Localization.AtPrime p) : WithBot ℕ∞)) :
    ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  suffices key : ∀ n : ℕ, ∀ (p : Ideal R) (_ : p.IsPrime), p.height ≤ (n : ℕ∞) →
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) by
    intro p hp
    obtain ⟨n, hn⟩ :=
      ENat.ne_top_iff_exists.1 (show p.height ≠ ⊤ from Ideal.height_ne_top_of_isPrime)
    exact key n p hp hn.ge
  intro n
  induction n with
  | zero =>
      intro p hp h0
      have hle1 : p.height ≤ 1 := le_trans h0 (by simp)
      exact normal_atPrime_of_height_le_one p (hR1 p hle1) hle1
  | succ n ih =>
      intro p hp hle
      by_cases h1 : p.height ≤ 1
      · exact normal_atPrime_of_height_le_one p (hR1 p h1) h1
      have h2 : 2 ≤ p.height := two_le_of_not_le_one h1
      have hdim : ringKrullDim (Localization.AtPrime p) = (p.height : WithBot ℕ∞) :=
        IsLocalization.AtPrime.ringKrullDim_eq_height p _
      have hdim2 : 2 ≤ ringKrullDim (Localization.AtPrime p) := by
        rw [hdim, show (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) from rfl]
        exact WithBot.coe_le_coe.2 h2
      have hdep : 2 ≤ Module.depth (Localization.AtPrime p)
          (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p) :=
        two_le_depth_of_min_le _ (hS2 p) hdim2
      have hIH : ∀ q : Ideal R, ∀ _ : q.IsPrime, q < p →
          IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) :=
        fun q hq hqp => ih q hq
          (ENat.lt_natCast_add_one_iff.1
            (by exact_mod_cast (Ideal.height_strict_mono_of_isPrime hqp).trans_le hle))
      have hloc := normal_localization_atPrime_of_forall_lt p hIH
      have hred : IsReduced (Localization.AtPrime p) := by
        refine isReduced_of_forall_isReduced_localization _
          (exists_mem_nonZeroDivisors_of_one_le_depth _ (le_trans (by norm_num) hdep))
          fun P hP hPne => ?_
        have := (hloc P hP hPne).1
        infer_instance
      have hic : IsIntegrallyClosed (Localization.AtPrime p) :=
        isIntegrallyClosed_of_two_le_depth _ hdep hloc
      exact ⟨isDomain_of_two_le_depth _ hdep fun q hq hqm => (hloc q hq hqm).1, hic⟩

public theorem solution
    {R : Type*} [CommRing R] [IsNoetherianRing R] :
    (∀ (p : Ideal R) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) ↔
      (∀ (p : Ideal R) [p.IsPrime], p.height ≤ 1 →
          IsRegularLocalRing (Localization.AtPrime p)) ∧
        ∀ (p : Ideal R) [p.IsPrime],
          min 2 (ringKrullDim (Localization.AtPrime p)) ≤
            (Module.depth (Localization.AtPrime p)
              (IsLocalRing.maximalIdeal (Localization.AtPrime p))
              (Localization.AtPrime p) : WithBot ℕ∞) :=
  ⟨forward, fun h => backward h.1 h.2⟩

end Stacks.Serre.NormalityCriterion

end

/-!
# Serre's criterion for normality

Let `R` be a Noetherian ring. Following Definition 031P, `R` has property `(R_k)` when the local
ring `R_𝔭` is regular for every prime `𝔭` of height `≤ k`, and property `(S_k)` when
`depth(R_𝔭) ≥ min{k, dim(R_𝔭)}` for every prime `𝔭`. A ring is *normal* (Definition 00GV) when
`R_𝔭` is a normal domain — a domain integrally closed in its fraction field — for every prime
`𝔭`. Serre's criterion says that normality is exactly `(R_1)` together with `(S_2)`.

One direction reduces, via the criterion `(R_0) + (S_1)` for reducedness (Lemma 031R), to showing
that a local Noetherian normal domain of dimension `d` has depth `≥ min{2, d}` and is regular
when `d = 1`; the case `d ≥ 2` is the four-way alternative of Lemma 0BHZ, whose cases (1), (2)
and (4) are excluded by normality. The converse direction is again reduced to the local case by
Lemma 031R, and there `(S_2)` forbids the finite extension `R[x]` of a putative non-integral
`x ∈ Q(R)` from having support `{𝔪}`, so `R` is integrally closed in `Q(R)` and Lemma 030C
applies.

## Main results

* `isDomain_and_isIntegrallyClosed_atPrime_iff_isRegularLocalRing_and_min_two_le_depth`:
  a Noetherian ring is normal if and only if it has properties `(R_1)` and `(S_2)`.

## Implementation notes

Mathlib defines no predicate for a normal ring — its `IsIntegrallyClosed` file describes one in
prose and cites tag 00GV, but stops there — so "`R` is a normal ring" is inlined as
"`Localization.AtPrime 𝔭` is a domain and is integrally closed, for every prime `𝔭`". That is the
spelling used for item (1) of tag 030C and the shape `isRegularRing_iff` uses for the same kind
of local condition, and it is definitionally the `IsNormalRing` of tag 00GV as this repository
states it, so a later promotion of that predicate turns this statement into `IsNormalRing R ↔ ⋯`
by `Iff.rfl`. The `IsDomain` conjunct is genuine content: `IsIntegrallyClosed` is Mathlib's
`IsIntegrallyClosedIn R (FractionRing R)`, which carries no domain hypothesis.

Properties `(R_1)` and `(S_2)` are likewise spelled out at `k = 1` and `k = 2`. Mathlib has
neither condition, and while general-`k` predicates for both do exist in this repository, they
measure depth with a different constant from the `Module.depth` of tag 00LI that this statement,
and the four-way alternative 0BHZ that proves it, are phrased with; spelling the two cases out
keeps all three about one notion of depth. `(R_1)` uses Mathlib's `Ideal.height`, the source's
height of a prime, and `IsRegularLocalRing`, which bundles Noetherian and local. `(S_2)` is the
inequality of Definition 031P read in `WithBot ℕ∞`, where `Module.depth` (tag 00LI) takes values
in `ℕ∞` with `depth(0) = ⊤` while `ringKrullDim` takes values in `WithBot ℕ∞`, the value `⊥`
recording `dim(∅) = -∞`; `dim(R_𝔭)` is written as `ringKrullDim (Localization.AtPrime 𝔭)`, which
is the source's literal `dim(R_𝔭)` and equals `Ideal.height 𝔭` by
`IsLocalization.AtPrime.ringKrullDim_eq_height`, so a user may work in `ℕ∞` throughout.

Faithfulness to [StacksProject 031S]:

1. No dead hypothesis: `IsNoetherianRing R` is load-bearing in both directions, and not only
   because Definition 031P presupposes it. The ring `ℤ̄` of all algebraic integers is a normal
   ring of dimension `1`, but its localization at a maximal ideal is a non-discrete rank-one
   valuation ring, hence not Noetherian and so not `IsRegularLocalRing`, while that maximal ideal
   has height `1`; so (1) holds and `(R_1)` fails without the hypothesis. In the other direction
   it is what makes `R[x]` finite over `R` and Lemma 0BHZ available.
2. The scalars and base are the source's: at each prime everything happens over `R_𝔭` and not
   over `R`. Integrality is that of `R_𝔭` inside its own fraction field, not of `R` inside
   `Q(R)`; the depth is that of `R_𝔭` as a module over itself along its maximal ideal, i.e.
   `Module.depth R_𝔭 (maximalIdeal R_𝔭) R_𝔭` and not `Module.depth R 𝔭 R`; and the dimension is
   that of `R_𝔭`, not of `R`.
3. The source names no canonical map here, but it does name the local rings: the localizations
   are pinned to the canonical model `Localization.AtPrime 𝔭` with its canonical algebra
   structure over `R`, so all three conditions are about the localizations of `R` and not about
   some local rings with the same invariants.
4. The instantiation is not degenerate, and neither conjunct on the right is redundant.
   Both sides hold for every field — the only prime is `⊥`, the localization there is a field,
   so `(R_1)` is immediate and `min{2, 0} = 0` — as well as for `R = ℤ`, for `R = k[x, y]`, and
   for the non-regular normal ring `R = k[x, y, z]/(xy - z²)`. Both sides fail for
   `R = k[x, y]/(xy)`, whose localization at the origin — a height-one prime — is not a domain.
   The cusp `R = k[x, y]/(y² - x³)` is a one-dimensional hypersurface, so it satisfies `(S_2)`
   while failing `(R_1)` at the origin, and it is not normal. The union of two planes
   `R = k[x, y, z, w]/((x, y) ∩ (z, w))` has singular locus the origin, a height-two prime, so it
   satisfies `(R_1)` while failing `(S_2)` there, and it is not normal either.

## References

* [StacksProject 031S](https://stacks.math.columbia.edu/tag/031S)
* [EGA IV, Theorem 5.8.6]

## Tags

normal ring, Serre's criterion, regular in codimension one, depth, Krull dimension
-/

@[expose] public section

/-- **Stacks Tag 031S (Serre's criterion for normality).** Let `R` be a Noetherian ring. Then `R`
is a normal ring — every localization `R_𝔭` at a prime is a domain integrally closed in its
fraction field — if and only if `R` has properties `(R_1)` and `(S_2)`: the local ring `R_𝔭` is
regular for every prime `𝔭` of height `≤ 1`, and `depth(R_𝔭) ≥ min{2, dim(R_𝔭)}` for every
prime `𝔭`, the latter inequality being read in `WithBot ℕ∞`. -/
@[stacks 031S "Normality is inlined as `IsDomain` plus `IsIntegrallyClosed` on \
  `Localization.AtPrime 𝔭` for every prime `𝔭`, as in item (1) of tag 030C, Mathlib having no \
  predicate for a normal ring; properties `(R_1)` and `(S_2)` are spelled out from Definition \
  031P at `k = 1` and `k = 2` with `Ideal.height`, `IsRegularLocalRing`, `ringKrullDim` and \
  `Module.depth` (tag 00LI), the depth inequality being read in `WithBot ℕ∞`. See the module \
  docstring.", ega "IV 5.8.6" "affine case", sga "2 XI 3.11" "more general"]
public theorem isDomain_and_isIntegrallyClosed_atPrime_iff_isRegularLocalRing_and_min_two_le_depth
    {R : Type*} [CommRing R] [IsNoetherianRing R] :
    (∀ (p : Ideal R) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) ↔
      (∀ (p : Ideal R) [p.IsPrime], p.height ≤ 1 →
          IsRegularLocalRing (Localization.AtPrime p)) ∧
        ∀ (p : Ideal R) [p.IsPrime],
          min 2 (ringKrullDim (Localization.AtPrime p)) ≤
            (Module.depth (Localization.AtPrime p)
              (IsLocalRing.maximalIdeal (Localization.AtPrime p))
              (Localization.AtPrime p) : WithBot ℕ∞) :=
                by apply Stacks.Serre.NormalityCriterion.solution

end
