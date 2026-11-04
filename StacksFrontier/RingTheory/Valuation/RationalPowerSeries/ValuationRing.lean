module

public import StacksFrontier.RingTheory.Valuation.RationalPowerSeries.CompletionEquiv

/-!
# Power series with nonnegative rational exponents: the valuation ring

## Main results

* `RationalPowerSeries.isDomain`, `RationalPowerSeries.isLocalRing`,
  `RationalPowerSeries.isValuationRing`: the ring is a local domain and a valuation ring.
* `RationalPowerSeries.t_mem_maximalIdeal`, `RationalPowerSeries.radical_span_t`: the
  monomial `t` lies in the maximal ideal, which is the radical of `(t)`.
* `RationalPowerSeries.isAdic_span_t`, `RationalPowerSeries.isComplete`: the topology is the
  `(t)`-adic one and the ring is separated and complete for it.
* `RationalPowerSeries.not_fg_maximalIdeal`: the maximal ideal is not finitely generated.

## Implementation notes

Completeness is `TopologicalRing.IsComplete`, that is, separatedness together with
completeness for the canonical right uniformity of the additive group. It holds because the
ideal `(t)` of `rationalPolynomial κ` is finitely generated, so the adic completion of a ring
at a finitely generated ideal is adically complete.

## References

* [Stacks Project, Tag 0CB8](https://stacks.math.columbia.edu/tag/0CB8)
-/

@[expose] public noncomputable section

namespace RationalPowerSeries

/-! ### The example -/

/-- **Stacks 0CB8.** The ring of power series with nonnegative rational exponents is a
domain. -/
@[stacks 0CB8 "the rational power series valuation ring"]
theorem isDomain (k : Type*) [Field k] : IsDomain (rationalPowerSeries k) := by
  obtain ⟨e, _⟩ := exists_ringEquiv_coefficientRing k
  have hne : (0 : rationalPowerSeries k) ≠ 1 := by
    intro h
    have heq : (0 : coefficientRing k) = 1 := by simpa using congrArg e h
    exact zero_ne_one heq
  let : Nontrivial (rationalPowerSeries k) := ⟨⟨0, 1, hne⟩⟩
  let : NoZeroDivisors (rationalPowerSeries k) := e.noZeroDivisors
  exact NoZeroDivisors.to_isDomain _

/-- **Stacks 0CB8.** The ring of power series with nonnegative rational exponents is a
domain. -/
@[stacks 0CB8 "the rational power series valuation ring"]
instance instIsDomain (k : Type*) [Field k] : IsDomain (rationalPowerSeries k) :=
  isDomain k

/-- **Stacks 0CB8.** The ring of power series with nonnegative rational exponents is
local. -/
@[stacks 0CB8 "the rational power series valuation ring"]
theorem isLocalRing (k : Type*) [Field k] : IsLocalRing (rationalPowerSeries k) := by
  obtain ⟨e, _⟩ := exists_ringEquiv_coefficientRing k
  let : IsLocalRing (coefficientRing k) := coefficientRing_isLocalRing k
  exact e.symm.isLocalRing

/-- **Stacks 0CB8.** The ring of power series with nonnegative rational exponents is
local. -/
@[stacks 0CB8 "the rational power series valuation ring"]
instance instIsLocalRing (k : Type*) [Field k] : IsLocalRing (rationalPowerSeries k) :=
  isLocalRing k

/-- **Stacks 0CB8.** This local domain is a valuation ring: inside its fraction field it is
maximal for the domination order among local subrings. -/
@[stacks 0CB8 "the rational power series valuation ring"]
theorem isValuationRing (k : Type*) [Field k] :
    IsValuationRing (rationalPowerSeries k) := by
  obtain ⟨e, _⟩ := exists_ringEquiv_coefficientRing k
  let : PreValuationRing (coefficientRing k) := coefficientRing_preValuationRing k
  let : ValuationRing (rationalPowerSeries k) :=
    Function.Surjective.valuationRing e.symm.toRingHom e.symm.surjective
  exact isValuationRing_of_valuationRing _

/-- **Stacks 0CB8.** The monomial `t` lies in the maximal ideal; in particular it is not a
unit. -/
@[stacks 0CB8 "the rational power series valuation ring"]
theorem t_mem_maximalIdeal (k : Type*) [Field k] :
    t k ∈ IsLocalRing.maximalIdeal (rationalPowerSeries k) := by
  rw [IsLocalRing.mem_maximalIdeal]
  simp only [mem_nonunits_iff]
  intro htunit
  obtain ⟨e, he⟩ := exists_ringEquiv_coefficientRing k
  apply coefficientRing_zero_const_notUnit (e (t k)) ?_ (e.toRingHom.isUnit_map htunit)
  simpa [t, polynomialT] using he (polynomialT k) 0

/-- **Stacks 0CB8.** The topology of `rationalPowerSeries k` is the `(t)`-adic topology. -/
@[stacks 0CB8 "the rational power series valuation ring"]
theorem isAdic_span_t (k : Type*) [Field k] :
    IsAdic (Ideal.span ({t k} : Set (rationalPowerSeries k))) := rfl

/-- **Stacks 0CB8.** The ring of power series with nonnegative rational exponents is
separated and complete for its `(t)`-adic topology. -/
@[stacks 0CB8 "the rational power series valuation ring"]
theorem isComplete (k : Type*) [Field k] :
    TopologicalRing.IsComplete (rationalPowerSeries k) := by
  let R := rationalPolynomial k
  let I := polynomialTIdeal k
  have hfg : I.FG := by
    show (Submodule.span R ({polynomialT k} : Set R)).FG
    exact Submodule.fg_span (Set.finite_singleton (polynomialT k))
  have heq : tIdeal k = I.map (algebraMap R (AdicCompletion I R)) := by
    show Ideal.span {AdicCompletion.of I R (polynomialT k)} =
      Ideal.map (algebraMap R (AdicCompletion I R)) (Ideal.span {polynomialT k})
    rw [Ideal.map_span, Set.image_singleton, AdicCompletion.algebraMap_apply]
    simp [R]
  have hcomplete : IsAdicComplete (tIdeal k) (rationalPowerSeries k) := by
    rw [heq]
    exact AdicCompletion.isAdicComplete_self I hfg
  let : UniformSpace (rationalPowerSeries k) :=
    IsTopologicalAddGroup.rightUniformSpace (rationalPowerSeries k)
  let : IsUniformAddGroup (rationalPowerSeries k) := isUniformAddGroup_of_addCommGroup
  have hc := (IsAdic.isAdicComplete_iff (isAdic_span_t k)).mp hcomplete
  exact ⟨hc.2, hc.1⟩

/-- A nonzero non-unit of `coefficientRing k` has positive order. -/
private theorem order_pos_of_not_isUnit {k : Type*} [Field k] (f : coefficientRing k)
    (hf : f.1 ≠ 0) (hu : ¬ IsUnit f) : 0 < f.1.order := by
  have hconst := coefficientRing_notUnit_coeff_zero f hu
  refine lt_of_le_of_ne bot_le (Ne.symm fun hzero => ?_)
  have hlead : f.1.leadingCoeff ≠ 0 := HahnSeries.leadingCoeff_ne_zero.mpr hf
  rw [HahnSeries.leadingCoeff_eq, hzero] at hlead
  exact hlead hconst

/-- **Stacks 0CB8.** The radical of `(t)` is the maximal ideal: every non-unit has positive
order, so some power of it is divisible by `t`. -/
@[stacks 0CB8 "the rational power series valuation ring"]
theorem radical_span_t (k : Type*) [Field k] :
    (Ideal.span ({t k} : Set (rationalPowerSeries k))).radical =
      IsLocalRing.maximalIdeal (rationalPowerSeries k) := by
  apply Ideal.ext
  intro x
  rw [Ideal.mem_radical_iff]
  have hspan : Ideal.span ({t k} : Set (rationalPowerSeries k)) ≤
      IsLocalRing.maximalIdeal (rationalPowerSeries k) :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (t_mem_maximalIdeal k))
  refine ⟨fun ⟨n, hn⟩ => (IsLocalRing.maximalIdeal.isMaximal _).isPrime.mem_of_pow_mem n
    (hspan hn), fun hx => ?_⟩
  obtain ⟨e, he⟩ := exists_ringEquiv_coefficientRing k
  have ht := coefficientRing_equiv_t e he
  have hxnu : ¬ IsUnit x := by
    simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hx
  have hnotunit : ¬ IsUnit (e x) := fun hu =>
    hxnu (by simpa using e.symm.toRingHom.isUnit_map hu)
  by_cases hx0 : (e x).1 = 0
  · obtain rfl : x = 0 := e.injective (Subtype.ext (by simpa using hx0))
    exact ⟨1, by simp⟩
  let f : coefficientRing k := e x
  have horderpos : 0 < f.1.order := order_pos_of_not_isUnit f hx0 hnotunit
  obtain ⟨n, hn⟩ := exists_nat_gt ((1 : ℚ≥0) / f.1.order)
  have hlarge : 1 < n • f.1.order := by
    rw [nsmul_eq_mul]
    exact (div_lt_iff₀ horderpos).mp hn
  let p : HahnSeries ℚ≥0 k := f.1 ^ n
  have hpLF : ∀ m : ℕ, {q : ℚ≥0 | q ≤ m ∧ p.coeff q ≠ 0}.Finite := by
    simpa [p] using (mem_coefficientRing_iff k (f ^ n).1).mp (pow_mem f.2 n)
  have hbelow : ∀ q : ℚ≥0, q < 1 → p.coeff q = 0 := by
    intro q hq
    have hpowOrder : 1 < p.order := by
      dsimp [p]
      rw [HahnSeries.order_pow]
      simpa [f] using hlarge
    exact HahnSeries.coeff_eq_zero_of_lt_order (lt_trans hq hpowOrder)
  let y : HahnSeries ℚ≥0 k := shiftDownHahn p hpLF 1
  have hyLF : ∀ m : ℕ, {q : ℚ≥0 | q ≤ m ∧ y.coeff q ≠ 0}.Finite := by
    simpa [y, shiftDownHahn, coefficientFamilyToHahn] using
      (shiftDownFamily ⟨p.coeff, hpLF⟩ 1).2
  have hfactor : HahnSeries.single 1 (1 : k) * y = p :=
    single_mul_shiftDown_eq p hpLF 1 hbelow
  let yS : coefficientRing k := ⟨y, (mem_coefficientRing_iff k y).2 hyLF⟩
  have hmiddle : (e x) ^ n = e (t k) * e (e.symm yS) := by
    apply Subtype.ext
    show (e x).1 ^ n = (e (t k)).1 * (e (e.symm yS)).1
    rw [RingEquiv.apply_symm_apply, ht]
    exact hfactor.symm
  have hpow : x ^ n = t k * e.symm yS := by
    apply e.injective
    rw [map_pow, map_mul]
    exact hmiddle
  exact ⟨n, Ideal.mem_span_singleton.mpr ⟨e.symm yS, hpow⟩⟩

/-- The monomial `t` is a nonzero element of the completion: the coefficient of exponent one
of the corresponding series is `1`. -/
theorem t_ne_zero (k : Type*) [Field k] : t k ≠ 0 := by
  intro ht
  obtain ⟨e, he⟩ := exists_ringEquiv_coefficientRing k
  have heq : e (t k) = 0 := by simpa using congrArg e ht
  have hval := congrArg Subtype.val heq
  rw [coefficientRing_equiv_t e he] at hval
  change HahnSeries.single 1 (1 : k) = 0 at hval
  have hzero : (HahnSeries.single (1 : ℚ≥0) (1 : k)).coeff 1 = 0 := by
    rw [hval]
    simp
  simp at hzero

/-- **Stacks 0CB8.** The maximal ideal is not finitely generated: finitely many elements of
the maximal ideal have a least positive order `a`, and the monomial of exponent `a / 2` is in
the maximal ideal but not in the ideal they generate. -/
@[stacks 0CB8 "the rational power series valuation ring"]
theorem not_fg_maximalIdeal (k : Type*) [Field k] :
    ¬ (IsLocalRing.maximalIdeal (rationalPowerSeries k)).FG := by
  classical
  intro hfg
  obtain ⟨e, -⟩ := exists_ringEquiv_coefficientRing k
  obtain ⟨n, F, hF⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp hfg
  have hspan : Ideal.span (Set.range F) =
      IsLocalRing.maximalIdeal (rationalPowerSeries k) := hF
  by_cases hn : n = 0
  · subst n
    have hrange : Set.range F = ∅ := by
      ext x
      simp
    have htSpan : t k ∈ Ideal.span (Set.range F) := hspan.symm ▸ t_mem_maximalIdeal k
    rw [hrange, Ideal.span_empty] at htSpan
    exact t_ne_zero k (Ideal.mem_bot.mp htSpan)
  let g (i : Fin n) : coefficientRing k := e (F i)
  have hnotunit (i : Fin n) : ¬ IsUnit (g i) := by
    intro hu
    have hu' : IsUnit (F i) := by
      simpa [g] using e.symm.toRingHom.isUnit_map hu
    have hmem : F i ∈ IsLocalRing.maximalIdeal (rationalPowerSeries k) := by
      rw [← hspan]
      exact Ideal.subset_span (Set.mem_range_self i)
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmem
    exact hmem hu'
  obtain ⟨q, hqpos, hgJ⟩ : ∃ q : ℚ≥0, 0 < q ∧ ∀ i, g i ∈ coefficientVanishingIdeal q := by
    let d (i : Fin n) : ℚ≥0 := if g i = 0 then 1 else (g i).1.order
    have hdpos (i : Fin n) : 0 < d i := by
      by_cases hz : g i = 0
      · simp [d, hz]
      · simp only [d, ite_eq_right hz]
        exact order_pos_of_not_isUnit (g i) (fun h => hz (Subtype.ext h)) (hnotunit i)
    let s : Finset ℚ≥0 := Finset.univ.image d
    have hs : s.Nonempty := by
      obtain ⟨i⟩ := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
      exact ⟨d i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
    let a : ℚ≥0 := s.min' hs
    have ha : 0 < a := by
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.min'_mem s hs)
      show 0 < s.min' hs
      rw [← hi]
      exact hdpos i
    have hamin (i : Fin n) : a ≤ d i :=
      Finset.min'_le s (d i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    refine ⟨a / 2, by positivity, fun i r hr => ?_⟩
    by_cases hz : g i = 0
    · simp [hz]
    · apply HahnSeries.coeff_eq_zero_of_lt_order
      have hrd : r < d i := hr.trans_lt ((div_lt_self ha (by norm_num)).trans_le (hamin i))
      simpa [d, hz] using hrd
  let T : Ideal (coefficientRing k) := Ideal.span (Set.range g)
  have hTle : T ≤ coefficientVanishingIdeal q :=
    Ideal.span_le.mpr (Set.range_subset_iff.mpr hgJ)
  have hmap : Ideal.map e.toRingHom
      (IsLocalRing.maximalIdeal (rationalPowerSeries k)) = T := by
    rw [← hspan, Ideal.map_span]
    show Ideal.span (e '' Set.range F) = Ideal.span (Set.range g)
    rw [← Set.range_comp]
    rfl
  let m : coefficientRing k :=
    ⟨HahnSeries.single q (1 : k), single_mem_coefficientRing _ _⟩
  have hmconst : m.1.coeff 0 = 0 := by
    simp [m, Ne.symm (ne_of_gt hqpos)]
  have hmnotJ : m ∉ coefficientVanishingIdeal q := fun hm => by simpa [m] using hm q le_rfl
  let x : rationalPowerSeries k := e.symm m
  have hxM : x ∈ IsLocalRing.maximalIdeal (rationalPowerSeries k) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hxunit
    have hmUnit : IsUnit m := by
      simpa [x] using e.toRingHom.isUnit_map hxunit
    exact (coefficientRing_zero_const_notUnit m hmconst) hmUnit
  have hxm : m ∈ T := by
    rw [← hmap]
    simpa [x] using Ideal.mem_map_of_mem e.toRingHom hxM
  exact hmnotJ (hTle hxm)

end RationalPowerSeries

end
