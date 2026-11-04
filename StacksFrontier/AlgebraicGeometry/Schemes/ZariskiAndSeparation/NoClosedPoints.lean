module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Data.Finsupp.Lex
public import Mathlib.RingTheory.HahnSeries.Summable
public import Mathlib.RingTheory.HahnSeries.Valuation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Valuation.Domination
public import StacksFrontier.RingTheory.Valuation.ValueGroup

/-!
# A scheme without closed points

There is a valuation ring whose prime ideals form a strictly increasing countable chain followed
by its maximal ideal. The complement of the closed point in its spectrum is a nonempty scheme
with no closed points.

## Main results

* `AlgebraicGeometry.exists_valuationRing_with_spectrum_chain`: the local valuation domain with
  the spectrum described in the example.
* `AlgebraicGeometry.puncturedSpectrum_no_closed_points`: the property of the associated open
  subscheme.
* `AlgebraicGeometry.exists_scheme_without_closed_points`: the stated example.

## Implementation notes

The ring is characterized by the ordered chain of its prime ideals rather than by a particular
presentation of its value group. The prime-ideal chain is the one obtained from the
lexicographically ordered direct sum of countably many copies of `ℤ`, realized inside a field of
Hahn series. The punctured spectrum is represented by Mathlib's open-subscheme construction.

## References

* [Stacks Project, Tag 01IY](https://stacks.math.columbia.edu/tag/01IY)
* [Krull]
-/

public section

namespace AlgebraicGeometry

universe u

private abbrev LexIntegerGroup := Lex (ℕ →₀ ℤ)

private noncomputable def hahnValuation :
    Valuation (HahnSeries LexIntegerGroup (ULift.{u} ℚ))
      (Multiplicative (WithTop LexIntegerGroup)ᵒᵈ) :=
  (HahnSeries.addVal LexIntegerGroup (ULift.{u} ℚ)).toValuation

private noncomputable def hahnValuationRing :
    ValuationSubring (HahnSeries LexIntegerGroup (ULift.{u} ℚ)) :=
  Valuation.valuationSubring hahnValuation

private theorem valuationSubring_isValuationRing {K : Type*} [Field K]
    (v : Valuation K (Multiplicative (WithTop LexIntegerGroup)ᵒᵈ)) :
    IsValuationRing v.valuationSubring := by
  let A := v.valuationSubring
  change IsMax (LocalSubring.range (algebraMap A (FractionRing A)))
  let w := ValuationRing.valuation A (FractionRing A)
  apply (LocalSubring.isMax_iff).2
  refine ⟨w.valuationSubring, ?_⟩
  apply LocalSubring.toSubring_injective
  change w.valuationSubring.toSubring = (algebraMap A (FractionRing A)).range
  rw [← ValuationRing.range_algebraMap_eq A (FractionRing A)]
  rfl

private noncomputable def leadingIndex (g : LexIntegerGroup) (hg : 0 < g) : ℕ :=
  Classical.choose (Finsupp.Lex.lt_iff.mp hg)

private theorem leadingIndex_spec (g : LexIntegerGroup) (hg : 0 < g) :
    (∀ j < leadingIndex g hg, (ofLex g) j = 0) ∧ 0 < (ofLex g) (leadingIndex g hg) := by
  obtain ⟨hi, hpos⟩ := Classical.choose_spec (Finsupp.Lex.lt_iff.mp hg)
  exact ⟨fun j hj => (hi j hj).symm, hpos⟩

private theorem leadingIndex_eq_of_spec {g : LexIntegerGroup} (hg : 0 < g)
    {i : ℕ} (hi : (∀ j < i, (ofLex g) j = 0) ∧ 0 < (ofLex g) i) :
    leadingIndex g hg = i := by
  have hs := leadingIndex_spec g hg
  rcases lt_trichotomy (leadingIndex g hg) i with h | h | h
  · exact False.elim <| (ne_of_gt hs.2) (hi.1 _ h)
  · exact h
  · exact False.elim <| (ne_of_gt hi.2) (hs.1 _ h)

private noncomputable def basisValue (i : ℕ) : LexIntegerGroup :=
  Finsupp.single i (1 : ℤ)

private theorem basisValue_pos (i : ℕ) : 0 < basisValue i := by
  apply Finsupp.Lex.lt_iff.mpr
  refine ⟨i, ?_, ?_⟩
  · intro j hj
    rw [show ofLex (0 : LexIntegerGroup) = 0 from rfl,
      show ofLex (basisValue i) = Finsupp.single i (1 : ℤ) from rfl]
    exact (Finsupp.single_eq_of_ne (a := i) (a' := j) (b := (1 : ℤ)) (ne_of_lt hj)).symm
  · rw [show ofLex (0 : LexIntegerGroup) = 0 from rfl,
      show ofLex (basisValue i) = Finsupp.single i (1 : ℤ) from rfl]
    simp

private theorem leadingIndex_basisValue (i : ℕ) :
    leadingIndex (basisValue i) (basisValue_pos i) = i := by
  apply leadingIndex_eq_of_spec (basisValue_pos i)
  constructor
  · intro j hj
    rw [show ofLex (basisValue i) = Finsupp.single i (1 : ℤ) from rfl]
    exact Finsupp.single_eq_of_ne (a := i) (a' := j) (b := (1 : ℤ)) (ne_of_lt hj)
  · rw [show ofLex (basisValue i) = Finsupp.single i (1 : ℤ) from rfl]
    simp

private theorem ofLex_nonneg_of_le_leadingIndex {g : LexIntegerGroup} (hg : 0 < g) {i : ℕ}
    (hi : i ≤ leadingIndex g hg) : 0 ≤ ofLex g i := by
  rcases hi.lt_or_eq with hlt | rfl
  · rw [(leadingIndex_spec g hg).1 _ hlt]
  · exact (leadingIndex_spec g hg).2.le

private theorem leadingIndex_add {g h : LexIntegerGroup} (hg : 0 < g) (hh : 0 < h) :
    leadingIndex (g + h) (add_pos hg hh) =
      min (leadingIndex g hg) (leadingIndex h hh) := by
  apply leadingIndex_eq_of_spec (add_pos hg hh)
  refine ⟨fun j hj => ?_, ?_⟩
  · simp [(leadingIndex_spec g hg).1 j (hj.trans_le (min_le_left _ _)),
      (leadingIndex_spec h hh).1 j (hj.trans_le (min_le_right _ _))]
  · have hsum : 0 < ofLex g (min (leadingIndex g hg) (leadingIndex h hh)) +
        ofLex h (min (leadingIndex g hg) (leadingIndex h hh)) := by
      rcases le_total (leadingIndex g hg) (leadingIndex h hh) with ho | ho
      · rw [min_eq_left ho]
        exact add_pos_of_pos_of_nonneg (leadingIndex_spec g hg).2
          (ofLex_nonneg_of_le_leadingIndex hh ho)
      · rw [min_eq_right ho]
        exact add_pos_of_nonneg_of_pos (ofLex_nonneg_of_le_leadingIndex hg ho)
          (leadingIndex_spec h hh).2
    simpa [Finsupp.coe_add] using hsum

private theorem leadingIndex_le_of_le {g h : LexIntegerGroup} (hg : 0 < g) (hh : 0 < h)
    (hgh : g ≤ h) : leadingIndex h hh ≤ leadingIndex g hg := by
  by_contra! hltIdx
  have hsmall : h < g := by
    apply Finsupp.Lex.lt_iff.mpr
    refine ⟨leadingIndex g hg, ?_, ?_⟩
    · exact fun j hj => ((leadingIndex_spec h hh).1 j (hj.trans hltIdx)).trans
        ((leadingIndex_spec g hg).1 j hj).symm
    · rw [(leadingIndex_spec h hh).1 _ hltIdx]
      exact (leadingIndex_spec g hg).2
  exact hgh.not_gt hsmall

private theorem leadingIndex_congr {g h : LexIntegerGroup} (heq : g = h)
    (hg : 0 < g) (hh : 0 < h) : leadingIndex g hg = leadingIndex h hh := by
  cases heq
  rfl

private abbrev HahnField := HahnSeries LexIntegerGroup (ULift.{u} ℚ)

private noncomputable def hahnAddValuation : AddValuation HahnField (WithTop LexIntegerGroup) :=
  HahnSeries.addVal LexIntegerGroup (ULift.{u} ℚ)

private noncomputable def hahnOrder (x : hahnValuationRing) : LexIntegerGroup :=
  (x : HahnField).order

private theorem coe_hahnField_ne_zero {x : hahnValuationRing} (hx : x ≠ 0) : (x : HahnField) ≠ 0 :=
  fun h => hx (Subtype.ext h)

private theorem ne_zero_of_hahnOrder_pos {x : hahnValuationRing} (h : 0 < hahnOrder x) :
    x ≠ 0 := by
  rintro rfl
  simp [hahnOrder] at h

private theorem hahnValue_order (x : hahnValuationRing) (hx : x ≠ 0) :
    hahnAddValuation (x : HahnField) = (hahnOrder x : WithTop LexIntegerGroup) := by
  rw [hahnAddValuation, HahnSeries.addVal_apply,
    ← HahnSeries.order_eq_orderTop_of_ne_zero (coe_hahnField_ne_zero hx)]
  rfl

private theorem hahnOrder_nonneg (x : hahnValuationRing) : 0 ≤ hahnOrder x := by
  by_cases hx : x = 0
  · simp [hahnOrder, hx]
  · have hv := (Valuation.mem_valuationSubring_iff hahnValuation (x : HahnField)).mp x.property
    change (0 : WithTop LexIntegerGroup) ≤ hahnAddValuation (x : HahnField) at hv
    rw [hahnValue_order x hx] at hv
    exact (WithTop.coe_le_coe).mp hv

private theorem hahnOrder_nonunit_pos {x : hahnValuationRing} (hx : x ≠ 0)
    (hu : ¬ IsUnit x) : 0 < hahnOrder x := by
  have hn : hahnOrder x ≠ 0 := by
    intro hzero
    apply hu
    have hxval : hahnValuation (x : HahnField) = 1 := by
      change Multiplicative.ofAdd (hahnAddValuation (x : HahnField)) = 1
      rw [hahnValue_order x hx, hzero]
      rfl
    have hinv : ((x : HahnField)⁻¹) ∈ hahnValuationRing := by
      change ((x : HahnField)⁻¹) ∈ hahnValuation.valuationSubring
      rw [Valuation.mem_valuationSubring_iff hahnValuation, map_inv₀, hxval, inv_one]
    exact IsUnit.of_mul_eq_one (⟨(x : HahnField)⁻¹, hinv⟩ : hahnValuationRing)
      (Subtype.ext (mul_inv_cancel₀ (coe_hahnField_ne_zero hx)))
  exact (hahnOrder_nonneg x).lt_of_ne' hn

private noncomputable def basisSeries (i : ℕ) : HahnField :=
  HahnSeries.single (basisValue i) (ULift.up (1 : ℚ))

private theorem basisSeries_ne_zero (i : ℕ) : basisSeries i ≠ 0 :=
  HahnSeries.single_ne_zero one_ne_zero

private theorem basisSeries_orderTop (i : ℕ) :
    (basisSeries i).orderTop = (basisValue i : WithTop LexIntegerGroup) := by
  change (HahnSeries.single (basisValue i) (ULift.up (1 : ℚ))).orderTop = _
  rw [HahnSeries.orderTop_single (r := ULift.up (1 : ℚ)) one_ne_zero]

private theorem mem_hahnValuationRing_of_addVal_nonneg (x : HahnField)
    (hx : (0 : WithTop LexIntegerGroup) ≤ hahnAddValuation x) :
    x ∈ hahnValuationRing := by
  change x ∈ hahnValuation.valuationSubring
  rw [Valuation.mem_valuationSubring_iff hahnValuation]
  change (Multiplicative.ofAdd (hahnAddValuation x) :
    Multiplicative (WithTop LexIntegerGroup)ᵒᵈ) ≤ 1
  exact hx

private noncomputable def basisElement (i : ℕ) : hahnValuationRing :=
  ⟨basisSeries i, mem_hahnValuationRing_of_addVal_nonneg (basisSeries i) (by
    rw [hahnAddValuation, HahnSeries.addVal_apply, basisSeries_orderTop]
    exact WithTop.coe_le_coe.mpr (le_of_lt (basisValue_pos i)))⟩

private theorem basisElement_ne_zero (i : ℕ) : basisElement i ≠ 0 :=
  fun h => basisSeries_ne_zero i (congrArg Subtype.val h)

private theorem hahnOrder_basisElement (i : ℕ) : hahnOrder (basisElement i) = basisValue i := by
  unfold hahnOrder basisElement
  change ↑(basisSeries i).order = ↑(basisValue i)
  apply WithTop.coe_injective
  rw [HahnSeries.order_eq_orderTop_of_ne_zero (basisSeries_ne_zero i),
    basisSeries_orderTop]

private theorem leadingIndex_hahnOrder_basisElement (n : ℕ) (hp : 0 < hahnOrder (basisElement n)) :
    leadingIndex (hahnOrder (basisElement n)) hp = n :=
  (leadingIndex_congr (hahnOrder_basisElement n) hp (basisValue_pos n)).trans
    (leadingIndex_basisValue n)

private theorem hahnOrder_add_ge {x y : hahnValuationRing}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (hahnOrder x) (hahnOrder y) ≤ hahnOrder (x + y) := by
  have hv := AddValuation.map_add hahnAddValuation (x : HahnField) (y : HahnField)
  change min (hahnAddValuation (x : HahnField)) (hahnAddValuation (y : HahnField)) ≤
    hahnAddValuation ((x + y : hahnValuationRing) : HahnField) at hv
  rw [hahnValue_order x hx, hahnValue_order y hy, hahnValue_order (x + y) hxy,
    ← WithTop.coe_min] at hv
  exact (WithTop.coe_le_coe).mp hv

private theorem hahnOrder_mul {x y : hahnValuationRing}
    (hx : x ≠ 0) (hy : y ≠ 0) : hahnOrder (x * y) = hahnOrder x + hahnOrder y := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  have hv := AddValuation.map_mul hahnAddValuation (x : HahnField) (y : HahnField)
  change hahnAddValuation ((x * y : hahnValuationRing) : HahnField) =
    hahnAddValuation (x : HahnField) + hahnAddValuation (y : HahnField) at hv
  rw [hahnValue_order x hx, hahnValue_order y hy, hahnValue_order (x * y) hxy] at hv
  exact WithTop.coe_injective hv

private theorem dvd_of_hahnOrder_le {x y : hahnValuationRing} (hx : x ≠ 0)
    (hxy : hahnOrder x ≤ hahnOrder y) : x ∣ y := by
  by_cases hy : y = 0
  · simp [hy]
  have hv : (0 : WithTop LexIntegerGroup) ≤
      hahnAddValuation ((y : HahnField) / (x : HahnField)) := by
    rw [AddValuation.map_div, hahnValue_order y hy, hahnValue_order x hx]
    exact WithTop.coe_le_coe.mpr (sub_nonneg.mpr hxy)
  let z : hahnValuationRing :=
    ⟨(y : HahnField) / (x : HahnField), mem_hahnValuationRing_of_addVal_nonneg _ hv⟩
  refine ⟨z, ?_⟩
  apply Subtype.ext
  change (y : HahnField) = (x : HahnField) * ((y : HahnField) / (x : HahnField))
  field_simp [coe_hahnField_ne_zero hx]

/-- A nonzero-order element of small leading index is dominated by anything of larger order. -/
private theorem mem_carrier_of_hahnOrder_le {n : ℕ} {x z : hahnValuationRing}
    (hxp : 0 < hahnOrder x) (hxi : leadingIndex (hahnOrder x) hxp < n)
    (hle : hahnOrder x ≤ hahnOrder z) :
    z = 0 ∨ ∃ hz : 0 < hahnOrder z, leadingIndex (hahnOrder z) hz < n :=
  have hzp := hxp.trans_le hle
  Or.inr ⟨hzp, (leadingIndex_le_of_le hxp hzp hle).trans_lt hxi⟩

private noncomputable def hahnPrimeIdeal (n : ℕ) : Ideal hahnValuationRing where
  carrier := {x | x = 0 ∨ ∃ hx : 0 < hahnOrder x,
    leadingIndex (hahnOrder x) hx < n}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro x y hx hy
    rcases hx with rfl | ⟨hxp, hxi⟩
    · simpa using hy
    rcases hy with rfl | ⟨hyp, hyi⟩
    · rw [add_zero]
      exact Or.inr ⟨hxp, hxi⟩
    have hx0 := ne_zero_of_hahnOrder_pos hxp
    have hy0 := ne_zero_of_hahnOrder_pos hyp
    by_cases hxy : x + y = 0
    · exact Or.inl hxy
    have hsum := hahnOrder_add_ge hx0 hy0 hxy
    rcases le_total (hahnOrder x) (hahnOrder y) with h | h
    · exact mem_carrier_of_hahnOrder_le hxp hxi ((le_min le_rfl h).trans hsum)
    · exact mem_carrier_of_hahnOrder_le hyp hyi ((le_min h le_rfl).trans hsum)
  smul_mem' := by
    intro r x hx
    rcases hx with rfl | ⟨hxp, hxi⟩
    · simp
    by_cases hr : r = 0
    · simp [hr]
    have hx0 := ne_zero_of_hahnOrder_pos hxp
    have hle : hahnOrder x ≤ hahnOrder (r * x) := by
      rw [hahnOrder_mul hr hx0]
      exact le_add_of_nonneg_left (hahnOrder_nonneg r)
    exact mem_carrier_of_hahnOrder_le hxp hxi hle

private theorem hahnPrimeIdeal_isPrime (n : ℕ) : (hahnPrimeIdeal n).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one]
    intro h
    rcases h with h | ⟨hp, hi⟩
    · exact one_ne_zero h
    · simp [hahnOrder] at hp
  · intro x y hxy
    by_cases hx : x = 0
    · exact Or.inl (Or.inl hx)
    by_cases hy : y = 0
    · exact Or.inr (Or.inl hy)
    rcases hxy with hzero | ⟨hp, hi⟩
    · exact absurd hzero (mul_ne_zero hx hy)
    · have hmul := hahnOrder_mul hx hy
      by_cases hx0 : hahnOrder x = 0
      · exact Or.inr (mem_carrier_of_hahnOrder_le hp hi (by rw [hmul, hx0, zero_add]))
      have hxpos : 0 < hahnOrder x := (hahnOrder_nonneg x).lt_of_ne' hx0
      by_cases hy0 : hahnOrder y = 0
      · exact Or.inl (mem_carrier_of_hahnOrder_le hp hi (by rw [hmul, hy0, add_zero]))
      have hypos : 0 < hahnOrder y := (hahnOrder_nonneg y).lt_of_ne' hy0
      have hsumPos : 0 < hahnOrder x + hahnOrder y := hmul ▸ hp
      have hidxeq := (leadingIndex_congr hmul hp hsumPos).trans (leadingIndex_add hxpos hypos)
      have hidxlt : min (leadingIndex (hahnOrder x) hxpos)
          (leadingIndex (hahnOrder y) hypos) < n := by
        simpa [hidxeq] using hi
      rcases min_lt_iff.mp hidxlt with h | h
      · exact Or.inl (Or.inr ⟨hxpos, h⟩)
      · exact Or.inr (Or.inr ⟨hypos, h⟩)

private noncomputable def hahnPrimeSpectrumPoint (n : ℕ) : PrimeSpectrum hahnValuationRing :=
  ⟨hahnPrimeIdeal n, hahnPrimeIdeal_isPrime n⟩

private theorem hahnPrimeIdeal_mono (n : ℕ) :
    hahnPrimeIdeal n ≤ hahnPrimeIdeal (n + 1) := by
  rintro x (rfl | ⟨hp, hi⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨hp, hi.trans (Nat.lt_succ_self n)⟩

private theorem hahnPrimeIdeal_chain_strict (n : ℕ) :
    hahnPrimeIdeal n < hahnPrimeIdeal (n + 1) := by
  refine lt_of_le_of_ne (hahnPrimeIdeal_mono n) ?_
  intro heq
  have hmem : basisElement n ∈ hahnPrimeIdeal (n + 1) := by
    have hp : 0 < hahnOrder (basisElement n) := by
      rw [hahnOrder_basisElement]
      exact basisValue_pos n
    exact Or.inr ⟨hp, (leadingIndex_hahnOrder_basisElement n hp).trans_lt (Nat.lt_succ_self n)⟩
  have hnot : basisElement n ∉ hahnPrimeIdeal n := by
    rintro (hz | ⟨hp, hi⟩)
    · exact basisElement_ne_zero n hz
    · rw [leadingIndex_hahnOrder_basisElement] at hi
      exact Nat.lt_irrefl n hi
  exact hnot (heq ▸ hmem)

private theorem hahnPrimeIdeal_zero : hahnPrimeIdeal 0 = ⊥ := by
  ext x
  change x = 0 ∨ (∃ hx : 0 < hahnOrder x, leadingIndex (hahnOrder x) hx < 0) ↔ x = 0
  constructor
  · rintro (rfl | ⟨_, hi⟩)
    · rfl
    · exact False.elim (Nat.not_lt_zero _ hi)
  · exact Or.inl

private theorem hahnOrder_pow (x : hahnValuationRing) (hx : x ≠ 0) (m : ℕ) :
    hahnOrder (x ^ m) = m • hahnOrder x := by
  induction m with
  | zero => simp [hahnOrder]
  | succ m ih =>
    rw [pow_succ, hahnOrder_mul (pow_ne_zero m hx) hx, ih, succ_nsmul]

/-- A prime ideal containing `a` contains `b` if some multiple of `b`'s order dominates `a`'s. -/
private theorem mem_prime_of_hahnOrder_le_nsmul {I : Ideal hahnValuationRing} (hI : I.IsPrime)
    {a b : hahnValuationRing} (ha : a ∈ I) (ha0 : a ≠ 0) (hb0 : b ≠ 0) {k : ℕ}
    (hle : hahnOrder a ≤ k • hahnOrder b) : b ∈ I :=
  hI.mem_of_pow_mem k
    (I.mem_of_dvd (dvd_of_hahnOrder_le ha0 (by rwa [hahnOrder_pow b hb0])) ha)

private theorem exists_nsmul_ge_of_sameLeadingIndex {g h : LexIntegerGroup}
    (hg : 0 < g) (hh : 0 < h)
    (hidx : leadingIndex g hg = leadingIndex h hh) :
    ∃ n : ℕ, 0 < n ∧ g ≤ n • h := by
  let i := leadingIndex g hg
  let a := (ofLex g) i
  let b := (ofLex h) i
  have ha : 0 < a := by simpa [a, i] using (leadingIndex_spec g hg).2
  have hb : 0 < b := by
    simpa [b, i, hidx] using (leadingIndex_spec h hh).2
  let n := a.toNat + 1
  have hna : a < (n : ℤ) := by simp [n, Int.toNat_of_nonneg ha.le]
  have hnpos : 0 < (n : ℤ) := lt_trans ha hna
  have hble : 1 ≤ b := by omega
  have hbn : (n : ℤ) ≤ (n : ℤ) * b := le_mul_of_one_le_right hnpos.le hble
  have hcoord : (ofLex g) i < (ofLex (n • h)) i := by
    change a < (n : ℤ) * b
    exact lt_of_lt_of_le hna hbn
  have hlt : g < n • h := by
    apply Finsupp.Lex.lt_iff.mpr
    refine ⟨i, ?_, hcoord⟩
    intro j hj
    have hgzero := (leadingIndex_spec g hg).1 j hj
    have hhzero := (leadingIndex_spec h hh).1 j (hj.trans_eq hidx)
    change (ofLex g) j = (n : ℕ) • (ofLex h) j
    rw [hgzero, hhzero]
    simp
  exact ⟨n, Nat.succ_pos _, hlt.le⟩

private theorem hahnOrder_pos_of_mem_prime {I : Ideal hahnValuationRing} (hI : I.IsPrime)
    {x : hahnValuationRing} (hx : x ∈ I) (hx0 : x ≠ 0) : 0 < hahnOrder x :=
  hahnOrder_nonunit_pos hx0 fun hu => hI.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hu)

private theorem basisElement_mem_of_mem_prime {I : Ideal hahnValuationRing}
    (hI : I.IsPrime) {x : hahnValuationRing} (hx : x ∈ I) (hx0 : x ≠ 0) :
    basisElement (leadingIndex (hahnOrder x)
      (hahnOrder_nonunit_pos hx0 (by
        intro hu
        exact hI.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hu)))) ∈ I := by
  have hp := hahnOrder_pos_of_mem_prime hI hx hx0
  let i := leadingIndex (hahnOrder x) hp
  obtain ⟨k, -, hle⟩ := exists_nsmul_ge_of_sameLeadingIndex hp (basisValue_pos i)
    (leadingIndex_basisValue i).symm
  exact mem_prime_of_hahnOrder_le_nsmul hI hx hx0 (basisElement_ne_zero i)
    (by rwa [hahnOrder_basisElement])

private theorem mem_prime_of_basisElement_mem {I : Ideal hahnValuationRing}
    (hI : I.IsPrime) {i : ℕ} (hbi : basisElement i ∈ I)
    {x : hahnValuationRing} (hx0 : x ≠ 0) (hp : 0 < hahnOrder x)
    (hidx : leadingIndex (hahnOrder x) hp = i) : x ∈ I := by
  obtain ⟨k, -, hle⟩ := exists_nsmul_ge_of_sameLeadingIndex (basisValue_pos i) hp (by
    rw [leadingIndex_basisValue, hidx])
  exact mem_prime_of_hahnOrder_le_nsmul hI hbi (basisElement_ne_zero i) hx0
    (by rwa [hahnOrder_basisElement])

private theorem basisValue_le_of_le {i j : ℕ} (hji : j ≤ i) : basisValue i ≤ basisValue j := by
  rcases hji.eq_or_lt with rfl | hlt
  · exact le_rfl
  apply le_of_lt
  apply Finsupp.Lex.lt_iff.mpr
  refine ⟨j, fun k hk => ?_, ?_⟩
  · change (Finsupp.single i (1 : ℤ)) k = (Finsupp.single j (1 : ℤ)) k
    rw [Finsupp.single_eq_of_ne (a := i) (a' := k) (b := (1 : ℤ)) (ne_of_lt (lt_trans hk hlt)),
      Finsupp.single_eq_of_ne (a := j) (a' := k) (b := (1 : ℤ)) (ne_of_lt hk)]
  · change (Finsupp.single i (1 : ℤ)) j < (Finsupp.single j (1 : ℤ)) j
    rw [Finsupp.single_eq_of_ne (a := i) (a' := j) (b := (1 : ℤ)) hlt.ne]
    simp

private theorem hahnPrimeIdeal_eq_of_prime (I : Ideal hahnValuationRing)
    (hI : I.IsPrime) : I = IsLocalRing.maximalIdeal hahnValuationRing ∨
      ∃ n, I = hahnPrimeIdeal n := by
  classical
  by_cases hAll : ∀ n, basisElement n ∈ I
  · left
    apply le_antisymm (IsLocalRing.le_maximalIdeal hI.ne_top)
    intro x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    have hp := hahnOrder_nonunit_pos hx0 fun hu => (IsLocalRing.notMem_maximalIdeal).2 hu hx
    exact mem_prime_of_basisElement_mem hI (hAll _) hx0 hp rfl
  · right
    have hex : ∃ n : ℕ, basisElement n ∉ I := not_forall.mp hAll
    let n₀ := Nat.find hex
    have hn₀ : basisElement n₀ ∉ I := Nat.find_spec hex
    refine ⟨n₀, SetLike.ext fun x => ?_⟩
    change x ∈ I ↔ x = 0 ∨ (∃ hx : 0 < hahnOrder x,
      leadingIndex (hahnOrder x) hx < n₀)
    refine ⟨fun hx => ?_, ?_⟩
    · by_cases hx0 : x = 0
      · exact Or.inl hx0
      have hp := hahnOrder_pos_of_mem_prime hI hx hx0
      let i := leadingIndex (hahnOrder x) hp
      have hbi : basisElement i ∈ I := basisElement_mem_of_mem_prime hI hx hx0
      by_cases hlt : i < n₀
      · exact Or.inr ⟨hp, hlt⟩
      have hbn : basisElement i ∣ basisElement n₀ := dvd_of_hahnOrder_le (basisElement_ne_zero i)
        (by simpa only [hahnOrder_basisElement] using basisValue_le_of_le (Nat.le_of_not_gt hlt))
      exact absurd (I.mem_of_dvd hbn hbi) hn₀
    · rintro (rfl | ⟨hp, hi⟩)
      · exact I.zero_mem
      · exact mem_prime_of_basisElement_mem hI
          (not_not.mp (Nat.find_min hex hi)) (ne_zero_of_hahnOrder_pos hp) hp rfl

/-- There is a valuation ring whose spectrum is a countable strictly increasing chain
of prime ideals, with one further maximal ideal above all of them. -/
@[stacks 01IY "valuation ring with the specified prime spectrum"]
theorem exists_valuationRing_with_spectrum_chain :
    ∃ (R : Type u) (ring : CommRing R),
      letI : CommRing R := ring
      ∃ (domain : IsDomain R),
        letI : IsDomain R := domain
        ∃ (localRing : IsLocalRing R),
          letI : IsLocalRing R := localRing
          IsValuationRing R ∧
            ∃ p : ℕ → PrimeSpectrum R,
              ((p 0).asIdeal = ⊥) ∧
                (∀ n, (p n).asIdeal < (p (n + 1)).asIdeal) ∧
                (∀ q : PrimeSpectrum R,
                  (q = IsLocalRing.closedPoint R) ∨ (∃ n, q = p n)) := by
  let R : Type u := hahnValuationRing
  let : CommRing R := inferInstance
  let : IsDomain R := inferInstance
  let : IsLocalRing R := inferInstance
  refine ⟨R, inferInstance, inferInstance, inferInstance,
    valuationSubring_isValuationRing hahnValuation, ?_⟩
  refine ⟨hahnPrimeSpectrumPoint, hahnPrimeIdeal_zero, hahnPrimeIdeal_chain_strict, ?_⟩
  · intro q
    rcases hahnPrimeIdeal_eq_of_prime q.asIdeal q.2 with hmax | ⟨n, hEq⟩
    · left
      apply PrimeSpectrum.ext
      simpa [IsLocalRing.closedPoint] using hmax
    · right
      refine ⟨n, ?_⟩
      apply PrimeSpectrum.ext
      simpa [hahnPrimeSpectrumPoint] using hEq

private theorem succ_ne_closedPoint {R : Type*} [CommRing R] [IsLocalRing R]
    {p : ℕ → PrimeSpectrum R} (hchain : ∀ n, (p n).asIdeal < (p (n + 1)).asIdeal) (n : ℕ) :
    p (n + 1) ≠ IsLocalRing.closedPoint R := by
  intro h
  have hle : (p (n + 2)).asIdeal ≤ (p (n + 1)).asIdeal := by
    rw [h]
    exact IsLocalRing.le_maximalIdeal (p (n + 2)).2.1
  exact (hchain (n + 1)).not_ge hle

/-- Removing the unique closed point from a local spectrum with the indicated
unbounded chain of other primes gives an open subscheme without closed points. -/
@[stacks 01IY "the punctured spectrum has no closed points"]
theorem puncturedSpectrum_no_closed_points
    (R : Type u) [CommRing R] [IsLocalRing R]
    (p : ℕ → PrimeSpectrum R)
    (hchain : ∀ n, (p n).asIdeal < (p (n + 1)).asIdeal)
    (hexhaust : ∀ q : PrimeSpectrum R,
      (q = IsLocalRing.closedPoint R) ∨ (∃ n, q = p n)) :
    ∀ x : Scheme.Opens.toScheme
      (⟨({IsLocalRing.closedPoint R} : Set (PrimeSpectrum R))ᶜ,
        (IsLocalRing.isClosed_singleton_closedPoint R).isOpen_compl⟩ :
        (Spec (.of R)).Opens),
      ¬ IsClosed ({x} : Set _) := by
  intro x hx
  obtain ⟨n, hn⟩ := (hexhaust x.1).resolve_left x.2
  let y : Scheme.Opens.toScheme
      (⟨({IsLocalRing.closedPoint R} : Set (PrimeSpectrum R))ᶜ,
        (IsLocalRing.isClosed_singleton_closedPoint R).isOpen_compl⟩ :
        (Spec (.of R)).Opens) := ⟨p (n + 1), succ_ne_closedPoint hchain n⟩
  have hspec : x ⤳ y := by
    apply (subtype_specializes_iff x y).2
    rw [hn]
    exact (PrimeSpectrum.le_iff_specializes (p n) (p (n + 1))).mp (hchain n).le
  have hyeq : y = x := by simpa [hx.closure_eq] using specializes_iff_mem_closure.mp hspec
  have hxy : (p (n + 1)).asIdeal = (p n).asIdeal := by
    simpa [y, hn] using congrArg (fun z => z.1.asIdeal) hyeq
  exact (hchain n).not_ge hxy.le

/-- A nonempty scheme may have no closed points. -/
@[stacks 01IY "existence of a scheme without closed points"]
theorem exists_scheme_without_closed_points :
    ∃ X : Scheme.{u}, Nonempty X ∧ ∀ x : X, ¬ IsClosed ({x} : Set X) := by
  obtain ⟨R, ring, domain, localRing, hval, p, hbot, hchain, hexhaust⟩ :=
    exists_valuationRing_with_spectrum_chain.{u}
  let : CommRing R := ring
  let : IsDomain R := domain
  let : IsLocalRing R := localRing
  let U : (Spec (.of R)).Opens :=
    ⟨({IsLocalRing.closedPoint R} : Set (PrimeSpectrum R))ᶜ,
      (IsLocalRing.isClosed_singleton_closedPoint R).isOpen_compl⟩
  exact ⟨U.toScheme, ⟨⟨p 1, succ_ne_closedPoint hchain 0⟩⟩,
    puncturedSpectrum_no_closed_points R p hchain hexhaust⟩

end AlgebraicGeometry

end
