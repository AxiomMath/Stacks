module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.LinearAlgebra.DiagonallyDominant
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Defs
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Genus
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.FourVertices
public import Mathlib
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Proper subgraphs of type `D₅`

In a numerical type with more than five components, a `D₅` configuration of
minus-two indices forces all five weights to agree, and bounds the multiplicity
of each component of the configuration by a combination of the multiplicities of
its neighbours.

## Main results

* `AlgebraicGeometry.NumericalType.exists_weight_eq_d5_of_isMinusTwoIndex`.
* `AlgebraicGeometry.NumericalType.multiplicity_le_of_d5_at_zero` through
  `AlgebraicGeometry.NumericalType.multiplicity_le_of_d5_at_four`.

## References

* [Stacks Project, Tag 0C87](https://stacks.math.columbia.edu/tag/0C87)
-/

@[expose] public section

open Matrix

namespace AlgebraicGeometry.NumericalType



private lemma supported_quadratic_lt_zero (T : NumericalType)
    (v : Fin 5 ↪ Fin T.componentCount) (hn : 5 < T.componentCount)
    (x : Fin T.componentCount → ℚ)
    (hsupport : ∀ z, z ∉ Set.range v → x z = 0)
    (hnonzero : ∃ z, x z ≠ 0) :
    x ⬝ᵥ ((fun a b => (T.intersection a b : ℚ)) *ᵥ x) < 0 := by
  classical
  let A : Matrix (Fin T.componentCount) (Fin T.componentCount) ℚ :=
    fun a b => (T.intersection a b : ℚ)
  let m : Fin T.componentCount → ℚ := fun a => (T.multiplicity a : ℚ)
  have hAsymm : A.IsSymm := by
    ext a b
    change (T.intersection b a : ℚ) = (T.intersection a b : ℚ)
    exact_mod_cast (T.intersection_symm a b).symm
  have hAoff : ∀ a b, a ≠ b → 0 ≤ A a b := by
    intro a b hab
    change 0 ≤ (T.intersection a b : ℚ)
    exact_mod_cast T.intersection_nonneg a b hab
  have hmpos : ∀ a, 0 < m a := by
    intro a
    change 0 < (T.multiplicity a : ℚ)
    exact_mod_cast T.multiplicity_pos a
  have hAm : A *ᵥ m = 0 := by
    ext a
    change (∑ b, (T.intersection a b : ℚ) * (T.multiplicity b : ℚ)) = 0
    exact_mod_cast T.intersection_mul_multiplicity a
  have hconnected : ∀ I : Set (Fin T.componentCount), I.Nonempty → I ≠ Set.univ →
      ¬ ∀ a ∈ I, ∀ b ∉ I, A a b = 0 := by
    intro I hIne hIproper hcut
    refine T.connected ⟨I, hIne, hIproper, fun a ha b hb => ?_⟩
    have hab : (T.intersection a b : ℚ) = 0 := hcut a ha b hb
    exact_mod_cast hab
  refine lt_of_le_of_ne
    (dotProduct_mulVec_nonpos_of_positive_kernel hAsymm hAoff hmpos hAm x) fun hzero => ?_
  obtain ⟨q, hxq⟩ :=
    (dotProduct_mulVec_eq_zero_iff_of_positive_kernel
      hAsymm hAoff hmpos hAm hconnected (x := x)).mp hzero
  obtain ⟨z, hz⟩ : ∃ z : Fin T.componentCount, z ∉ Set.range v := by
    by_contra h
    have hsurj : Function.Surjective v := fun z => not_not.mp fun hz => h ⟨z, hz⟩
    have hcard := Fintype.card_congr (Equiv.ofBijective v ⟨v.injective, hsurj⟩)
    simp only [Fintype.card_fin] at hcard
    omega
  have hqzero : q = 0 := by
    have hzq := congrFun hxq z
    rw [hsupport z hz] at hzq
    change 0 = q * m z at hzq
    nlinarith [hmpos z]
  obtain ⟨a, ha⟩ := hnonzero
  exact ha (by simpa [hqzero] using congrFun hxq a)

private lemma sum_multiplicity_le_of_intersection_eq (T : NumericalType)
    (i : Fin T.componentCount) (neighbors : Finset (Fin T.componentCount)) (w : ℤ)
    (hw : 0 < w) (hdiag : T.intersection i i = -2 * w)
    (hneighbors : ∀ j ∈ neighbors, T.intersection i j = w)
    (hnotmem : i ∉ neighbors) :
    (∑ j ∈ neighbors, T.multiplicity j) ≤ 2 * T.multiplicity i := by
  classical
  let f : Fin T.componentCount → ℤ := fun j =>
    T.intersection i j * T.multiplicity j
  have hrow := T.intersection_mul_multiplicity i
  change (∑ j, f j) = 0 at hrow
  rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ i)] at hrow
  have hterms_nonneg : ∀ j ∈ Finset.univ.erase i, 0 ≤ f j := by
    intro j hj
    have hne : i ≠ j := (Finset.mem_erase.mp hj).1.symm
    exact mul_nonneg (T.intersection_nonneg i j hne) (le_of_lt (T.multiplicity_pos j))
  have hsum_eq : (∑ j ∈ Finset.univ.erase i, f j) = 2 * w * T.multiplicity i := by
    dsimp [f] at hrow
    rw [hdiag] at hrow
    nlinarith
  have hsubset : neighbors ⊆ Finset.univ.erase i := fun j hj =>
    Finset.mem_erase.mpr ⟨fun hji => hnotmem (hji ▸ hj), Finset.mem_univ j⟩
  have hneighbor_sum : (∑ j ∈ neighbors, f j) =
      w * (∑ j ∈ neighbors, T.multiplicity j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp [f, hneighbors j hj]
  refine (mul_le_mul_iff_of_pos_left hw).mp ?_
  calc
    w * (∑ j ∈ neighbors, T.multiplicity j) = ∑ j ∈ neighbors, f j := hneighbor_sum.symm
    _ ≤ ∑ j ∈ Finset.univ.erase i, f j :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset fun j hj _ => hterms_nonneg j hj
    _ = 2 * w * T.multiplicity i := hsum_eq
    _ = w * (2 * T.multiplicity i) := by ring

/-- Two positive integers with product below `2` are both `1`. Pulled out of
`exists_weight_eq_d5_of_isMinusTwoIndex`, where the two `nlinarith` calls proving
it cost about 3.7 seconds each against that proof's full context; in isolation
they are immediate. -/
private lemma eq_one_and_eq_one_of_mul_lt_two {a b : ℤ} (ha : 0 < a) (hb : 0 < b)
    (h : a * b < 2) : a = 1 ∧ b = 1 := by
  constructor
  · by_contra hne
    have h2 : 2 ≤ a := by omega
    nlinarith
  · by_contra hne
    have h2 : 2 ≤ b := by omega
    nlinarith

/-- A positive integer that factors a positive integer is itself positive. Pulled
out of `exists_weight_eq_d5_of_isMinusTwoIndex`, where proving it inline for the
two cofactors cost about 3 seconds each against that proof's full context. -/
private lemma pos_of_mul_eq_pos {p a q : ℤ} (hp : 0 < p) (hq : 0 < q)
    (h : q = p * a) : 0 < a :=
  pos_of_mul_pos_right (hq.trans_eq h) hp.le

/-- A nonnegative multiple of `w` is either `0` or at least `w`. -/
private lemma eq_zero_or_le_of_dvd_of_nonneg {w r : ℤ} (hw : 0 < w) (hr : 0 ≤ r)
    (hdvd : w ∣ r) : r = 0 ∨ w ≤ r := by
  obtain ⟨c, hc⟩ := hdvd
  rcases lt_trichotomy c 0 with hlt | heq | hgt
  · exact absurd hr (by nlinarith)
  · exact Or.inl (by rw [hc, heq, mul_zero])
  · refine Or.inr ?_
    calc w = w * 1 := (mul_one w).symm
      _ ≤ w * c := mul_le_mul_of_nonneg_left (by omega) hw.le
      _ = r := hc.symm

/-- The three intersection numbers from the extra component of a `D5` diagram to
the three components it is not joined to all vanish, given that the weighted sum
`2r₂ + r₃ + r₄` is below the common weight and each is a multiple of it.

This is the one argument that the three branches `r₂ = 0`, `r₃ = 0`, `r₄ = 0` of
`exists_weight_eq_d5_of_isMinusTwoIndex` share; factoring it out avoids three copies of the
argument, each closing with its own `nlinarith` over the full context. -/
private lemma eq_zero_of_dvd_of_weighted_sum_lt {w r₂ r₃ r₄ : ℤ} (hw : 0 < w)
    (h₂ : 0 ≤ r₂) (h₃ : 0 ≤ r₃) (h₄ : 0 ≤ r₄)
    (d₂ : w ∣ r₂) (d₃ : w ∣ r₃) (d₄ : w ∣ r₄)
    (hsum : 2 * r₂ + r₃ + r₄ < w) : r₂ = 0 ∧ r₃ = 0 ∧ r₄ = 0 := by
  rcases eq_zero_or_le_of_dvd_of_nonneg hw h₂ d₂ with e₂ | e₂
  · rcases eq_zero_or_le_of_dvd_of_nonneg hw h₃ d₃ with e₃ | e₃
    · rcases eq_zero_or_le_of_dvd_of_nonneg hw h₄ d₄ with e₄ | e₄
      · exact ⟨e₂, e₃, e₄⟩
      · omega
    · omega
  · omega

/-- Five minus-two indices forming the edges of a `D5` diagram in a numerical
type with more than five components have equal weights, the standard `D5`
intersection matrix. -/
@[stacks 0C87 "weights and intersections"]
public lemma exists_weight_eq_d5_of_isMinusTwoIndex (T : NumericalType)
    (hn : 5 < T.componentCount) (v : Fin 5 ↪ Fin T.componentCount)
    (hminus : ∀ r, IsMinusTwoIndex T (v r))
    (h₀₁ : T.intersection (v 0) (v 1) ≠ 0)
    (h₁₂ : T.intersection (v 1) (v 2) ≠ 0)
    (h₂₃ : T.intersection (v 2) (v 3) ≠ 0)
    (h₂₄ : T.intersection (v 2) (v 4) ≠ 0) :
    ∃ w : ℤ,
      (fun r ↦ T.weight (v r)) = ![w, w, w, w, w] ∧
      (fun r s ↦ T.intersection (v r) (v s)) =
        !![-2 * w, w, 0, 0, 0;
           w, -2 * w, w, 0, 0;
           0, w, -2 * w, w, w;
           0, 0, w, -2 * w, 0;
           0, 0, w, 0, -2 * w] := by
  classical
  have hvne (r s : Fin 5) (hrs : r ≠ s) : v r ≠ v s := v.injective.ne hrs
  have h₂₁ : T.intersection (v 2) (v 1) ≠ 0 := by rwa [T.intersection_symm]
  obtain ⟨w, hw, hw₂, hw₁, hw₃, hw₄, hd₂₂, hd₁₁, hd₃₃, hd₄₄,
    he₂₁, he₁₂, he₂₃, he₃₂, he₂₄, he₄₂, he₁₃, he₃₁, he₁₄, he₄₁,
    he₃₄, he₄₃, -, -, -, -, -, -, -⟩ :=
    exists_d4_configuration_of_four_isMinusTwoIndex T (by omega)
      (v 2) (v 1) (v 3) (v 4)
      (hvne 2 1 (by decide)) (hvne 2 3 (by decide)) (hvne 2 4 (by decide))
      (hvne 1 3 (by decide)) (hvne 1 4 (by decide)) (hvne 3 4 (by decide))
      (hminus 2) (hminus 1) (hminus 3) (hminus 4)
      h₂₁ h₂₃ h₂₄
  let p : ℤ := T.weight (v 0)
  let q : ℤ := T.intersection (v 0) (v 1)
  let r₂ : ℤ := T.intersection (v 0) (v 2)
  let r₃ : ℤ := T.intersection (v 0) (v 3)
  let r₄ : ℤ := T.intersection (v 0) (v 4)
  have hp : 0 < p := T.weight_pos (v 0)
  have hq : 0 < q :=
    lt_of_le_of_ne (T.intersection_nonneg (v 0) (v 1) (hvne 0 1 (by decide))) (Ne.symm h₀₁)
  have hr₂ : 0 ≤ r₂ := T.intersection_nonneg (v 0) (v 2) (hvne 0 2 (by decide))
  have hr₃ : 0 ≤ r₃ := T.intersection_nonneg (v 0) (v 3) (hvne 0 3 (by decide))
  have hr₄ : 0 ≤ r₄ := T.intersection_nonneg (v 0) (v 4) (hvne 0 4 (by decide))
  have hd₀₀ : T.intersection (v 0) (v 0) = -2 * p := (hminus 0).2
  let A : Matrix (Fin T.componentCount) (Fin T.componentCount) ℚ :=
    fun a b => (T.intersection a b : ℚ)
  let x : Fin T.componentCount → ℚ := fun a =>
    if a = v 0 then 2 * (w : ℚ) else
    if a = v 1 then 2 * (q : ℚ) else
    if a = v 2 then 2 * (q : ℚ) else
    if a = v 3 then (q : ℚ) else if a = v 4 then (q : ℚ) else 0
  have hsupport : ∀ z, z ∉ Set.range v → x z = 0 := by
    intro z hz
    have hz0 : z ≠ v 0 := by intro h; exact hz ⟨0, h.symm⟩
    have hz1 : z ≠ v 1 := by intro h; exact hz ⟨1, h.symm⟩
    have hz2 : z ≠ v 2 := by intro h; exact hz ⟨2, h.symm⟩
    have hz3 : z ≠ v 3 := by intro h; exact hz ⟨3, h.symm⟩
    have hz4 : z ≠ v 4 := by intro h; exact hz ⟨4, h.symm⟩
    simp [x, hz0, hz1, hz2, hz3, hz4]
  have hxnonzero : ∃ z, x z ≠ 0 := by
    refine ⟨v 0, ?_⟩
    have hval : x (v 0) = 2 * (w : ℚ) := by simp [x]
    rw [hval]
    positivity
  have hquadlt : x ⬝ᵥ (A *ᵥ x) < 0 := by
    simpa [A] using supported_quadratic_lt_zero T v hn x hsupport hxnonzero
  have hformula : x ⬝ᵥ (A *ᵥ x) =
      4 * (w : ℚ) * ((q : ℚ)^2 - 2 * (p : ℚ) * (w : ℚ) +
        2 * (q : ℚ) * (r₂ : ℚ) + (q : ℚ) * (r₃ : ℚ) + (q : ℚ) * (r₄ : ℚ)) := by
    calc
      x ⬝ᵥ (A *ᵥ x) =
          (2 * (w : ℚ)) *
              (A (v 0) (v 0) * (2 * (w : ℚ)) +
                A (v 0) (v 1) * (2 * (q : ℚ)) +
                A (v 0) (v 2) * (2 * (q : ℚ)) +
                A (v 0) (v 3) * (q : ℚ) + A (v 0) (v 4) * (q : ℚ)) +
            (2 * (q : ℚ)) *
              (A (v 1) (v 0) * (2 * (w : ℚ)) +
                A (v 1) (v 1) * (2 * (q : ℚ)) +
                A (v 1) (v 2) * (2 * (q : ℚ)) +
                A (v 1) (v 3) * (q : ℚ) + A (v 1) (v 4) * (q : ℚ)) +
            (2 * (q : ℚ)) *
              (A (v 2) (v 0) * (2 * (w : ℚ)) +
                A (v 2) (v 1) * (2 * (q : ℚ)) +
                A (v 2) (v 2) * (2 * (q : ℚ)) +
                A (v 2) (v 3) * (q : ℚ) + A (v 2) (v 4) * (q : ℚ)) +
            (q : ℚ) *
              (A (v 3) (v 0) * (2 * (w : ℚ)) +
                A (v 3) (v 1) * (2 * (q : ℚ)) +
                A (v 3) (v 2) * (2 * (q : ℚ)) +
                A (v 3) (v 3) * (q : ℚ) + A (v 3) (v 4) * (q : ℚ)) +
            (q : ℚ) *
              (A (v 4) (v 0) * (2 * (w : ℚ)) +
                A (v 4) (v 1) * (2 * (q : ℚ)) +
                A (v 4) (v 2) * (2 * (q : ℚ)) +
                A (v 4) (v 3) * (q : ℚ) + A (v 4) (v 4) * (q : ℚ)) := by
        simpa [x] using five_coordinate_quadratic A (v 0) (v 1) (v 2) (v 3) (v 4)
          (hvne 0 1 (by decide)) (hvne 0 2 (by decide)) (hvne 0 3 (by decide))
          (hvne 0 4 (by decide)) (hvne 1 2 (by decide)) (hvne 1 3 (by decide))
          (hvne 1 4 (by decide)) (hvne 2 3 (by decide)) (hvne 2 4 (by decide))
          (hvne 3 4 (by decide)) (2 * (w : ℚ)) (2 * (q : ℚ)) (2 * (q : ℚ))
          (q : ℚ) (q : ℚ)
      _ = _ := by
        simp [A, p, q, r₂, r₃, r₄, hd₀₀, hd₁₁, hd₂₂, hd₃₃, hd₄₄,
          he₂₁, he₁₂, he₂₃, he₃₂, he₂₄, he₄₂, he₁₃, he₃₁, he₁₄, he₄₁,
          he₃₄, he₄₃, T.intersection_symm]
        ring
  have hwQ : 0 < (w : ℚ) := by exact_mod_cast hw
  have hbracket : (q : ℚ)^2 - 2 * (p : ℚ) * (w : ℚ) +
      2 * (q : ℚ) * (r₂ : ℚ) + (q : ℚ) * (r₃ : ℚ) +
      (q : ℚ) * (r₄ : ℚ) < 0 := by
    have hpos : 0 < (4 : ℚ) * (w : ℚ) := by positivity
    rw [hformula] at hquadlt
    rcases (mul_neg_iff.mp hquadlt) with ⟨_, hneg⟩ | ⟨hneg, _⟩
    · exact hneg
    · linarith
  have hbaseQ : (q : ℚ)^2 < 2 * (p : ℚ) * (w : ℚ) := by
    have hrest : 0 ≤ 2 * (q : ℚ) * (r₂ : ℚ) +
        (q : ℚ) * (r₃ : ℚ) + (q : ℚ) * (r₄ : ℚ) := by positivity
    linarith
  have hbase : q^2 < 2 * p * w := by exact_mod_cast hbaseQ
  have hpDvd : p ∣ q := T.weight_dvd_intersection (v 0) (v 1)
  have hwDvd : w ∣ q := by
    have h := T.weight_dvd_intersection (v 1) (v 0)
    rwa [hw₁, T.intersection_symm (v 1) (v 0)] at h
  obtain ⟨a, ha⟩ := hpDvd
  obtain ⟨b, hb⟩ := hwDvd
  have haPos : 0 < a := pos_of_mul_eq_pos hp hq ha
  have hbPos : 0 < b := pos_of_mul_eq_pos hw hq hb
  have habFactor : q^2 = p * w * (a * b) := by
    calc
      q^2 = (p * a) * q := by rw [ha]; ring
      _ = (p * a) * (w * b) := by rw [hb]
      _ = p * w * (a * b) := by ring
  have habLt : a * b < 2 := by
    apply (mul_lt_mul_iff_of_pos_left (mul_pos hp hw)).mp
    calc
      p * w * (a * b) = q^2 := habFactor.symm
      _ < 2 * p * w := hbase
      _ = p * w * 2 := by ring
  obtain ⟨haOne, hbOne⟩ := eq_one_and_eq_one_of_mul_lt_two haPos hbPos habLt
  rw [haOne, mul_one] at ha
  rw [hbOne, mul_one] at hb
  have hpw : p = w := ha.symm.trans hb
  have hqw : q = w := hb
  have he₀₁ : T.intersection (v 0) (v 1) = w := by change q = w; exact hqw
  have he₁₀ : T.intersection (v 1) (v 0) = w := by
    rw [T.intersection_symm]
    exact he₀₁
  have hdvd (s : Fin 5) : w ∣ T.intersection (v 0) (v s) := by
    have h : p ∣ T.intersection (v 0) (v s) := T.weight_dvd_intersection (v 0) (v s)
    rwa [hpw] at h
  have hsum : 2 * r₂ + r₃ + r₄ < w := by
    rw [hpw, hqw] at hbracket
    have hwQ' : (0 : ℚ) < (w : ℚ) := by exact_mod_cast hw
    have hmul : (w : ℚ) * (2 * (r₂ : ℚ) + (r₃ : ℚ) + (r₄ : ℚ)) <
        (w : ℚ) * (w : ℚ) := by linarith
    exact_mod_cast lt_of_mul_lt_mul_left hmul hwQ'.le
  obtain ⟨hr₂zero, hr₃zero, hr₄zero⟩ :=
    eq_zero_of_dvd_of_weighted_sum_lt hw hr₂ hr₃ hr₄ (hdvd 2) (hdvd 3) (hdvd 4) hsum
  refine ⟨w, ?_, ?_⟩
  · funext r
    fin_cases r <;> simp [p, hpw, hw₁, hw₂, hw₃, hw₄]
  · funext r s
    fin_cases r <;> fin_cases s <;>
      simp [p, hpw, q, hqw, r₂, hr₂zero, r₃, hr₃zero, r₄, hr₄zero,
        hd₀₀, hd₁₁, hd₂₂, hd₃₃, hd₄₄, he₂₁, he₁₂, he₂₃, he₃₂,
        he₂₄, he₄₂, he₁₃, he₃₁, he₁₄, he₄₁, he₃₄, he₄₃,
        he₁₀, T.intersection_symm]

/-- The `D5` intersection matrix of `exists_weight_eq_d5_of_isMinusTwoIndex`, with positive
weight. -/
private lemma exists_pos_weight_matrix_d5 (T : NumericalType)
    (hn : 5 < T.componentCount) (v : Fin 5 ↪ Fin T.componentCount)
    (hminus : ∀ r, IsMinusTwoIndex T (v r))
    (h₀₁ : T.intersection (v 0) (v 1) ≠ 0)
    (h₁₂ : T.intersection (v 1) (v 2) ≠ 0)
    (h₂₃ : T.intersection (v 2) (v 3) ≠ 0)
    (h₂₄ : T.intersection (v 2) (v 4) ≠ 0) :
    ∃ w : ℤ, 0 < w ∧
      (fun r s ↦ T.intersection (v r) (v s)) =
        !![-2 * w, w, 0, 0, 0;
           w, -2 * w, w, 0, 0;
           0, w, -2 * w, w, w;
           0, 0, w, -2 * w, 0;
           0, 0, w, 0, -2 * w] := by
  obtain ⟨w, hweights, hmatrix⟩ := exists_weight_eq_d5_of_isMinusTwoIndex
    T hn v hminus h₀₁ h₁₂ h₂₃ h₂₄
  exact ⟨w, (T.weight_pos (v 0)).trans_eq (by simpa using congrFun hweights (0 : Fin 5)),
    hmatrix⟩

/-- The first multiplicity inequality for a proper `D5` subgraph. -/
@[stacks 0C87 "first multiplicity inequality"]
public lemma multiplicity_le_of_d5_at_zero (T : NumericalType)
    (hn : 5 < T.componentCount) (v : Fin 5 ↪ Fin T.componentCount)
    (hminus : ∀ r, IsMinusTwoIndex T (v r))
    (h₀₁ : T.intersection (v 0) (v 1) ≠ 0)
    (h₁₂ : T.intersection (v 1) (v 2) ≠ 0)
    (h₂₃ : T.intersection (v 2) (v 3) ≠ 0)
    (h₂₄ : T.intersection (v 2) (v 4) ≠ 0) :
    T.multiplicity (v 1) ≤ 2 * T.multiplicity (v 0) := by
  obtain ⟨w, hw, hmatrix⟩ := exists_pos_weight_matrix_d5 T hn v hminus h₀₁ h₁₂ h₂₃ h₂₄
  have hdiag : T.intersection (v 0) (v 0) = -2 * w := by
    simpa using congrFun (congrFun hmatrix (0 : Fin 5)) 0
  have hedge : T.intersection (v 0) (v 1) = w := by
    simpa using congrFun (congrFun hmatrix (0 : Fin 5)) 1
  simpa using sum_multiplicity_le_of_intersection_eq T (v 0) {v 1} w hw hdiag
    (by simp [hedge])
    (by simp [v.injective.ne (by decide : (0 : Fin 5) ≠ 1)])

/-- The second multiplicity inequality for a proper `D5` subgraph. -/
@[stacks 0C87 "second multiplicity inequality"]
public lemma multiplicity_le_of_d5_at_one (T : NumericalType)
    (hn : 5 < T.componentCount) (v : Fin 5 ↪ Fin T.componentCount)
    (hminus : ∀ r, IsMinusTwoIndex T (v r))
    (h₀₁ : T.intersection (v 0) (v 1) ≠ 0)
    (h₁₂ : T.intersection (v 1) (v 2) ≠ 0)
    (h₂₃ : T.intersection (v 2) (v 3) ≠ 0)
    (h₂₄ : T.intersection (v 2) (v 4) ≠ 0) :
    T.multiplicity (v 0) + T.multiplicity (v 2) ≤
      2 * T.multiplicity (v 1) := by
  obtain ⟨w, hw, hmatrix⟩ := exists_pos_weight_matrix_d5 T hn v hminus h₀₁ h₁₂ h₂₃ h₂₄
  have hdiag : T.intersection (v 1) (v 1) = -2 * w := by
    simpa using congrFun (congrFun hmatrix (1 : Fin 5)) 1
  have hedge₀ : T.intersection (v 1) (v 0) = w := by
    simpa using congrFun (congrFun hmatrix (1 : Fin 5)) 0
  have hedge₂ : T.intersection (v 1) (v 2) = w := by
    simpa using congrFun (congrFun hmatrix (1 : Fin 5)) 2
  have hbound := sum_multiplicity_le_of_intersection_eq T (v 1) {v 0, v 2} w hw hdiag
    (by simp [hedge₀, hedge₂])
    (by simp [v.injective.ne (by decide : (1 : Fin 5) ≠ 0),
      v.injective.ne (by decide : (1 : Fin 5) ≠ 2)])
  simpa [v.injective.ne (by decide : (0 : Fin 5) ≠ 2)] using hbound

/-- The central multiplicity inequality for a proper `D5` subgraph. -/
@[stacks 0C87 "third multiplicity inequality"]
public lemma multiplicity_le_of_d5_at_two (T : NumericalType)
    (hn : 5 < T.componentCount) (v : Fin 5 ↪ Fin T.componentCount)
    (hminus : ∀ r, IsMinusTwoIndex T (v r))
    (h₀₁ : T.intersection (v 0) (v 1) ≠ 0)
    (h₁₂ : T.intersection (v 1) (v 2) ≠ 0)
    (h₂₃ : T.intersection (v 2) (v 3) ≠ 0)
    (h₂₄ : T.intersection (v 2) (v 4) ≠ 0) :
    T.multiplicity (v 1) + T.multiplicity (v 3) + T.multiplicity (v 4) ≤
      2 * T.multiplicity (v 2) := by
  obtain ⟨w, hw, hmatrix⟩ := exists_pos_weight_matrix_d5 T hn v hminus h₀₁ h₁₂ h₂₃ h₂₄
  have hdiag : T.intersection (v 2) (v 2) = -2 * w := by
    simpa using congrFun (congrFun hmatrix (2 : Fin 5)) 2
  have hedge₁ : T.intersection (v 2) (v 1) = w := by
    simpa using congrFun (congrFun hmatrix (2 : Fin 5)) 1
  have hedge₃ : T.intersection (v 2) (v 3) = w := by
    simpa using congrFun (congrFun hmatrix (2 : Fin 5)) 3
  have hedge₄ : T.intersection (v 2) (v 4) = w := by
    simpa using congrFun (congrFun hmatrix (2 : Fin 5)) 4
  have hbound := sum_multiplicity_le_of_intersection_eq T (v 2) {v 1, v 3, v 4} w hw hdiag
    (by simp [hedge₁, hedge₃, hedge₄])
    (by simp [v.injective.ne (by decide : (2 : Fin 5) ≠ 1),
      v.injective.ne (by decide : (2 : Fin 5) ≠ 3),
      v.injective.ne (by decide : (2 : Fin 5) ≠ 4)])
  simpa [add_assoc, v.injective.ne (by decide : (1 : Fin 5) ≠ 3),
    v.injective.ne (by decide : (1 : Fin 5) ≠ 4),
    v.injective.ne (by decide : (3 : Fin 5) ≠ 4)] using hbound

/-- The fourth multiplicity inequality for a proper `D5` subgraph. -/
@[stacks 0C87 "fourth multiplicity inequality"]
public lemma multiplicity_le_of_d5_at_three (T : NumericalType)
    (hn : 5 < T.componentCount) (v : Fin 5 ↪ Fin T.componentCount)
    (hminus : ∀ r, IsMinusTwoIndex T (v r))
    (h₀₁ : T.intersection (v 0) (v 1) ≠ 0)
    (h₁₂ : T.intersection (v 1) (v 2) ≠ 0)
    (h₂₃ : T.intersection (v 2) (v 3) ≠ 0)
    (h₂₄ : T.intersection (v 2) (v 4) ≠ 0) :
    T.multiplicity (v 2) ≤ 2 * T.multiplicity (v 3) := by
  obtain ⟨w, hw, hmatrix⟩ := exists_pos_weight_matrix_d5 T hn v hminus h₀₁ h₁₂ h₂₃ h₂₄
  have hdiag : T.intersection (v 3) (v 3) = -2 * w := by
    simpa using congrFun (congrFun hmatrix (3 : Fin 5)) 3
  have hedge : T.intersection (v 3) (v 2) = w := by
    simpa using congrFun (congrFun hmatrix (3 : Fin 5)) 2
  simpa using sum_multiplicity_le_of_intersection_eq T (v 3) {v 2} w hw hdiag
    (by simp [hedge])
    (by simp [v.injective.ne (by decide : (3 : Fin 5) ≠ 2)])

/-- The fifth multiplicity inequality for a proper `D5` subgraph. -/
@[stacks 0C87 "fifth multiplicity inequality"]
public lemma multiplicity_le_of_d5_at_four (T : NumericalType)
    (hn : 5 < T.componentCount) (v : Fin 5 ↪ Fin T.componentCount)
    (hminus : ∀ r, IsMinusTwoIndex T (v r))
    (h₀₁ : T.intersection (v 0) (v 1) ≠ 0)
    (h₁₂ : T.intersection (v 1) (v 2) ≠ 0)
    (h₂₃ : T.intersection (v 2) (v 3) ≠ 0)
    (h₂₄ : T.intersection (v 2) (v 4) ≠ 0) :
    T.multiplicity (v 2) ≤ 2 * T.multiplicity (v 4) := by
  obtain ⟨w, hw, hmatrix⟩ := exists_pos_weight_matrix_d5 T hn v hminus h₀₁ h₁₂ h₂₃ h₂₄
  have hdiag : T.intersection (v 4) (v 4) = -2 * w := by
    simpa using congrFun (congrFun hmatrix (4 : Fin 5)) 4
  have hedge : T.intersection (v 4) (v 2) = w := by
    simpa using congrFun (congrFun hmatrix (4 : Fin 5)) 2
  simpa using sum_multiplicity_le_of_intersection_eq T (v 4) {v 2} w hw hdiag
    (by simp [hedge])
    (by simp [v.injective.ne (by decide : (4 : Fin 5) ≠ 2)])

end AlgebraicGeometry.NumericalType
