module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.FiveChain.WeightShapes

/-!
# Five-vertex chains: configurations

The quadratic form of a numerical type on vectors supported on five indices,
the row-balance bound at a minus-two index, the ordered configurations of type
`A₅`, `C₅` and `B₅`, and the five-vertex path matrices at these weight
profiles.

## Main definitions

* `AlgebraicGeometry.NumericalType.IsA5Configuration`,
  `AlgebraicGeometry.NumericalType.IsC5Configuration` and
  `AlgebraicGeometry.NumericalType.IsB5Configuration`.
-/

@[expose] public section

open Matrix

namespace AlgebraicGeometry.NumericalType

theorem dotProduct_mulVec_five_formula {α : Type*} [Fintype α]
    [DecidableEq α] (A : Matrix α α ℚ) (hA : A.IsSymm)
    (a b c d e : α) (_hab : a ≠ b) (_hac : a ≠ c) (_had : a ≠ d)
    (_hae : a ≠ e) (_hbc : b ≠ c) (_hbd : b ≠ d) (_hbe : b ≠ e)
    (_hcd : c ≠ d) (_hce : c ≠ e) (_hde : d ≠ e)
    (c0 c1 c2 c3 c4 : ℚ) :
    let x : α → ℚ := fun s =>
      (if s = a then c0 else 0) + (if s = b then c1 else 0) +
        (if s = c then c2 else 0) + (if s = d then c3 else 0) +
        (if s = e then c4 else 0)
    x ⬝ᵥ (A *ᵥ x) =
      c0*c0*A a a + c0*c1*A a b + c0*c2*A a c + c0*c3*A a d +
      c0*c4*A a e + c1*c0*A b a + c1*c1*A b b + c1*c2*A b c +
      c1*c3*A b d + c1*c4*A b e + c2*c0*A c a + c2*c1*A c b +
      c2*c2*A c c + c2*c3*A c d + c2*c4*A c e + c3*c0*A d a +
      c3*c1*A d b + c3*c2*A d c + c3*c3*A d d + c3*c4*A d e +
      c4*c0*A e a + c4*c1*A e b + c4*c2*A e c + c4*c3*A e d +
      c4*c4*A e e := by
  dsimp
  simp [Matrix.mulVec, dotProduct, Finset.sum_add_distrib, add_mul, mul_add, hA.apply]
  ring

/-- The intersection matrix of a numerical type is symmetric, off-diagonally nonnegative, and
kills the strictly positive multiplicity vector. -/
private lemma intersection_positive_kernel (T : NumericalType) :
    (Matrix.of fun i j : Fin T.componentCount => (T.intersection i j : ℚ)).IsSymm ∧
      (∀ i j, i ≠ j → 0 ≤ (T.intersection i j : ℚ)) ∧
      (∀ i, 0 < (T.multiplicity i : ℚ)) ∧
      (Matrix.of fun i j : Fin T.componentCount => (T.intersection i j : ℚ)) *ᵥ
        (fun i => (T.multiplicity i : ℚ)) = 0 := by
  refine ⟨?_, fun i j hij => ?_, fun i => ?_, ?_⟩
  · ext i j
    simp [T.intersection_symm]
  · exact_mod_cast T.intersection_nonneg i j hij
  · exact_mod_cast T.multiplicity_pos i
  · ext i
    have hrow : (∑ j, (T.intersection i j : ℚ) * (T.multiplicity j : ℚ)) = 0 := by
      exact_mod_cast T.intersection_mul_multiplicity i
    simpa [Matrix.mulVec, dotProduct] using hrow

private lemma numericalType_dotProduct_eq_zero_iff (T : NumericalType)
    (x : Fin T.componentCount → ℚ) :
    x ⬝ᵥ ((fun i j => (T.intersection i j : ℚ)) *ᵥ x) = 0 ↔
      ∃ q : ℚ, x = q • (fun i => (T.multiplicity i : ℚ)) := by
  obtain ⟨hsymm, hoff, hm, hAm⟩ := intersection_positive_kernel T
  refine dotProduct_mulVec_eq_zero_iff_of_positive_kernel hsymm hoff hm hAm fun I hI hne hcut => ?_
  refine T.connected ⟨I, hI, hne, fun i hi j hj => ?_⟩
  exact_mod_cast hcut i hi j hj

lemma five_support_quadratic_strictly_negative (T : NumericalType)
    (hcount : 5 < T.componentCount) (v : Fin 5 → Fin T.componentCount)
    (_hv : Function.Injective v) (x : Fin T.componentCount → ℚ)
    (houtside : ∀ u, (∀ r, u ≠ v r) → x u = 0)
    (hnonzero : x (v 0) ≠ 0) :
    x ⬝ᵥ ((fun i j => (T.intersection i j : ℚ)) *ᵥ x) < 0 := by
  obtain ⟨hsymm, hoff, hm, hAm⟩ := intersection_positive_kernel T
  have hnonpos := dotProduct_mulVec_nonpos_of_positive_kernel hsymm hoff hm hAm x
  by_contra hnot
  have hzero : x ⬝ᵥ ((fun i j => (T.intersection i j : ℚ)) *ᵥ x) = 0 :=
    le_antisymm hnonpos (not_lt.mp hnot)
  obtain ⟨q, hq⟩ :=
    (numericalType_dotProduct_eq_zero_iff T x).mp hzero
  have hnotSurj : ¬ Function.Surjective v := by
    intro hs
    have hle : Fintype.card (Fin T.componentCount) ≤ Fintype.card (Fin 5) :=
      Fintype.card_le_of_surjective v hs
    have hle' : T.componentCount ≤ 5 := by simpa using hle
    omega
  obtain ⟨u, hu⟩ : ∃ u, ∀ r : Fin 5, v r ≠ u := by
    by_contra hno
    apply hnotSurj
    intro u
    by_contra hmiss
    apply hno
    refine ⟨u, ?_⟩
    intro r hr
    exact hmiss ⟨r, hr⟩
  have hqu : q = 0 := by
    have hxu := houtside u (fun r => (hu r).symm)
    have hpoint := congrFun hq u
    have hmup : 0 < (T.multiplicity u : ℚ) := by
      exact_mod_cast T.multiplicity_pos u
    have hprod : q * (T.multiplicity u : ℚ) = 0 := by
      simpa [smul_eq_mul, hxu] using hpoint
    rcases mul_eq_zero.mp hprod with hqzero | hmzero
    · exact hqzero
    · linarith
  have hz := congrFun hq (v 0)
  apply hnonzero
  simpa [hqu, smul_eq_mul] using hz

lemma endpoint_zero_of_quadratic_formula (T : NumericalType)
    (hcount : 5 < T.componentCount) (v : Fin 5 → Fin T.componentCount)
    (hv : Function.Injective v) (x : Fin T.componentCount → ℚ)
    (houtside : ∀ u, (∀ r, u ≠ v r) → x u = 0)
    (hnonzero : x (v 0) ≠ 0) (w : ℤ) (_hw : 0 < w)
    (hfirstWeight : w ≤ T.weight (v 0))
    (hformula : x ⬝ᵥ ((fun i j => (T.intersection i j : ℚ)) *ᵥ x) =
      -2 * (w : ℚ) + 2 * (T.intersection (v 0) (v 4) : ℚ)) :
    T.intersection (v 0) (v 4) = 0 := by
  have hstrict := five_support_quadratic_strictly_negative
    T hcount v hv x houtside hnonzero
  have hlt : (T.intersection (v 0) (v 4) : ℚ) < w := by
    nlinarith [hstrict, hformula]
  have hltZ : T.intersection (v 0) (v 4) < w := by
    exact_mod_cast hlt
  have hne : v 0 ≠ v 4 := by
    intro h
    have hh := hv h
    omega
  have hnonneg : 0 ≤ T.intersection (v 0) (v 4) :=
    T.intersection_nonneg (v 0) (v 4) hne
  obtain ⟨q, hdiv⟩ := T.weight_dvd_intersection (v 0) (v 4)
  have hbasePos : 0 < T.weight (v 0) := T.weight_pos _
  have hqnonneg : 0 ≤ q := by
    by_contra hq
    have hqneg : q < 0 := by omega
    rw [hdiv] at hnonneg
    nlinarith [mul_neg_of_pos_of_neg hbasePos hqneg]
  by_cases hqzero : q = 0
  · rw [hdiv, hqzero]
    omega
  · have hqpos : 0 < q := by omega
    have hqge : 1 ≤ q := by omega
    have hprod : T.weight (v 0) ≤ T.weight (v 0) * q := by
      have hmul := mul_nonneg (le_of_lt hbasePos) (by omega : 0 ≤ q - 1)
      nlinarith
    have hwle : w ≤ T.weight (v 0) := hfirstWeight
    rw [hdiv] at hltZ
    omega

lemma row_balance_dominates (T : NumericalType)
    (i : Fin T.componentCount) (hi : IsMinusTwoIndex T i)
    (S : Finset (Fin T.componentCount))
    (hS : ∀ j ∈ S, j ≠ i) :
    (∑ j ∈ S, T.intersection i j * T.multiplicity j) ≤
      2 * T.weight i * T.multiplicity i := by
  classical
  let f : Fin T.componentCount → ℤ :=
    fun j => T.intersection i j * T.multiplicity j
  have hrow := T.intersection_mul_multiplicity i
  have huniv : f i + ∑ j ∈ Finset.univ.erase i, f j = 0 := by
    rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ i)] at hrow
    simpa [f] using hrow
  have hbalance :
      (∑ j ∈ Finset.univ.erase i, f j) =
        2 * T.weight i * T.multiplicity i := by
    rw [show f i = (-2 * T.weight i) * T.multiplicity i by
      simp [f, hi.2]] at huniv
    nlinarith
  have hsubset : S ⊆ Finset.univ.erase i := by
    intro j hj
    simp only [Finset.mem_erase, Finset.mem_univ]
    exact ⟨hS j hj, trivial⟩
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
    intro j hj hnot
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have hnonneg : 0 ≤ T.intersection i j :=
      T.intersection_nonneg i j hji.symm
    exact mul_nonneg hnonneg (le_of_lt (T.multiplicity_pos j)))
  have hsum' : (∑ j ∈ S, f j) ≤ 2 * T.weight i * T.multiplicity i :=
    hsum.trans_eq hbalance
  simpa [f] using hsum'

/-- The ordered configuration of type `A₅`: equal weights and the simply-laced
five-vertex chain intersection matrix. -/
public def IsA5Configuration (T : NumericalType)
    (v : Fin 5 → Fin T.componentCount) (w : ℤ) : Prop :=
  (fun r ↦ T.weight (v r)) = ![w, w, w, w, w] ∧
    (fun r s ↦ T.intersection (v r) (v s)) =
      !![-2 * w, w, 0, 0, 0;
          w, -2 * w, w, 0, 0;
          0, w, -2 * w, w, 0;
          0, 0, w, -2 * w, w;
          0, 0, 0, w, -2 * w] ∧
    2 * T.multiplicity (v 0) ≥ T.multiplicity (v 1) ∧
    2 * T.multiplicity (v 1) ≥ T.multiplicity (v 0) + T.multiplicity (v 2) ∧
    2 * T.multiplicity (v 2) ≥ T.multiplicity (v 1) + T.multiplicity (v 3) ∧
    2 * T.multiplicity (v 3) ≥ T.multiplicity (v 2) + T.multiplicity (v 4) ∧
    2 * T.multiplicity (v 4) ≥ T.multiplicity (v 3)

/-- The ordered configuration of type `C₅`, with the last weight twice the
other four weights. -/
public def IsC5Configuration (T : NumericalType)
    (v : Fin 5 → Fin T.componentCount) (w : ℤ) : Prop :=
  (fun r ↦ T.weight (v r)) = ![w, w, w, w, 2 * w] ∧
    (fun r s ↦ T.intersection (v r) (v s)) =
      !![-2 * w, w, 0, 0, 0;
          w, -2 * w, w, 0, 0;
          0, w, -2 * w, w, 0;
          0, 0, w, -2 * w, 2 * w;
          0, 0, 0, 2 * w, -4 * w] ∧
    2 * T.multiplicity (v 0) ≥ T.multiplicity (v 1) ∧
    2 * T.multiplicity (v 1) ≥ T.multiplicity (v 0) + T.multiplicity (v 2) ∧
    2 * T.multiplicity (v 2) ≥ T.multiplicity (v 1) + T.multiplicity (v 3) ∧
    2 * T.multiplicity (v 3) ≥ T.multiplicity (v 2) + 2 * T.multiplicity (v 4) ∧
    2 * T.multiplicity (v 4) ≥ T.multiplicity (v 3)

/-- The ordered configuration of type `B₅`, with the first four weights twice
the last weight. -/
public def IsB5Configuration (T : NumericalType)
    (v : Fin 5 → Fin T.componentCount) (w : ℤ) : Prop :=
  (fun r ↦ T.weight (v r)) = ![2 * w, 2 * w, 2 * w, 2 * w, w] ∧
    (fun r s ↦ T.intersection (v r) (v s)) =
      !![-4 * w, 2 * w, 0, 0, 0;
          2 * w, -4 * w, 2 * w, 0, 0;
          0, 2 * w, -4 * w, 2 * w, 0;
          0, 0, 2 * w, -4 * w, 2 * w;
          0, 0, 0, 2 * w, -2 * w] ∧
    2 * T.multiplicity (v 0) ≥ T.multiplicity (v 1) ∧
    2 * T.multiplicity (v 1) ≥ T.multiplicity (v 0) + T.multiplicity (v 2) ∧
    2 * T.multiplicity (v 2) ≥ T.multiplicity (v 1) + T.multiplicity (v 3) ∧
    2 * T.multiplicity (v 3) ≥ T.multiplicity (v 2) + T.multiplicity (v 4) ∧
    T.multiplicity (v 3) ≥ T.multiplicity (v 2)

/-! ### The five chain matrices, computed once each

Each branch of `five_chain_is_A5_or_C5_or_B5` has to evaluate
`fivePathMatrix` at its weight profile, over all twenty-five index pairs. Done
inline, those five `fin_cases r <;> fin_cases s <;> simp` blocks cost about
seven seconds each and dominate the declaration -- which is what the profiler
showed and why the proof needed a raised heartbeat budget. They are statements
about `fivePathMatrix` alone, with no numerical type in them, so each is lifted
here into its own declaration with its own budget. -/

lemma fivePathMatrix_eq_A5 (a b c d e w : ℤ)
    (ha : a = w) (hb : b = w) (hc : c = w) (hd : d = w) (he : e = w) :
    fivePathMatrix a b c d e = !![-2 * w, w, 0, 0, 0;
     w, -2 * w, w, 0, 0;
     0, w, -2 * w, w, 0;
     0, 0, w, -2 * w, w;
     0, 0, 0, w, -2 * w] := by
  subst ha hb hc hd he
  ext r s
  fin_cases r <;> fin_cases s <;> simp [fivePathMatrix]

lemma fivePathMatrix_eq_C5 (a b c d e w : ℤ) (hw : 0 ≤ w)
    (ha : a = w) (hb : b = w) (hc : c = w) (hd : d = w) (he : e = 2 * w) :
    fivePathMatrix a b c d e = !![-2 * w, w, 0, 0, 0;
     w, -2 * w, w, 0, 0;
     0, w, -2 * w, w, 0;
     0, 0, w, -2 * w, 2 * w;
     0, 0, 0, 2 * w, -4 * w] := by
  subst ha hb hc hd he
  ext r s
  fin_cases r <;> fin_cases s <;> simp [fivePathMatrix] <;> omega

lemma fivePathMatrix_reverse_eq_C5 (a b c d e w : ℤ) (hw : 0 ≤ w)
    (ha : a = 2 * w) (hb : b = w) (hc : c = w) (hd : d = w) (he : e = w) :
    (fun r s => fivePathMatrix a b c d e (reverseFive r) (reverseFive s)) =
      !![-2 * w, w, 0, 0, 0;
     w, -2 * w, w, 0, 0;
     0, w, -2 * w, w, 0;
     0, 0, w, -2 * w, 2 * w;
     0, 0, 0, 2 * w, -4 * w] := by
  subst ha hb hc hd he
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [reverseFive, Equiv.swap_apply_def, fivePathMatrix] <;> omega

lemma fivePathMatrix_eq_B5 (a b c d e w : ℤ) (hw : 0 ≤ w)
    (ha : a = 2 * w) (hb : b = 2 * w) (hc : c = 2 * w) (hd : d = 2 * w)
    (he : e = w) :
    fivePathMatrix a b c d e = !![-4 * w, 2 * w, 0, 0, 0;
     2 * w, -4 * w, 2 * w, 0, 0;
     0, 2 * w, -4 * w, 2 * w, 0;
     0, 0, 2 * w, -4 * w, 2 * w;
     0, 0, 0, 2 * w, -2 * w] := by
  subst ha hb hc hd he
  ext r s
  fin_cases r <;> fin_cases s <;> simp [fivePathMatrix] <;> omega

lemma fivePathMatrix_reverse_eq_B5 (a b c d e w : ℤ) (hw : 0 ≤ w)
    (ha : a = w) (hb : b = 2 * w) (hc : c = 2 * w) (hd : d = 2 * w)
    (he : e = 2 * w) :
    (fun r s => fivePathMatrix a b c d e (reverseFive r) (reverseFive s)) =
      !![-4 * w, 2 * w, 0, 0, 0;
     2 * w, -4 * w, 2 * w, 0, 0;
     0, 2 * w, -4 * w, 2 * w, 0;
     0, 0, 2 * w, -4 * w, 2 * w;
     0, 0, 0, 2 * w, -2 * w] := by
  subst ha hb hc hd he
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [reverseFive, Equiv.swap_apply_def, fivePathMatrix] <;> omega

end AlgebraicGeometry.NumericalType
