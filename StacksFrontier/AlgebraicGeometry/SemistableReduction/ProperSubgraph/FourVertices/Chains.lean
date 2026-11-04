module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Defs
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Genus
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.LinearAlgebra.DiagonallyDominant
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.TwoVertices
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.ThreeVertices
public import Mathlib
public import Mathlib.Data.Fin.VecNotation
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.FourVertices.TripleShapes

/-!
# Four-vertex chains

Four distinct minus-two indices forming a chain extend the three-vertex
classification to the types `A₄`, `B₄`, `C₄` and `F₄`.

## Main results

* `AlgebraicGeometry.NumericalType.four_minus_two_indices`.

## References

* [Stacks Project, Tag 0C7V](https://stacks.math.columbia.edu/tag/0C7V)
-/

@[expose] public section

open Matrix

namespace AlgebraicGeometry.NumericalType

/-- The rational intersection matrix of a numerical type is symmetric. -/
private theorem intersection_matrix_isSymm (T : NumericalType) :
    (Matrix.of fun i j => (T.intersection i j : ℚ)).IsSymm := by
  ext i j
  rw [Matrix.transpose_apply]
  simp [T.intersection_symm]

private theorem numericalType_dotProduct_nonpos (T : NumericalType)
    (x : Fin T.componentCount → ℚ) :
    x ⬝ᵥ ((fun i j => (T.intersection i j : ℚ)) *ᵥ x) ≤ 0 := by
  classical
  let A : Matrix (Fin T.componentCount) (Fin T.componentCount) ℚ :=
    fun i j => (T.intersection i j : ℚ)
  let m : Fin T.componentCount → ℚ := fun i => (T.multiplicity i : ℚ)
  have hAoff : ∀ i j, i ≠ j → 0 ≤ A i j := by
    intro i j hij
    show 0 ≤ (T.intersection i j : ℚ)
    exact_mod_cast T.intersection_nonneg i j hij
  have hmpos : ∀ i, 0 < m i := by
    intro i
    show 0 < (T.multiplicity i : ℚ)
    exact_mod_cast T.multiplicity_pos i
  have hAm : A *ᵥ m = 0 := by
    ext i
    have hrow : (∑ j, (T.intersection i j : ℚ) * (T.multiplicity j : ℚ)) = 0 := by
      exact_mod_cast T.intersection_mul_multiplicity i
    show (∑ j, A i j * m j) = 0
    simpa [A, m] using hrow
  exact dotProduct_mulVec_nonpos_of_positive_kernel (intersection_matrix_isSymm T) hAoff hmpos hAm x

/-- The intersection quadratic form supported on four distinct indices is nonpositive. -/
private theorem four_term_quad_nonpos (T : NumericalType)
    (i j k l : Fin T.componentCount)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) (c0 c1 c2 c3 : ℚ) :
    c0 * c0 * (T.intersection i i : ℚ) + c0 * c1 * (T.intersection i j : ℚ) +
    c0 * c2 * (T.intersection i k : ℚ) + c0 * c3 * (T.intersection i l : ℚ) +
    c1 * c0 * (T.intersection j i : ℚ) + c1 * c1 * (T.intersection j j : ℚ) +
    c1 * c2 * (T.intersection j k : ℚ) + c1 * c3 * (T.intersection j l : ℚ) +
    c2 * c0 * (T.intersection k i : ℚ) + c2 * c1 * (T.intersection k j : ℚ) +
    c2 * c2 * (T.intersection k k : ℚ) + c2 * c3 * (T.intersection k l : ℚ) +
    c3 * c0 * (T.intersection l i : ℚ) + c3 * c1 * (T.intersection l j : ℚ) +
    c3 * c2 * (T.intersection l k : ℚ) + c3 * c3 * (T.intersection l l : ℚ) ≤ 0 := by
  classical
  exact le_of_eq_of_le (dotProduct_mulVec_four_formula
    (Matrix.of fun a b => (T.intersection a b : ℚ)) (intersection_matrix_isSymm T)
    i j k l hij hik hil hjk hjl hkl c0 c1 c2 c3).symm
    (numericalType_dotProduct_nonpos T _)

/-- The all-ones quadratic form on four distinct indices is nonpositive, in symmetrized form. -/
private theorem four_ones_quad_nonpos (T : NumericalType)
    (i j k l : Fin T.componentCount)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    T.intersection i i + T.intersection j j + T.intersection k k + T.intersection l l +
      2 * (T.intersection i j + T.intersection i k + T.intersection i l +
        T.intersection j k + T.intersection j l + T.intersection k l) ≤ 0 := by
  have h := four_term_quad_nonpos T i j k l hij hik hil hjk hjl hkl 1 1 1 1
  have h' : ((T.intersection i i + T.intersection j j + T.intersection k k +
      T.intersection l l + 2 * (T.intersection i j + T.intersection i k +
        T.intersection i l + T.intersection j k + T.intersection j l +
        T.intersection k l) : ℤ) : ℚ) ≤ 0 := by
    push_cast
    simp only [T.intersection_symm] at h ⊢
    linarith
  exact_mod_cast h'

private theorem no_affine_four_chord (T : NumericalType)
    (hn : 4 < T.componentCount)
    (i j k l : Fin T.componentCount)
    (hdistinct : Function.Injective ![i, j, k, l])
    (c : Fin 4 → ℚ) (hc0 : c 0 ≠ 0) (w : ℤ) (K : ℚ)
    (hK : 0 < K) (hw : 0 < w)
    (hquad :
      c 0 * c 0 * (T.intersection i i : ℚ) + c 0 * c 1 * (T.intersection i j : ℚ) +
      c 0 * c 2 * (T.intersection i k : ℚ) + c 0 * c 3 * (T.intersection i l : ℚ) +
      c 1 * c 0 * (T.intersection j i : ℚ) + c 1 * c 1 * (T.intersection j j : ℚ) +
      c 1 * c 2 * (T.intersection j k : ℚ) + c 1 * c 3 * (T.intersection j l : ℚ) +
      c 2 * c 0 * (T.intersection k i : ℚ) + c 2 * c 1 * (T.intersection k j : ℚ) +
      c 2 * c 2 * (T.intersection k k : ℚ) + c 2 * c 3 * (T.intersection k l : ℚ) +
      c 3 * c 0 * (T.intersection l i : ℚ) + c 3 * c 1 * (T.intersection l j : ℚ) +
      c 3 * c 2 * (T.intersection l k : ℚ) + c 3 * c 3 * (T.intersection l l : ℚ) =
        K * (w : ℚ) * (T.intersection i l : ℚ)) : False := by
  have h03 : i ≠ l := hdistinct.ne (show (0 : Fin 4) ≠ 3 by decide)
  have hnonpos := four_term_quad_nonpos T i j k l
    (hdistinct.ne (show (0 : Fin 4) ≠ 1 by decide))
    (hdistinct.ne (show (0 : Fin 4) ≠ 2 by decide)) h03
    (hdistinct.ne (show (1 : Fin 4) ≠ 2 by decide))
    (hdistinct.ne (show (1 : Fin 4) ≠ 3 by decide))
    (hdistinct.ne (show (2 : Fin 4) ≠ 3 by decide)) (c 0) (c 1) (c 2) (c 3)
  have hs : 0 ≤ (T.intersection i l : ℚ) := by
    exact_mod_cast T.intersection_nonneg i l h03
  have hKw : 0 < K * (w : ℚ) := mul_pos hK (by exact_mod_cast hw)
  have hchord : (T.intersection i l : ℚ) = 0 := by
    nlinarith [hnonpos, hquad, hs, hKw]
  exact no_affine_four_chain T hn ![i, j, k, l] hdistinct c hc0
    (hquad.trans (by rw [hchord]; ring))

private theorem chord_zero_A4 (T : NumericalType) (hn : 4 < T.componentCount)
    (i j k l : Fin T.componentCount)
    (hijne : i ≠ j) (hikne : i ≠ k) (hilne : i ≠ l)
    (hjkne : j ≠ k) (hjlne : j ≠ l) (hklne : k ≠ l)
    (hi : IsMinusTwoIndex T i) (hj : IsMinusTwoIndex T j)
    (hl : IsMinusTwoIndex T l)
    (hij : T.intersection i j ≠ 0)
    (w : ℤ)
    (hL : TripleA T i j k w) (hR : TripleA T j k l w) :
    T.intersection i l = 0 := by
  by_contra hchord
  have hji : T.intersection j i ≠ 0 := by
    simpa [T.intersection_symm] using hij
  have hthird := ordered_triple_shape T (by omega) j i l hijne.symm hjlne
    hilne hj hi hl hji hchord
  have hpos := T.weight_pos i
  rcases hthird with ⟨u, hA⟩ | ⟨u, hC⟩ | ⟨u, hCr⟩ | ⟨u, hB⟩ | ⟨u, hBr⟩ <;>
  simp only [TripleA, TripleB, TripleC, TripleBr, TripleCr] at * <;>
  try omega
  · have hlocal :
        (1:ℚ) * 1 * (T.intersection i i : ℚ) +
        (1:ℚ) * 1 * (T.intersection i j : ℚ) +
        (1:ℚ) * 1 * (T.intersection i k : ℚ) +
        (1:ℚ) * 1 * (T.intersection i l : ℚ) +
        (1:ℚ) * 1 * (T.intersection j i : ℚ) +
        (1:ℚ) * 1 * (T.intersection j j : ℚ) +
        (1:ℚ) * 1 * (T.intersection j k : ℚ) +
        (1:ℚ) * 1 * (T.intersection j l : ℚ) +
        (1:ℚ) * 1 * (T.intersection k i : ℚ) +
        (1:ℚ) * 1 * (T.intersection k j : ℚ) +
        (1:ℚ) * 1 * (T.intersection k k : ℚ) +
        (1:ℚ) * 1 * (T.intersection k l : ℚ) +
        (1:ℚ) * 1 * (T.intersection l i : ℚ) +
        (1:ℚ) * 1 * (T.intersection l j : ℚ) +
        (1:ℚ) * 1 * (T.intersection l k : ℚ) +
        (1:ℚ) * 1 * (T.intersection l l : ℚ) = 0 := by
      simp_all [T.intersection_symm]
      ring
    have hdist : Function.Injective ![i, j, k, l] := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
    exact no_affine_four_chain T hn ![i, j, k, l] hdist
      (![1, 1, 1, 1] : Fin 4 → ℚ) (by norm_num) hlocal

private theorem chord_zero_Bfamily (T : NumericalType) (hn : 4 < T.componentCount)
    (i j k l : Fin T.componentCount)
    (hijne : i ≠ j) (hikne : i ≠ k) (hilne : i ≠ l)
    (hjkne : j ≠ k) (hjlne : j ≠ l) (hklne : k ≠ l)
    (hi : IsMinusTwoIndex T i) (hj : IsMinusTwoIndex T j)
    (hl : IsMinusTwoIndex T l) (hij : T.intersection i j ≠ 0)
    (w : ℤ) (hL : TripleA T i j k (2 * w))
    (hR : TripleB T j k l w) : T.intersection i l = 0 := by
  by_contra hchord
  have hji : T.intersection j i ≠ 0 := by
    simpa [T.intersection_symm] using hij
  have hthird := ordered_triple_shape T (by omega) j i l hijne.symm hjlne
    hilne hj hi hl hji hchord
  have hpos := T.weight_pos i
  have hquad := four_ones_quad_nonpos T i j k l hijne hikne hilne hjkne hjlne hklne
  rcases hthird with ⟨u, hA⟩ | ⟨u, hC⟩ | ⟨u, hCr⟩ | ⟨u, hB⟩ | ⟨u, hBr⟩ <;>
  simp only [TripleA, TripleB, TripleC, TripleBr, TripleCr, T.intersection_symm] at * <;>
  omega

private theorem chord_zero_Cfamily (T : NumericalType) (hn : 4 < T.componentCount)
    (i j k l : Fin T.componentCount)
    (hijne : i ≠ j) (hikne : i ≠ k) (hilne : i ≠ l)
    (hjkne : j ≠ k) (hjlne : j ≠ l) (hklne : k ≠ l)
    (hi : IsMinusTwoIndex T i) (hj : IsMinusTwoIndex T j)
    (hl : IsMinusTwoIndex T l) (hij : T.intersection i j ≠ 0)
    (w : ℤ)
    (hpath : (TripleA T i j k w ∧ TripleC T j k l w) ∨
      (TripleC T i j k w ∧ TripleBr T j k l w)) :
    T.intersection i l = 0 := by
  by_contra hchord
  have hji : T.intersection j i ≠ 0 := by
    simpa [T.intersection_symm] using hij
  have hthird := ordered_triple_shape T (by omega) j i l hijne.symm hjlne
    hilne hj hi hl hji hchord
  have hpos := T.weight_pos i
  have hquad := four_ones_quad_nonpos T i j k l hijne hikne hilne hjkne hjlne hklne
  rcases hpath with ⟨hL, hR⟩ | ⟨hL, hR⟩ <;>
  rcases hthird with ⟨u, hA⟩ | ⟨u, hC⟩ | ⟨u, hCr⟩ | ⟨u, hB⟩ | ⟨u, hBr⟩ <;>
  simp only [TripleA, TripleB, TripleC, TripleBr, TripleCr, T.intersection_symm] at * <;>
  omega

private def QuadA (T : NumericalType) (a b c d : Fin T.componentCount)
    (w : ℤ) : Prop :=
  (fun p : Fin 4 => T.weight (![a, b, c, d] p)) = ![w, w, w, w] ∧
  (fun p q : Fin 4 => T.intersection (![a, b, c, d] p) (![a, b, c, d] q)) =
    ![![-2 * w, w, 0, 0], ![w, -2 * w, w, 0],
      ![0, w, -2 * w, w], ![0, 0, w, -2 * w]] ∧
  2 * T.multiplicity a ≥ T.multiplicity b ∧
  2 * T.multiplicity b ≥ T.multiplicity a + T.multiplicity c ∧
  2 * T.multiplicity c ≥ T.multiplicity b + T.multiplicity d ∧
  2 * T.multiplicity d ≥ T.multiplicity c

private def QuadC (T : NumericalType) (a b c d : Fin T.componentCount)
    (w : ℤ) : Prop :=
  (fun p : Fin 4 => T.weight (![a, b, c, d] p)) = ![w, w, w, 2 * w] ∧
  (fun p q : Fin 4 => T.intersection (![a, b, c, d] p) (![a, b, c, d] q)) =
    ![![-2 * w, w, 0, 0], ![w, -2 * w, w, 0],
      ![0, w, -2 * w, 2 * w], ![0, 0, 2 * w, -4 * w]] ∧
  2 * T.multiplicity a ≥ T.multiplicity b ∧
  2 * T.multiplicity b ≥ T.multiplicity a + T.multiplicity c ∧
  2 * T.multiplicity c ≥ T.multiplicity b + 2 * T.multiplicity d ∧
  2 * T.multiplicity d ≥ T.multiplicity c

private def QuadB (T : NumericalType) (a b c d : Fin T.componentCount)
    (w : ℤ) : Prop :=
  (fun p : Fin 4 => T.weight (![a, b, c, d] p)) = ![2 * w, 2 * w, 2 * w, w] ∧
  (fun p q : Fin 4 => T.intersection (![a, b, c, d] p) (![a, b, c, d] q)) =
    ![![-4 * w, 2 * w, 0, 0], ![2 * w, -4 * w, 2 * w, 0],
      ![0, 2 * w, -4 * w, 2 * w], ![0, 0, 2 * w, -2 * w]] ∧
  2 * T.multiplicity a ≥ T.multiplicity b ∧
  2 * T.multiplicity b ≥ T.multiplicity a + T.multiplicity c ∧
  2 * T.multiplicity c ≥ T.multiplicity b + T.multiplicity d ∧
  T.multiplicity d ≥ T.multiplicity c

private def QuadF (T : NumericalType) (a b c d : Fin T.componentCount)
    (w : ℤ) : Prop :=
  (fun p : Fin 4 => T.weight (![a, b, c, d] p)) = ![w, w, 2 * w, 2 * w] ∧
  (fun p q : Fin 4 => T.intersection (![a, b, c, d] p) (![a, b, c, d] q)) =
    ![![-2 * w, w, 0, 0], ![w, -2 * w, 2 * w, 0],
      ![0, 2 * w, -4 * w, 2 * w], ![0, 0, 2 * w, -4 * w]] ∧
  2 * T.multiplicity a ≥ T.multiplicity b ∧
  2 * T.multiplicity b ≥ T.multiplicity a + 2 * T.multiplicity c ∧
  2 * T.multiplicity c ≥ T.multiplicity b + T.multiplicity d ∧
  2 * T.multiplicity d ≥ T.multiplicity c

private def FourResult (T : NumericalType) (i j k l : Fin T.componentCount) : Prop :=
  (∃ w, QuadA T i j k l w) ∨ (∃ w, QuadC T i j k l w) ∨
  (∃ w, QuadB T i j k l w) ∨ (∃ w, QuadF T i j k l w) ∨
  (∃ w, QuadC T l k j i w) ∨ (∃ w, QuadF T l k j i w) ∨
  (∃ w, QuadB T l k j i w)

private theorem quadA_of_triples (T : NumericalType)
    (i j k l : Fin T.componentCount) (w : ℤ)
    (hL : TripleA T i j k w) (hR : TripleA T j k l w)
    (hChord : T.intersection i l = 0) : QuadA T i j k l w := by
  simp only [TripleA] at hL hR
  simp only [QuadA]
  refine ⟨?_, ?_, by omega⟩
  · funext p
    fin_cases p <;> simp_all
  · funext p q
    fin_cases p <;> fin_cases q <;> simp_all [T.intersection_symm]

private theorem quadC_of_triples (T : NumericalType)
    (i j k l : Fin T.componentCount) (w : ℤ)
    (hL : TripleA T i j k w) (hR : TripleC T j k l w)
    (hChord : T.intersection i l = 0) : QuadC T i j k l w := by
  simp only [TripleA] at hL
  simp only [TripleC] at hR
  simp only [QuadC]
  refine ⟨?_, ?_, by omega⟩
  · funext p
    fin_cases p <;> simp_all
  · funext p q
    fin_cases p <;> fin_cases q <;> simp_all [T.intersection_symm]

private theorem quadB_of_triples (T : NumericalType)
    (i j k l : Fin T.componentCount) (w : ℤ)
    (hL : TripleA T i j k (2 * w)) (hR : TripleB T j k l w)
    (hChord : T.intersection i l = 0) : QuadB T i j k l w := by
  simp only [TripleA] at hL
  simp only [TripleB] at hR
  simp only [QuadB]
  refine ⟨?_, ?_, by omega⟩
  · funext p
    fin_cases p <;> simp_all
  · funext p q
    fin_cases p <;> fin_cases q <;> simp_all [T.intersection_symm]

private theorem quadF_of_triples (T : NumericalType)
    (i j k l : Fin T.componentCount) (w : ℤ)
    (hL : TripleC T i j k w) (hR : TripleBr T j k l w)
    (hChord : T.intersection i l = 0) : QuadF T i j k l w := by
  simp only [TripleC] at hL
  simp only [TripleBr] at hR
  simp only [QuadF]
  refine ⟨?_, ?_, by omega⟩
  · funext p
    fin_cases p <;> simp_all
  · funext p q
    fin_cases p <;> fin_cases q <;> simp_all [T.intersection_symm]

private theorem reverseTripleA (T : NumericalType)
    (a b c : Fin T.componentCount) (w : ℤ)
    (h : TripleA T a b c w) : TripleA T c b a w := by
  simp only [TripleA] at h ⊢
  rcases h with ⟨hwa, hwb, hwc, haa, hab, hac, hba, hbb, hbc, hca, hcb, hcc,
    hma, hmb, hmc⟩
  exact ⟨hwc, hwb, hwa, hcc, hcb, hca, hbc, hbb, hba, hac, hab, haa,
    hmc, by omega, hma⟩

private theorem reverseTripleCr (T : NumericalType)
    (a b c : Fin T.componentCount) (w : ℤ)
    (h : TripleCr T a b c w) : TripleC T c b a w := by
  simp only [TripleCr] at h
  simp only [TripleC]
  rcases h with ⟨hwa, hwb, hwc, haa, hab, hac, hba, hbb, hbc, hca, hcb, hcc,
    hma, hmb, hmc⟩
  exact ⟨hwc, hwb, hwa, hcc, hcb, hca, hbc, hbb, hba, hac, hab, haa,
    hma, hmb, hmc⟩

private theorem reverseTripleB (T : NumericalType)
    (a b c : Fin T.componentCount) (w : ℤ)
    (h : TripleB T a b c w) : TripleBr T c b a w := by
  simp only [TripleB] at h
  simp only [TripleBr]
  rcases h with ⟨hwa, hwb, hwc, haa, hab, hac, hba, hbb, hbc, hca, hcb, hcc,
    hma, hmb, hmc⟩
  exact ⟨hwc, hwb, hwa, hcc, hcb, hca, hbc, hbb, hba, hac, hab, haa,
    hma, by omega, hmc⟩

private theorem reverseTripleBr (T : NumericalType)
    (a b c : Fin T.componentCount) (w : ℤ)
    (h : TripleBr T a b c w) : TripleB T c b a w := by
  simp only [TripleBr] at h
  simp only [TripleB]
  rcases h with ⟨hwa, hwb, hwc, haa, hab, hac, hba, hbb, hbc, hca, hcb, hcc,
    hma, hmb, hmc⟩
  exact ⟨hwc, hwb, hwa, hcc, hcb, hca, hbc, hbb, hba, hac, hab, haa,
    hma, by omega, hmc⟩

private theorem fourResult_to_conclusion (T : NumericalType)
    (i j k l : Fin T.componentCount) (h : FourResult T i j k l) :
    ∃ (σ : Equiv.Perm (Fin 4)) (w : ℤ),
      let r : Fin 4 → Fin T.componentCount := ![i, j, k, l] ∘ σ
      (((fun p => T.weight (r p)) = ![w, w, w, w] ∧
          (fun p q => T.intersection (r p) (r q)) =
            ![![-2 * w, w, 0, 0], ![w, -2 * w, w, 0],
              ![0, w, -2 * w, w], ![0, 0, w, -2 * w]] ∧
          2 * T.multiplicity (r 0) ≥ T.multiplicity (r 1) ∧
          2 * T.multiplicity (r 1) ≥ T.multiplicity (r 0) + T.multiplicity (r 2) ∧
          2 * T.multiplicity (r 2) ≥ T.multiplicity (r 1) + T.multiplicity (r 3) ∧
          2 * T.multiplicity (r 3) ≥ T.multiplicity (r 2)) ∨
        ((fun p => T.weight (r p)) = ![w, w, w, 2 * w] ∧
          (fun p q => T.intersection (r p) (r q)) =
            ![![-2 * w, w, 0, 0], ![w, -2 * w, w, 0],
              ![0, w, -2 * w, 2 * w], ![0, 0, 2 * w, -4 * w]] ∧
          2 * T.multiplicity (r 0) ≥ T.multiplicity (r 1) ∧
          2 * T.multiplicity (r 1) ≥ T.multiplicity (r 0) + T.multiplicity (r 2) ∧
          2 * T.multiplicity (r 2) ≥
            T.multiplicity (r 1) + 2 * T.multiplicity (r 3) ∧
          2 * T.multiplicity (r 3) ≥ T.multiplicity (r 2)) ∨
        ((fun p => T.weight (r p)) = ![2 * w, 2 * w, 2 * w, w] ∧
          (fun p q => T.intersection (r p) (r q)) =
            ![![-4 * w, 2 * w, 0, 0], ![2 * w, -4 * w, 2 * w, 0],
              ![0, 2 * w, -4 * w, 2 * w], ![0, 0, 2 * w, -2 * w]] ∧
          2 * T.multiplicity (r 0) ≥ T.multiplicity (r 1) ∧
          2 * T.multiplicity (r 1) ≥ T.multiplicity (r 0) + T.multiplicity (r 2) ∧
          2 * T.multiplicity (r 2) ≥ T.multiplicity (r 1) + T.multiplicity (r 3) ∧
          T.multiplicity (r 3) ≥ T.multiplicity (r 2)) ∨
        ((fun p => T.weight (r p)) = ![w, w, 2 * w, 2 * w] ∧
          (fun p q => T.intersection (r p) (r q)) =
            ![![-2 * w, w, 0, 0], ![w, -2 * w, 2 * w, 0],
              ![0, 2 * w, -4 * w, 2 * w], ![0, 0, 2 * w, -4 * w]] ∧
          2 * T.multiplicity (r 0) ≥ T.multiplicity (r 1) ∧
          2 * T.multiplicity (r 1) ≥
            T.multiplicity (r 0) + 2 * T.multiplicity (r 2) ∧
          2 * T.multiplicity (r 2) ≥ T.multiplicity (r 1) + T.multiplicity (r 3) ∧
          2 * T.multiplicity (r 3) ≥ T.multiplicity (r 2))) := by
  have hrevp (p : Fin 4) : ![i, j, k, l] p.rev = ![l, k, j, i] p := by
    fin_cases p <;> rfl
  rcases h with ⟨w, hA⟩ | ⟨w, hC⟩ | ⟨w, hB⟩ | ⟨w, hF⟩ |
    ⟨w, hCr⟩ | ⟨w, hFr⟩ | ⟨w, hBr⟩
  · refine ⟨Equiv.refl _, w, ?_⟩
    simpa [QuadA] using Or.inl hA
  · refine ⟨Equiv.refl _, w, ?_⟩
    simpa [QuadC] using Or.inr (Or.inl hC)
  · refine ⟨Equiv.refl _, w, ?_⟩
    simpa [QuadB] using Or.inr (Or.inr (Or.inl hB))
  · refine ⟨Equiv.refl _, w, ?_⟩
    simpa [QuadF] using Or.inr (Or.inr (Or.inr hF))
  · refine ⟨Fin.revPerm, w, ?_⟩
    simpa [hrevp, QuadC] using Or.inr (Or.inl hCr)
  · refine ⟨Fin.revPerm, w, ?_⟩
    simpa [hrevp, QuadF] using Or.inr (Or.inr (Or.inr hFr))
  · refine ⟨Fin.revPerm, w, ?_⟩
    simpa [hrevp, QuadB] using Or.inr (Or.inr (Or.inl hBr))

/-- **Stacks Project, Tag 0C7V.** A proper chain of four minus-two indices has,
after reordering, one of the four listed weighted intersection matrices. -/
@[stacks 0C7V]
public theorem four_minus_two_indices
    (T : NumericalType) (hn : 4 < T.componentCount)
    (i j k l : Fin T.componentCount)
    (hdistinct : Function.Injective ![i, j, k, l])
    (hi : IsMinusTwoIndex T i) (hj : IsMinusTwoIndex T j)
    (hk : IsMinusTwoIndex T k) (hl : IsMinusTwoIndex T l)
    (hij : T.intersection i j ≠ 0) (hjk : T.intersection j k ≠ 0)
    (hkl : T.intersection k l ≠ 0) :
    ∃ (σ : Equiv.Perm (Fin 4)) (w : ℤ),
      let r : Fin 4 → Fin T.componentCount := ![i, j, k, l] ∘ σ
      (((fun p => T.weight (r p)) = ![w, w, w, w] ∧
          (fun p q => T.intersection (r p) (r q)) =
            ![![-2 * w, w, 0, 0],
              ![w, -2 * w, w, 0],
              ![0, w, -2 * w, w],
              ![0, 0, w, -2 * w]] ∧
          2 * T.multiplicity (r 0) ≥ T.multiplicity (r 1) ∧
          2 * T.multiplicity (r 1) ≥ T.multiplicity (r 0) + T.multiplicity (r 2) ∧
          2 * T.multiplicity (r 2) ≥ T.multiplicity (r 1) + T.multiplicity (r 3) ∧
          2 * T.multiplicity (r 3) ≥ T.multiplicity (r 2)) ∨
        ((fun p => T.weight (r p)) = ![w, w, w, 2 * w] ∧
          (fun p q => T.intersection (r p) (r q)) =
            ![![-2 * w, w, 0, 0],
              ![w, -2 * w, w, 0],
              ![0, w, -2 * w, 2 * w],
              ![0, 0, 2 * w, -4 * w]] ∧
          2 * T.multiplicity (r 0) ≥ T.multiplicity (r 1) ∧
          2 * T.multiplicity (r 1) ≥ T.multiplicity (r 0) + T.multiplicity (r 2) ∧
          2 * T.multiplicity (r 2) ≥
            T.multiplicity (r 1) + 2 * T.multiplicity (r 3) ∧
          2 * T.multiplicity (r 3) ≥ T.multiplicity (r 2)) ∨
        ((fun p => T.weight (r p)) = ![2 * w, 2 * w, 2 * w, w] ∧
          (fun p q => T.intersection (r p) (r q)) =
            ![![-4 * w, 2 * w, 0, 0],
              ![2 * w, -4 * w, 2 * w, 0],
              ![0, 2 * w, -4 * w, 2 * w],
              ![0, 0, 2 * w, -2 * w]] ∧
          2 * T.multiplicity (r 0) ≥ T.multiplicity (r 1) ∧
          2 * T.multiplicity (r 1) ≥ T.multiplicity (r 0) + T.multiplicity (r 2) ∧
          2 * T.multiplicity (r 2) ≥ T.multiplicity (r 1) + T.multiplicity (r 3) ∧
          T.multiplicity (r 3) ≥ T.multiplicity (r 2)) ∨
        ((fun p => T.weight (r p)) = ![w, w, 2 * w, 2 * w] ∧
          (fun p q => T.intersection (r p) (r q)) =
            ![![-2 * w, w, 0, 0],
              ![w, -2 * w, 2 * w, 0],
              ![0, 2 * w, -4 * w, 2 * w],
              ![0, 0, 2 * w, -4 * w]] ∧
          2 * T.multiplicity (r 0) ≥ T.multiplicity (r 1) ∧
          2 * T.multiplicity (r 1) ≥
            T.multiplicity (r 0) + 2 * T.multiplicity (r 2) ∧
          2 * T.multiplicity (r 2) ≥ T.multiplicity (r 1) + T.multiplicity (r 3) ∧
          2 * T.multiplicity (r 3) ≥ T.multiplicity (r 2))) := by
  classical
  have hne (a b : Fin 4) (hab : a ≠ b) : ![i, j, k, l] a ≠ ![i, j, k, l] b :=
    fun he => hab (hdistinct he)
  have hijne : i ≠ j := hne 0 1 (by decide)
  have hikne : i ≠ k := hne 0 2 (by decide)
  have hilne : i ≠ l := hne 0 3 (by decide)
  have hjkne : j ≠ k := hne 1 2 (by decide)
  have hjlne : j ≠ l := hne 1 3 (by decide)
  have hklne : k ≠ l := hne 2 3 (by decide)
  have hleft := ordered_triple_shape T (by omega) i j k hijne hikne hjkne
    hi hj hk hij hjk
  have hright := ordered_triple_shape T (by omega) j k l hjkne hjlne hklne
    hj hk hl hjk hkl
  rcases overlapping_triples T i j k l (tripleShapeOfOr T i j k hleft)
      (tripleShapeOfOr T j k l hright) with ⟨w, hL, hR⟩ | ⟨w, hL, hR⟩ | ⟨w, hL, hR⟩ |
      ⟨w, hL, hR⟩ | ⟨w, hL, hR⟩ | ⟨w, hL, hR⟩ | ⟨w, hL, hR⟩ |
      ⟨w, hL, hR⟩ | ⟨w, hL, hR⟩ | ⟨w, hL, hR⟩ | ⟨w, hL, hR⟩
  · have hChord := chord_zero_A4 T hn i j k l hijne hikne hilne hjkne hjlne hklne
      hi hj hl hij w hL hR
    have hQ := quadA_of_triples T i j k l w hL hR hChord
    exact fourResult_to_conclusion T i j k l (Or.inl ⟨w, hQ⟩)
  · have hChord := chord_zero_Cfamily T hn i j k l hijne hikne hilne hjkne hjlne hklne
      hi hj hl hij w (Or.inl ⟨hL, hR⟩)
    have hQ := quadC_of_triples T i j k l w hL hR hChord
    exact fourResult_to_conclusion T i j k l (Or.inr (Or.inl ⟨w, hQ⟩))
  · have hChord := chord_zero_Bfamily T hn i j k l hijne hikne hilne hjkne hjlne hklne
      hi hj hl hij w hL hR
    have hQ := quadB_of_triples T i j k l w hL hR hChord
    exact fourResult_to_conclusion T i j k l
      (Or.inr (Or.inr (Or.inl ⟨w, hQ⟩)))
  · have hChord := chord_zero_Cfamily T hn i j k l hijne hikne hilne hjkne hjlne hklne
      hi hj hl hij w (Or.inr ⟨hL, hR⟩)
    have hQ := quadF_of_triples T i j k l w hL hR hChord
    exact fourResult_to_conclusion T i j k l
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨w, hQ⟩))))
  · have hkl0 := chord_zero_Cfamily T hn l k j i hklne.symm hjlne.symm
      hilne.symm hjkne.symm hikne.symm hijne.symm hl hk hi
      (by simpa [T.intersection_symm] using hkl) w
      (Or.inl ⟨reverseTripleA T j k l w hR, reverseTripleCr T i j k w hL⟩)
    have hA := reverseTripleA T j k l w hR
    have hC := reverseTripleCr T i j k w hL
    have hQ := quadC_of_triples T l k j i w hA hC hkl0
    exact fourResult_to_conclusion T i j k l
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨w, hQ⟩)))))
  · have hkl0 := chord_zero_Cfamily T hn l k j i hklne.symm hjlne.symm
      hilne.symm hjkne.symm hikne.symm hijne.symm hl hk hi
      (by simpa [T.intersection_symm] using hkl) w
      (Or.inr ⟨reverseTripleCr T j k l w hR,
        reverseTripleB T i j k w hL⟩)
    have hC := reverseTripleCr T j k l w hR
    have hBr := reverseTripleB T i j k w hL
    have hQ := quadF_of_triples T l k j i w hC hBr hkl0
    exact fourResult_to_conclusion T i j k l
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨w, hQ⟩))))))
  · have hkl0 := chord_zero_Bfamily T hn l k j i hklne.symm hjlne.symm
      hilne.symm hjkne.symm hikne.symm hijne.symm hl hk hi
      (by simpa [T.intersection_symm] using hkl) w
      (reverseTripleA T j k l (2 * w) hR) (reverseTripleBr T i j k w hL)
    have hA := reverseTripleA T j k l (2 * w) hR
    have hB := reverseTripleBr T i j k w hL
    have hQ := quadB_of_triples T l k j i w hA hB hkl0
    exact fourResult_to_conclusion T i j k l
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨w, hQ⟩))))))
  · simp only [TripleCr, TripleC] at hL hR
    exact (no_affine_four_chord T hn i j k l hdistinct ![1, 2, 2, 1]
      (by norm_num) 1 2 (by norm_num) (by norm_num)
      (by simp_all [T.intersection_symm]; ring)).elim
  · simp only [TripleBr, TripleB] at hL hR
    exact (no_affine_four_chord T hn i j k l hdistinct ![1, 1, 1, 1]
      (by norm_num) 1 2 (by norm_num) (by norm_num)
      (by simp_all [T.intersection_symm]; ring)).elim
  · simp only [TripleBr, TripleC] at hL hR
    exact (no_affine_four_chord T hn i j k l hdistinct ![2, 2, 2, 1]
      (by norm_num) 1 4 (by norm_num) (by norm_num)
      (by simp_all [T.intersection_symm]; ring)).elim
  · simp only [TripleCr, TripleB] at hL hR
    exact (no_affine_four_chord T hn i j k l hdistinct ![1, 2, 2, 2]
      (by norm_num) 1 4 (by norm_num) (by norm_num)
      (by simp_all [T.intersection_symm]; ring)).elim

end AlgebraicGeometry.NumericalType
