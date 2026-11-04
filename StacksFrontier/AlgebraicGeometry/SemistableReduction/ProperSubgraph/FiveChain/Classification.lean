module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.FiveChain.Configurations

/-!
# Five-vertex chains: classification

A chain of five distinct minus-two indices is of type `A₅`, `C₅` or `B₅`. The
proof computes the quadratic form on the span of the chain and uses that it is
negative definite on a proper subgraph.

## Main results

* `AlgebraicGeometry.NumericalType.five_chain_is_A5_or_C5_or_B5`.

## References

* [Stacks Project, Tag 0C82](https://stacks.math.columbia.edu/tag/0C82)
-/

@[expose] public section

open Matrix

namespace AlgebraicGeometry.NumericalType

-- The long finite case split combines the local-chain classification with
-- five row-balance bounds.
/-- Five distinct minus-two indices joined consecutively in a numerical type
with more than five components form, after reordering, a configuration of type
`A₅`, `C₅`, or `B₅`. -/
@[stacks 0C82]
public lemma five_chain_is_A5_or_C5_or_B5 (T : NumericalType)
    (hcount : 5 < T.componentCount)
    (v : Fin 5 → Fin T.componentCount) (hv : Function.Injective v)
    (hminus : ∀ r, IsMinusTwoIndex T (v r))
    (hadjacent : ∀ r : Fin 4,
      T.intersection (v r.castSucc) (v r.succ) ≠ 0) :
    ∃ σ : Equiv.Perm (Fin 5), ∃ w : ℤ, 0 < w ∧
      (IsA5Configuration T (fun r ↦ v (σ r)) w ∨
        IsC5Configuration T (fun r ↦ v (σ r)) w ∨
        IsB5Configuration T (fun r ↦ v (σ r)) w) := by
  classical
  let embL : Fin 4 → Fin 5 := Fin.castSucc
  let embR : Fin 4 → Fin 5 := Fin.succ
  have hEmbL : Function.Injective embL := by
    intro a b hab
    apply Fin.ext
    simpa [embL] using congrArg Fin.val hab
  have hEmbR : Function.Injective embR := by
    intro a b hab
    apply Fin.ext
    simpa [embR] using congrArg Fin.val hab
  have hVecL : ![v 0, v 1, v 2, v 3] = v ∘ embL := by
    funext x
    fin_cases x <;> rfl
  have hVecR : ![v 1, v 2, v 3, v 4] = v ∘ embR := by
    funext x
    fin_cases x <;> rfl
  have hInjectiveL : Function.Injective ![v 0, v 1, v 2, v 3] := by
    rw [hVecL]
    exact hv.comp hEmbL
  have hInjectiveR : Function.Injective ![v 1, v 2, v 3, v 4] := by
    rw [hVecR]
    exact hv.comp hEmbR
  have hEdgeL01 : T.intersection (v 0) (v 1) ≠ 0 := by
    simpa using hadjacent (0 : Fin 4)
  have hEdgeL12 : T.intersection (v 1) (v 2) ≠ 0 := by
    simpa using hadjacent (1 : Fin 4)
  have hEdgeL23 : T.intersection (v 2) (v 3) ≠ 0 := by
    simpa using hadjacent (2 : Fin 4)
  have hEdgeR01 : T.intersection (v 1) (v 2) ≠ 0 := by
    simpa using hadjacent (1 : Fin 4)
  have hEdgeR12 : T.intersection (v 2) (v 3) ≠ 0 := by
    simpa using hadjacent (2 : Fin 4)
  have hEdgeR23 : T.intersection (v 3) (v 4) ≠ 0 := by
    simpa using hadjacent (3 : Fin 4)
  have hleft := four_chain_endpoint_intersection_zero T (by omega)
    (v 0) (v 1) (v 2) (v 3) hInjectiveL
    (by simpa [embL] using hminus (embL 0))
    (by simpa [embL] using hminus (embL 1))
    (by simpa [embL] using hminus (embL 2))
    (by simpa [embL] using hminus (embL 3)) hEdgeL01 hEdgeL12 hEdgeL23
  have hright := four_chain_endpoint_intersection_zero T (by omega)
    (v 1) (v 2) (v 3) (v 4) hInjectiveR
    (by simpa [embR] using hminus (embR 0))
    (by simpa [embR] using hminus (embR 1))
    (by simpa [embR] using hminus (embR 2))
    (by simpa [embR] using hminus (embR 3)) hEdgeR01 hEdgeR12 hEdgeR23
  have hleftProfile := four_chain_edge_pattern T (by omega)
    (v 0) (v 1) (v 2) (v 3) hInjectiveL
    (by simpa [embL] using hminus (embL 0))
    (by simpa [embL] using hminus (embL 1))
    (by simpa [embL] using hminus (embL 2))
    (by simpa [embL] using hminus (embL 3)) hEdgeL01 hEdgeL12 hEdgeL23
  have hrightProfile := four_chain_edge_pattern T (by omega)
    (v 1) (v 2) (v 3) (v 4) hInjectiveR
    (by simpa [embR] using hminus (embR 0))
    (by simpa [embR] using hminus (embR 1))
    (by simpa [embR] using hminus (embR 2))
    (by simpa [embR] using hminus (embR 3)) hEdgeR01 hEdgeR12 hEdgeR23
  have hleftWeights := fourEdgePattern_weights T (v 0) (v 1) (v 2) (v 3)
    hleftProfile
  have hrightWeights := fourEdgePattern_weights T (v 1) (v 2) (v 3) (v 4)
    hrightProfile
  have hfiveWeights := overlap_weight_shapes
    (T.weight (v 0)) (T.weight (v 1)) (T.weight (v 2))
      (T.weight (v 3)) (T.weight (v 4))
    (T.weight_pos _) (T.weight_pos _) (T.weight_pos _)
      (T.weight_pos _) (T.weight_pos _) hleftWeights hrightWeights
  have h02 := hleft.1
  have h03 := hleft.2.1
  have h13 := hleft.2.2
  have h13r := hright.1
  have h14 := hright.2.1
  have h24 := hright.2.2
  have hne (r s : Fin 5) (hrs : r ≠ s) : v r ≠ v s := by
    intro h
    exact hrs (hv h)
  have hshapes012 := three_chain_edge_shapes T (by omega)
    (v 0) (v 1) (v 2) (hminus 0) (hminus 1) (hminus 2)
    (hne 0 1 (by decide)) (hne 0 2 (by decide)) (hne 1 2 (by decide))
    hEdgeL01 hEdgeL12
  have hshapes123 := three_chain_edge_shapes T (by omega)
    (v 1) (v 2) (v 3) (hminus 1) (hminus 2) (hminus 3)
    (hne 1 2 (by decide)) (hne 1 3 (by decide)) (hne 2 3 (by decide))
    hEdgeL12 hEdgeL23
  have hshapes234 := three_chain_edge_shapes T (by omega)
    (v 2) (v 3) (v 4) (hminus 2) (hminus 3) (hminus 4)
    (hne 2 3 (by decide)) (hne 2 4 (by decide)) (hne 3 4 (by decide))
    hEdgeR12 hEdgeR23
  have hedge01 := edgeShape_intersection_eq_max T (v 0) (v 1) hshapes012.1
  have hedge12 := edgeShape_intersection_eq_max T (v 1) (v 2) hshapes012.2
  have hedge23 := edgeShape_intersection_eq_max T (v 2) (v 3) hshapes123.2
  have hedge34 := edgeShape_intersection_eq_max T (v 3) (v 4) hshapes234.2
  let A : Matrix (Fin T.componentCount) (Fin T.componentCount) ℚ :=
    fun a b => (T.intersection a b : ℚ)
  let x : Fin T.componentCount → ℚ := fun s =>
    (if s = v 0 then 1 else 0) + (if s = v 1 then 1 else 0) +
      (if s = v 2 then 1 else 0) + (if s = v 3 then 1 else 0) +
      (if s = v 4 then 1 else 0)
  have hsymm : A.IsSymm := by
    ext a b
    rw [Matrix.transpose_apply]
    simp [A, T.intersection_symm]
  have hneq01 := hne 0 1 (by decide)
  have hneq02 := hne 0 2 (by decide)
  have hneq03 := hne 0 3 (by decide)
  have hneq04 := hne 0 4 (by decide)
  have hneq12 := hne 1 2 (by decide)
  have hneq13 := hne 1 3 (by decide)
  have hneq14 := hne 1 4 (by decide)
  have hneq23 := hne 2 3 (by decide)
  have hneq24 := hne 2 4 (by decide)
  have hneq34 := hne 3 4 (by decide)
  have hdot := dotProduct_mulVec_five_formula A hsymm
    (v 0) (v 1) (v 2) (v 3) (v 4)
    hneq01 hneq02 hneq03 hneq04 hneq12 hneq13 hneq14 hneq23 hneq24 hneq34
    1 1 1 1 1
  have hquad : x ⬝ᵥ (A *ᵥ x) =
      -2 * ((T.weight (v 0) : ℚ) + T.weight (v 1) + T.weight (v 2) +
        T.weight (v 3) + T.weight (v 4)) +
      2 * ((max (T.weight (v 0)) (T.weight (v 1) : ℤ) : ℚ) +
        max (T.weight (v 1)) (T.weight (v 2)) +
        max (T.weight (v 2)) (T.weight (v 3)) +
        max (T.weight (v 3)) (T.weight (v 4)) +
        T.intersection (v 0) (v 4)) := by
    rw [hdot]
    simp [A, T.intersection_symm,
      (hminus 0).2, (hminus 1).2, (hminus 2).2, (hminus 3).2, (hminus 4).2,
      h02, h03, h13, h14, h24, hedge01, hedge12, hedge23, hedge34]
    ring
  have hxnonzero : x (v 0) ≠ 0 := by
    simp [x, hneq01, hneq02, hneq03, hneq04]
  have hxoutside : ∀ u, (∀ r, u ≠ v r) → x u = 0 := by
    intro u hu
    simp [x, hu]
  have hbaseShape := path_quadratic_base_shape
    (T.weight (v 0)) (T.weight (v 1)) (T.weight (v 2))
    (T.weight (v 3)) (T.weight (v 4))
    (T.weight_pos _) (T.weight_pos _) (T.weight_pos _)
      (T.weight_pos _) (T.weight_pos _) hfiveWeights
  have hchord : T.intersection (v 0) (v 4) = 0 := by
    have hstrict := five_support_quadratic_strictly_negative
      T (by omega) v hv x hxoutside hxnonzero
    have hneq04 := hne 0 4 (by decide)
    have hchordNonneg := T.intersection_nonneg (v 0) (v 4) hneq04
    rcases hbaseShape with ⟨w, hwpos, hwle, hbase⟩ | hbasezero
    · have hformula : x ⬝ᵥ (A *ᵥ x) =
          -2 * (w : ℚ) + 2 * (T.intersection (v 0) (v 4) : ℚ) := by
        rw [hquad]
        unfold fivePathQuadraticBase at hbase
        linarith
      exact endpoint_zero_of_quadratic_formula T (by omega) v hv x hxoutside
        hxnonzero w hwpos hwle hformula
    · have hquadZero : x ⬝ᵥ (A *ᵥ x) =
          2 * (T.intersection (v 0) (v 4) : ℚ) := by
        rw [hquad]
        unfold fivePathQuadraticBase at hbasezero
        linarith
      have hge : 0 ≤ x ⬝ᵥ (A *ᵥ x) := by
        rw [hquadZero]
        positivity
      linarith
  have hsymm' {a b : Fin T.componentCount} {c : ℤ} (h : T.intersection a b = c) :
      T.intersection b a = c := by
    rwa [T.intersection_symm]
  have hedge01r := hsymm' hedge01
  have hedge12r := hsymm' hedge12
  have hedge23r := hsymm' hedge23
  have hedge34r := hsymm' hedge34
  have h02r := hsymm' h02
  have h03r := hsymm' h03
  have h13r' := hsymm' h13
  have h14r := hsymm' h14
  have h24r := hsymm' h24
  have hchordr := hsymm' hchord
  have hpath : (fun r s => T.intersection (v r) (v s)) =
      fivePathMatrix (T.weight (v 0)) (T.weight (v 1))
        (T.weight (v 2)) (T.weight (v 3)) (T.weight (v 4)) := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [fivePathMatrix,
        (hminus 0).2, (hminus 1).2, (hminus 2).2, (hminus 3).2, (hminus 4).2,
        h02, h03, h13, h14, h24, hchord, hedge01, hedge12, hedge23, hedge34,
        hedge01r, hedge12r, hedge23r, hedge34r,
        T.intersection_symm]
  have hstrictPath : ∀ x0 x1 x2 x3 x4 : ℚ, x0 ≠ 0 →
      fivePathQuadraticForm (T.weight (v 0)) (T.weight (v 1))
        (T.weight (v 2)) (T.weight (v 3)) (T.weight (v 4))
        x0 x1 x2 x3 x4 < 0 := by
    intro x0 x1 x2 x3 x4 hx0
    let c : Fin 5 → ℚ := ![x0, x1, x2, x3, x4]
    let y : Fin T.componentCount → ℚ := fiveSupport v c
    let z : Fin T.componentCount → ℚ := fun s =>
      (if s = v 0 then x0 else 0) + (if s = v 1 then x1 else 0) +
        (if s = v 2 then x2 else 0) + (if s = v 3 then x3 else 0) +
        (if s = v 4 then x4 else 0)
    have hyz : y = z := by
      funext s
      simp [y, z, c, fiveSupport]
    have hy0 : y (v 0) ≠ 0 := by
      simpa [y, c, fiveSupport, hneq01, hneq02, hneq03, hneq04] using hx0
    have hyoutside : ∀ u, (∀ r, u ≠ v r) → y u = 0 := by
      intro u hu
      simp [y, c, fiveSupport, hu]
    have hstrict := five_support_quadratic_strictly_negative
      T (by omega) v hv y hyoutside hy0
    have hdotc := dotProduct_mulVec_five_formula A hsymm
      (v 0) (v 1) (v 2) (v 3) (v 4)
      hneq01 hneq02 hneq03 hneq04 hneq12 hneq13 hneq14 hneq23 hneq24 hneq34
      x0 x1 x2 x3 x4
    have hdotc' : z ⬝ᵥ (A *ᵥ z) =
        x0 * x0 * A (v 0) (v 0) + x0 * x1 * A (v 0) (v 1) +
          x0 * x2 * A (v 0) (v 2) + x0 * x3 * A (v 0) (v 3) +
          x0 * x4 * A (v 0) (v 4) +
          x1 * x0 * A (v 1) (v 0) + x1 * x1 * A (v 1) (v 1) +
          x1 * x2 * A (v 1) (v 2) + x1 * x3 * A (v 1) (v 3) +
          x1 * x4 * A (v 1) (v 4) +
          x2 * x0 * A (v 2) (v 0) + x2 * x1 * A (v 2) (v 1) +
          x2 * x2 * A (v 2) (v 2) + x2 * x3 * A (v 2) (v 3) +
          x2 * x4 * A (v 2) (v 4) +
          x3 * x0 * A (v 3) (v 0) + x3 * x1 * A (v 3) (v 1) +
          x3 * x2 * A (v 3) (v 2) + x3 * x3 * A (v 3) (v 3) +
          x3 * x4 * A (v 3) (v 4) +
          x4 * x0 * A (v 4) (v 0) + x4 * x1 * A (v 4) (v 1) +
          x4 * x2 * A (v 4) (v 2) + x4 * x3 * A (v 4) (v 3) +
          x4 * x4 * A (v 4) (v 4) := by
      simpa [z] using hdotc
    have hformula : y ⬝ᵥ (A *ᵥ y) =
        fivePathQuadraticForm (T.weight (v 0)) (T.weight (v 1))
          (T.weight (v 2)) (T.weight (v 3)) (T.weight (v 4))
          x0 x1 x2 x3 x4 := by
      rw [hyz]
      rw [hdotc']
      simp only [Fin.isValue, (hminus 0).2, Int.reduceNeg, neg_mul, Int.cast_neg, Int.cast_mul,
        Int.cast_ofNat, mul_neg, hedge01, Int.cast_max, h02, Int.cast_zero, mul_zero, add_zero, h03,
        hchord, hedge01r, (hminus 1).2, hedge12, h13, h14, h02r, hedge12r, (hminus 2).2, hedge23,
        h24, h03r, h13r', hedge23r, (hminus 3).2, hedge34, hchordr, h14r, h24r, hedge34r,
        (hminus 4).2, A]
      unfold fivePathQuadraticForm
      ring
    rw [hformula] at hstrict
    exact hstrict
  have hfiniteWeights := negative_path_form_classification
    (T.weight (v 0)) (T.weight (v 1)) (T.weight (v 2))
    (T.weight (v 3)) (T.weight (v 4))
    (T.weight_pos _) (T.weight_pos _) (T.weight_pos _)
      (T.weight_pos _) (T.weight_pos _) hstrictPath hfiveWeights
  let m0 := T.multiplicity (v 0)
  let m1 := T.multiplicity (v 1)
  let m2 := T.multiplicity (v 2)
  let m3 := T.multiplicity (v 3)
  let m4 := T.multiplicity (v 4)
  have hrow (a : Fin 5) (S : Finset (Fin 5)) (hS : ∀ b ∈ S, b ≠ a) :
      ∑ b ∈ S, T.intersection (v a) (v b) * T.multiplicity (v b) ≤
        2 * T.weight (v a) * T.multiplicity (v a) := by
    have h := row_balance_dominates T (v a) (hminus a) (S.image v)
      (by simpa using fun b hb hba => hS b hb (hv hba))
    rwa [Finset.sum_image fun x _ y _ hxy => hv hxy] at h
  have hrow0 : T.intersection (v 0) (v 1) * m1 ≤ 2 * T.weight (v 0) * m0 := by
    simpa [m0, m1] using hrow 0 {1} (by decide)
  have hrow1 : T.intersection (v 1) (v 0) * m0 +
      T.intersection (v 1) (v 2) * m2 ≤ 2 * T.weight (v 1) * m1 := by
    simpa [m0, m1, m2, Finset.sum_pair (hne 0 2 (by decide))] using hrow 1 {0, 2} (by decide)
  have hrow2 : T.intersection (v 2) (v 1) * m1 +
      T.intersection (v 2) (v 3) * m3 ≤ 2 * T.weight (v 2) * m2 := by
    simpa [m1, m2, m3, Finset.sum_pair (hne 1 3 (by decide))] using hrow 2 {1, 3} (by decide)
  have hrow3 : T.intersection (v 3) (v 2) * m2 +
      T.intersection (v 3) (v 4) * m4 ≤ 2 * T.weight (v 3) * m3 := by
    simpa [m2, m3, m4, Finset.sum_pair (hne 2 4 (by decide))] using hrow 3 {2, 4} (by decide)
  have hrow4 : T.intersection (v 4) (v 3) * m3 ≤ 2 * T.weight (v 4) * m4 := by
    simpa [m3, m4] using hrow 4 {3} (by decide)
  have scale (k a b : ℤ) (hk : 0 < k) (h : k * a ≤ 2 * k * b) : 2 * b ≥ a :=
    le_of_mul_le_mul_left (by linarith) hk
  have scale2 (k a a' b : ℤ) (hk : 0 < k) (h : k * a + k * a' ≤ 2 * k * b) : 2 * b ≥ a + a' :=
    scale k _ _ hk (by linarith)
  have hentry (r s : Fin 5) :
      T.intersection (v r) (v s) =
        fivePathMatrix (T.weight (v 0)) (T.weight (v 1))
          (T.weight (v 2)) (T.weight (v 3)) (T.weight (v 4)) r s :=
    congrFun (congrFun hpath r) s
  rcases hfiniteWeights with hA | hC | hCrev | hB | hBrev
  · let w := T.weight (v 0)
    have hw : 0 < w := T.weight_pos _
    have hw2 : w ≤ 2 * w := by omega
    have hweights : (fun r => T.weight (v r)) = ![w, w, w, w, w] := by
      ext r
      fin_cases r <;> simp [w, hA]
    have hmatrix : (fun r s => T.intersection (v r) (v s)) =
        !![-2 * w, w, 0, 0, 0;
           w, -2 * w, w, 0, 0;
           0, w, -2 * w, w, 0;
           0, 0, w, -2 * w, w;
           0, 0, 0, w, -2 * w] := by
      simp only [hentry]
      exact fivePathMatrix_eq_A5 _ _ _ _ _ w
        (by simpa using congrFun hweights 0)
        (by simpa using congrFun hweights 1)
        (by simpa using congrFun hweights 2)
        (by simpa using congrFun hweights 3)
        (by simpa using congrFun hweights 4)
    have hm0 : 2 * m0 ≥ m1 := scale w _ _ hw (by
      simpa [m0, m1, w, hA, hedge01] using hrow0)
    have hm1 : 2 * m1 ≥ m0 + m2 := scale2 w _ _ _ hw (by
      simpa [m0, m1, m2, w, hA, hedge01r, hedge12] using hrow1)
    have hm2 : 2 * m2 ≥ m1 + m3 := scale2 w _ _ _ hw (by
      simpa [m1, m2, m3, w, hA, hedge12r, hedge23] using hrow2)
    have hm3 : 2 * m3 ≥ m2 + m4 := scale2 w _ _ _ hw (by
      simpa [m2, m3, m4, w, hA, hedge23r, hedge34] using hrow3)
    have hm4 : 2 * m4 ≥ m3 := scale w _ _ hw (by
      simpa [m3, m4, w, hA, hedge34r] using hrow4)
    refine ⟨Equiv.refl _, w, hw, Or.inl ?_⟩
    exact ⟨hweights, hmatrix, hm0, hm1, hm2, hm3, hm4⟩
  · let w := T.weight (v 0)
    have hw : 0 < w := T.weight_pos _
    have hw2 : w ≤ 2 * w := by omega
    have hC1 : T.weight (v 1) = w := by simpa [w] using hC.1.symm
    have hC2 : T.weight (v 2) = w := hC.2.1.symm.trans hC1
    have hC3 : T.weight (v 3) = w := hC.2.2.1.symm.trans hC2
    have hC4 : T.weight (v 4) = 2 * w := by rw [hC.2.2.2, hC3]
    have hweights : (fun r => T.weight (v r)) = ![w, w, w, w, 2 * w] := by
      ext r
      fin_cases r <;> simp [w, hC1, hC2, hC3, hC4]
    have hmatrix : (fun r s => T.intersection (v r) (v s)) =
        !![-2 * w, w, 0, 0, 0;
           w, -2 * w, w, 0, 0;
           0, w, -2 * w, w, 0;
           0, 0, w, -2 * w, 2 * w;
           0, 0, 0, 2 * w, -4 * w] := by
      simp only [hentry]
      exact fivePathMatrix_eq_C5 _ _ _ _ _ w (by omega)
        (by simpa using congrFun hweights 0)
        (by simpa using congrFun hweights 1)
        (by simpa using congrFun hweights 2)
        (by simpa using congrFun hweights 3)
        (by simpa using congrFun hweights 4)
    have hm0 : 2 * m0 ≥ m1 := scale w _ _ hw (by
      simpa [m0, m1, w, hC1, hC2, hC3, hC4, hedge01, max_eq_right hw2, max_eq_left hw2] using hrow0)
    have hm1 : 2 * m1 ≥ m0 + m2 := scale2 w _ _ _ hw (by
      simpa [m0, m1, m2, w, hC1, hC2, hC3, hC4, hedge01r, hedge12,
        max_eq_right hw2, max_eq_left hw2]
        using hrow1)
    have hm2 : 2 * m2 ≥ m1 + m3 := scale2 w _ _ _ hw (by
      simpa [m1, m2, m3, w, hC1, hC2, hC3, hC4, hedge12r, hedge23,
        max_eq_right hw2, max_eq_left hw2]
        using hrow2)
    have hm3 : 2 * m3 ≥ m2 + 2 * m4 := scale w _ _ hw (by
      linarith [show w * m2 + 2 * w * m4 ≤ 2 * w * m3 by
        simpa [m2, m3, m4, w, hC1, hC2, hC3, hC4, hedge23r, hedge34,
          max_eq_right hw2, max_eq_left hw2] using hrow3])
    have hm4 : 2 * m4 ≥ m3 := scale (2 * w) _ _ (by omega) (by
      simpa [m3, m4, w, hC1, hC2, hC3, hC4, hedge34r,
        max_eq_right hw2, max_eq_left hw2]
        using hrow4)
    refine ⟨Equiv.refl _, w, hw, Or.inr (Or.inl ?_)⟩
    exact ⟨hweights, hmatrix, hm0, hm1, hm2, hm3, hm4⟩
  · let w := T.weight (v 1)
    have hw : 0 < w := T.weight_pos _
    have hw2 : w ≤ 2 * w := by omega
    have hCr0 : T.weight (v 0) = 2 * w := by simpa [w] using hCrev.1
    have hCr2 : T.weight (v 2) = w := hCrev.2.1.symm
    have hCr3 : T.weight (v 3) = w := hCrev.2.2.1.symm.trans hCr2
    have hCr4 : T.weight (v 4) = w := hCrev.2.2.2.symm.trans hCr3
    have hweights : (fun r => T.weight (v (reverseFive r))) =
        ![w, w, w, w, 2 * w] := by
      ext r
      fin_cases r <;> simp [reverseFive, Equiv.swap_apply_def, w,
        hCr0, hCr2, hCr3, hCr4]
    have hmatrix : (fun r s => T.intersection (v (reverseFive r))
        (v (reverseFive s))) =
        !![-2 * w, w, 0, 0, 0;
           w, -2 * w, w, 0, 0;
           0, w, -2 * w, w, 0;
           0, 0, w, -2 * w, 2 * w;
           0, 0, 0, 2 * w, -4 * w] := by
      simp only [hentry]
      exact fivePathMatrix_reverse_eq_C5 _ _ _ _ _ w (by omega)
        (by simpa [reverseFive, Equiv.swap_apply_def] using congrFun hweights 4)
        (by simpa [reverseFive, Equiv.swap_apply_def] using congrFun hweights 3)
        (by simpa [reverseFive, Equiv.swap_apply_def] using congrFun hweights 2)
        (by simpa [reverseFive, Equiv.swap_apply_def] using congrFun hweights 1)
        (by simpa [reverseFive, Equiv.swap_apply_def] using congrFun hweights 0)
    have hm0 : 2 * m4 ≥ m3 := scale w _ _ hw (by
      simpa [m3, m4, w, hCrev, hedge34r] using hrow4)
    have hm1 : 2 * m3 ≥ m2 + m4 := scale2 w _ _ _ hw (by
      simpa [m2, m3, m4, w, hCr0, hCr2, hCr3, hCr4, hedge23r, hedge34,
        max_eq_right hw2, max_eq_left hw2]
        using hrow3)
    have hm2 : 2 * m2 ≥ m1 + m3 := scale2 w _ _ _ hw (by
      simpa [m1, m2, m3, w, hCr0, hCr2, hCr3, hCr4, hedge12r, hedge23,
        max_eq_right hw2, max_eq_left hw2]
        using hrow2)
    have hm3 : 2 * m1 ≥ 2 * m0 + m2 := scale w _ _ hw (by
      linarith [show 2 * w * m0 + w * m2 ≤ 2 * w * m1 by
        simpa [m0, m1, m2, w, hCr0, hCr2, hCr3, hCr4, hedge01r, hedge12,
          max_eq_right hw2, max_eq_left hw2] using hrow1])
    have hm4 : 2 * m0 ≥ m1 := scale (2 * w) _ _ (by omega) (by
      simpa [m0, m1, w, hCr0, hCr2, hCr3, hCr4, hedge01,
        max_eq_right hw2, max_eq_left hw2]
        using hrow0)
    have hcfg : IsC5Configuration T (fun r => v (reverseFive r)) w := by
      refine ⟨hweights, hmatrix, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [reverseFive, Equiv.swap_apply_def, m0, m1, m2, m3, m4] using hm0
      · simpa [reverseFive, Equiv.swap_apply_def, m0, m1, m2, m3, m4,
          add_comm, add_left_comm, add_assoc] using hm1
      · simpa [reverseFive, Equiv.swap_apply_def, m0, m1, m2, m3, m4,
          add_comm, add_left_comm, add_assoc] using hm2
      · simpa [reverseFive, Equiv.swap_apply_def, m0, m1, m2, m3, m4,
          add_comm, add_left_comm, add_assoc] using hm3
      · simpa [reverseFive, Equiv.swap_apply_def, m0, m1, m2, m3, m4] using hm4
    exact ⟨reverseFive, w, hw, Or.inr (Or.inl hcfg)⟩
  · let w := T.weight (v 4)
    have hw : 0 < w := T.weight_pos _
    have hw2 : w ≤ 2 * w := by omega
    have hB3 : T.weight (v 3) = 2 * w := by simpa [w] using hB.2.2.2
    have hB2 : T.weight (v 2) = 2 * w := hB.2.2.1.trans hB3
    have hB1 : T.weight (v 1) = 2 * w := hB.2.1.trans hB2
    have hB0 : T.weight (v 0) = 2 * w := hB.1.trans hB1
    have hweights : (fun r => T.weight (v r)) = ![2 * w, 2 * w, 2 * w, 2 * w, w] := by
      ext r
      fin_cases r <;> simp [w, hB0, hB1, hB2, hB3]
    have hmatrix : (fun r s => T.intersection (v r) (v s)) =
        !![-4 * w, 2 * w, 0, 0, 0;
           2 * w, -4 * w, 2 * w, 0, 0;
           0, 2 * w, -4 * w, 2 * w, 0;
           0, 0, 2 * w, -4 * w, 2 * w;
           0, 0, 0, 2 * w, -2 * w] := by
      simp only [hentry]
      exact fivePathMatrix_eq_B5 _ _ _ _ _ w (by omega)
        (by simpa using congrFun hweights 0)
        (by simpa using congrFun hweights 1)
        (by simpa using congrFun hweights 2)
        (by simpa using congrFun hweights 3)
        (by simpa using congrFun hweights 4)
    have hm0 : 2 * m0 ≥ m1 := scale (2 * w) _ _ (by omega) (by
      simpa [m0, m1, w, hB0, hB1, hB2, hB3, hedge01, max_eq_right hw2, max_eq_left hw2] using hrow0)
    have hm1 : 2 * m1 ≥ m0 + m2 := scale2 (2 * w) _ _ _ (by omega) (by
      simpa [m0, m1, m2, w, hB0, hB1, hB2, hB3, hedge01r, hedge12,
        max_eq_right hw2, max_eq_left hw2]
        using hrow1)
    have hm2 : 2 * m2 ≥ m1 + m3 := scale2 (2 * w) _ _ _ (by omega) (by
      simpa [m1, m2, m3, w, hB0, hB1, hB2, hB3, hedge12r, hedge23,
        max_eq_right hw2, max_eq_left hw2]
        using hrow2)
    have hm3 : 2 * m3 ≥ m2 + m4 := scale2 (2 * w) _ _ _ (by omega) (by
      simpa [m2, m3, m4, w, hB0, hB1, hB2, hB3, hedge23r, hedge34,
        max_eq_right hw2, max_eq_left hw2]
        using hrow3)
    have htail : m3 ≤ m4 := le_of_mul_le_mul_left (a := 2 * w) (by
      simpa [m3, m4, w, hB0, hB1, hB2, hB3, hedge34r, max_eq_right hw2, max_eq_left hw2]
        using hrow4) (by omega)
    refine ⟨Equiv.refl _, w, hw, Or.inr (Or.inr ?_)⟩
    have hm4 : m3 ≥ m2 := by omega
    exact ⟨hweights, hmatrix, hm0, hm1, hm2, hm3, hm4⟩
  · let w := T.weight (v 0)
    have hw : 0 < w := T.weight_pos _
    have hw2 : w ≤ 2 * w := by omega
    have hBrev1 : T.weight (v 1) = 2 * w := by simpa [w] using hBrev.1
    have hBrev2 : T.weight (v 2) = 2 * w := hBrev.2.1.symm.trans hBrev1
    have hBrev3 : T.weight (v 3) = 2 * w := hBrev.2.2.1.symm.trans hBrev2
    have hBrev4 : T.weight (v 4) = 2 * w := hBrev.2.2.2.symm.trans hBrev3
    have hweights : (fun r => T.weight (v (reverseFive r))) =
        ![2 * w, 2 * w, 2 * w, 2 * w, w] := by
      ext r
      fin_cases r <;> simp [reverseFive, Equiv.swap_apply_def, w,
        hBrev1, hBrev2, hBrev3, hBrev4]
    have hmatrix : (fun r s => T.intersection (v (reverseFive r))
        (v (reverseFive s))) =
        !![-4 * w, 2 * w, 0, 0, 0;
           2 * w, -4 * w, 2 * w, 0, 0;
           0, 2 * w, -4 * w, 2 * w, 0;
           0, 0, 2 * w, -4 * w, 2 * w;
           0, 0, 0, 2 * w, -2 * w] := by
      simp only [hentry]
      exact fivePathMatrix_reverse_eq_B5 _ _ _ _ _ w (by omega)
        (by simpa [reverseFive, Equiv.swap_apply_def] using congrFun hweights 4)
        (by simpa [reverseFive, Equiv.swap_apply_def] using congrFun hweights 3)
        (by simpa [reverseFive, Equiv.swap_apply_def] using congrFun hweights 2)
        (by simpa [reverseFive, Equiv.swap_apply_def] using congrFun hweights 1)
        (by simpa [reverseFive, Equiv.swap_apply_def] using congrFun hweights 0)
    have hm0 : 2 * m4 ≥ m3 := scale (2 * w) _ _ (by omega) (by
      simpa [m3, m4, w, hBrev1, hBrev2, hBrev3, hBrev4, hedge34r,
        max_eq_right hw2, max_eq_left hw2]
        using hrow4)
    have hm1 : 2 * m3 ≥ m2 + m4 := scale2 (2 * w) _ _ _ (by omega) (by
      simpa [m2, m3, m4, w, hBrev1, hBrev2, hBrev3, hBrev4, hedge23r, hedge34,
        max_eq_right hw2, max_eq_left hw2]
        using hrow3)
    have hm2 : 2 * m2 ≥ m1 + m3 := scale2 (2 * w) _ _ _ (by omega) (by
      simpa [m1, m2, m3, w, hBrev1, hBrev2, hBrev3, hBrev4, hedge12r, hedge23,
        max_eq_right hw2, max_eq_left hw2]
        using hrow2)
    have hm3 : 2 * m1 ≥ m0 + m2 := scale2 (2 * w) _ _ _ (by omega) (by
      simpa [m0, m1, m2, w, hBrev1, hBrev2, hBrev3, hBrev4, hedge01r, hedge12,
        max_eq_right hw2, max_eq_left hw2]
        using hrow1)
    have htail : m1 ≤ m0 := le_of_mul_le_mul_left (a := 2 * w) (by
      simpa [m0, m1, w, hBrev1, hBrev2, hBrev3, hBrev4, hedge01,
        max_eq_right hw2, max_eq_left hw2] using hrow0) (by omega)
    have hm4 : m1 ≥ m2 := by omega
    have hcfg : IsB5Configuration T (fun r => v (reverseFive r)) w := by
      refine ⟨hweights, hmatrix, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [reverseFive, Equiv.swap_apply_def, m0, m1, m2, m3, m4] using hm0
      · simpa [reverseFive, Equiv.swap_apply_def, m0, m1, m2, m3, m4,
          add_comm, add_left_comm, add_assoc] using hm1
      · simpa [reverseFive, Equiv.swap_apply_def, m0, m1, m2, m3, m4,
          add_comm, add_left_comm, add_assoc] using hm2
      · simpa [reverseFive, Equiv.swap_apply_def, m0, m1, m2, m3, m4,
          add_comm, add_left_comm, add_assoc] using hm3
      · simpa [reverseFive, Equiv.swap_apply_def, m0, m1, m2, m3, m4] using hm4
    exact ⟨reverseFive, w, hw, Or.inr (Or.inr hcfg)⟩

end AlgebraicGeometry.NumericalType
