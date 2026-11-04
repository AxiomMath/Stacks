module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.ChartNormalization

/-!
# Moving the singular point to the origin, with the coordinate change made explicit

`AlgebraicGeometry.exists_quadraticRelation_vanishing_first_row` moves the singular point
`(c₂, c₃)` of the first chart to the origin by the change of generators
`x'₁ = x₁, x'₂ = x₂ - u x₁, x'₃ = x₃ - v x₁` with `ū = c₂, v̄ = c₃`. This file states the same
result recording that change of generators, which is what locates the singular point of the
blowup at the origin `(x₁, x'₂/x₁, x'₃/x₁)` of the chart.

## Main results

* `AlgebraicGeometry.exists_quadraticRelation_vanishing_first_row_explicit`
-/

@[expose] public section

open IsLocalRing MvPolynomial

namespace AlgebraicGeometry

variable {A : Type*} [CommRing A] [IsLocalRing A]

/-- **The chart normalization of Section 54.12, with the change of generators recorded.** The
same statement as `AlgebraicGeometry.exists_quadraticRelation_vanishing_first_row`, together with
the new generators: `x'₁ = x₁`, `x'₂ = x₂ - u x₁`, `x'₃ = x₃ - v x₁` with residues `ū = c₂`,
`v̄ = c₃`. -/
public theorem exists_quadraticRelation_vanishing_first_row_explicit (x : Fin 3 → A)
    (hspan : Ideal.span (Set.range x) = maximalIdeal A)
    (a : Fin 3 → Fin 3 → A) (b : Fin 3 → Fin 3 → Fin 3 → A)
    (hupper : ∀ p q, q < p → a p q = 0)
    (hrel : ∑ p, ∑ q, a p q * (x p * x q) = ∑ p, ∑ q, ∑ r, b p q r * (x p * x q * x r))
    (hcase : ¬ IsScalarSqLinear fun p q => residue A (a p q))
    (c : Fin 2 → ResidueField A)
    (hconst : residue A (a 0 0) + residue A (a 0 1) * c 0 + residue A (a 0 2) * c 1 +
      residue A (a 1 1) * (c 0 * c 0) + residue A (a 1 2) * (c 0 * c 1) +
      residue A (a 2 2) * (c 1 * c 1) = 0)
    (hlin₂ : residue A (a 0 1) + 2 * (residue A (a 1 1) * c 0) + residue A (a 1 2) * c 1 = 0)
    (hlin₃ : residue A (a 0 2) + residue A (a 1 2) * c 0 + 2 * (residue A (a 2 2) * c 1) = 0) :
    ∃ (x' : Fin 3 → A) (a' : Fin 3 → Fin 3 → A) (b' : Fin 3 → Fin 3 → Fin 3 → A),
      Ideal.span (Set.range x') = maximalIdeal A ∧ (∀ p q, q < p → a' p q = 0) ∧
        a' 0 0 = 0 ∧ a' 0 1 = 0 ∧ a' 0 2 = 0 ∧
        (∀ p q : Fin 2, a' p.succ q.succ = a p.succ q.succ) ∧
        (∃ p q, p ≤ q ∧ a' p q ∉ maximalIdeal A) ∧
        (∑ p, ∑ q, a' p q * (x' p * x' q) = ∑ p, ∑ q, ∑ r, b' p q r * (x' p * x' q * x' r)) ∧
        IsGoodCoordinateForm (fun p q => residue A (a' p q)) ∧
        x' 0 = x 0 ∧ ∃ u v : A, residue A u = c 0 ∧ residue A v = c 1 ∧
          x' 1 = x 1 - u * x 0 ∧ x' 2 = x 2 - v * x 0 := by
  classical
  have hidx : ∀ r : Fin 3, r = 0 ∨ r = 1 ∨ r = 2 := by decide
  have hidx2 : ∀ r : Fin 2, r = 0 ∨ r = 1 := by decide
  have e1 : (0 : Fin 2).succ = (1 : Fin 3) := by decide
  have e2 : (1 : Fin 2).succ = (2 : Fin 3) := by decide
  obtain ⟨u, hu⟩ := residue_surjective (R := A) (c 0)
  obtain ⟨v, hv⟩ := residue_surjective (R := A) (c 1)
  obtain ⟨y, hy0, hy1, hy2⟩ : ∃ y : Fin 3 → A,
      y 0 = x 0 ∧ y 1 = x 1 - u * x 0 ∧ y 2 = x 2 - v * x 0 :=
    ⟨fun p => if p = 0 then x 0 else if p = 1 then x 1 - u * x 0 else x 2 - v * x 0,
      by simp, by simp, by simp⟩
  have hchart : ∀ (u v : A) (z w : Fin 3 → A), w 0 = z 0 → w 1 = u * z 0 + z 1 →
      w 2 = v * z 0 + z 2 → ∀ i, w i = ∑ p, chartTranslation u v i p * z p := by
    intro u v z w h0 h1 h2 i
    rcases hidx i with rfl | rfl | rfl
    exacts [h0.trans (sum_chartTranslation_mul u v z).1.symm,
      h1.trans (sum_chartTranslation_mul u v z).2.1.symm,
      h2.trans (sum_chartTranslation_mul u v z).2.2.symm]
  have hspan' : Ideal.span (Set.range y) = maximalIdeal A := by
    rw [span_range_eq_of_isUnit_det x y (chartTranslation (-u) (-v))
      (isUnit_det_chartTranslation _ _)
      (hchart _ _ x y hy0 (by rw [hy1]; ring) (by rw [hy2]; ring))]
    exact hspan
  have hx : ∀ i, x i = ∑ p, chartTranslation u v i p * y p :=
    hchart u v y x hy0.symm (by rw [hy0, hy1]; ring) (by rw [hy0, hy2]; ring)
  obtain ⟨b', hb'⟩ := exists_quadraticRelation_changeOfGenerators x y hspan'
    (chartTranslation u v) hx a b hrel
  obtain ⟨T, hT⟩ : ∃ T : Fin 3 → Fin 3 → A, ∀ p q, T p q =
      ∑ i, ∑ j, a i j * (chartTranslation u v i p * chartTranslation u v j q) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨e00, e01, e10, e02, e20, e11, e12, e21, e22⟩ :=
    transportForm_chartTranslation_entries u v a hupper
  have hrelT : ∑ p, ∑ q, T p q * (y p * y q)
      = ∑ p, ∑ q, ∑ r, b' p q r * (y p * y q * y r) :=
    Eq.trans (Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by rw [hT p q]) hb'
  have hT00 : residue A (T 0 0) = 0 := by
    rw [hT, e00]
    simp only [map_add, map_mul, hu, hv]
    linear_combination hconst
  have hT01 : residue A (T 0 1) + residue A (T 1 0) = 0 := by
    rw [hT, hT, e01, e10]
    simp only [map_add, map_mul, hu, hv]
    linear_combination hlin₂
  have hT02 : residue A (T 0 2) + residue A (T 2 0) = 0 := by
    rw [hT, hT, e02, e20]
    simp only [map_add, map_mul, hu, hv]
    linear_combination hlin₃
  obtain ⟨s, hs00, hs01, hs02, hs10, hs11, hs12, hs20, hs21, hs22⟩ :
      ∃ s : Fin 3 → Fin 3 → A, s 0 0 = T 0 0 ∧ s 0 1 = T 0 1 + T 1 0 ∧
        s 0 2 = T 0 2 + T 2 0 ∧ s 1 0 = 0 ∧ s 1 1 = T 1 1 ∧ s 1 2 = T 1 2 + T 2 1 ∧
        s 2 0 = 0 ∧ s 2 1 = 0 ∧ s 2 2 = T 2 2 :=
    ⟨fun p q => if p = 0 ∧ q = 0 then T 0 0 else if p = 0 ∧ q = 1 then T 0 1 + T 1 0
        else if p = 0 ∧ q = 2 then T 0 2 + T 2 0 else if p = 1 ∧ q = 1 then T 1 1
        else if p = 1 ∧ q = 2 then T 1 2 + T 2 1 else if p = 2 ∧ q = 2 then T 2 2 else 0,
      by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩
  obtain ⟨a', ha'00, ha'01, ha'02, ha'10, ha'11, ha'12, ha'20, ha'21, ha'22⟩ :
      ∃ a' : Fin 3 → Fin 3 → A, a' 0 0 = 0 ∧ a' 0 1 = 0 ∧ a' 0 2 = 0 ∧ a' 1 0 = 0 ∧
        a' 1 1 = T 1 1 ∧ a' 1 2 = T 1 2 + T 2 1 ∧ a' 2 0 = 0 ∧ a' 2 1 = 0 ∧ a' 2 2 = T 2 2 :=
    ⟨fun p q => if p = 1 ∧ q = 1 then T 1 1 else if p = 1 ∧ q = 2 then T 1 2 + T 2 1
        else if p = 2 ∧ q = 2 then T 2 2 else 0,
      by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩
  have hupper' : ∀ p q, q < p → a' p q = 0 := by
    intro p q hpq
    rcases hidx p with rfl | rfl | rfl
    · rcases hidx q with rfl | rfl | rfl <;> exact absurd hpq (by decide)
    · rcases hidx q with rfl | rfl | rfl
      · exact ha'10
      · exact absurd hpq (by decide)
      · exact absurd hpq (by decide)
    · rcases hidx q with rfl | rfl | rfl
      · exact ha'20
      · exact ha'21
      · exact absurd hpq (by decide)
  have hTs : (∀ p, T p p = s p p) ∧ ∀ p q, p < q → T p q + T q p = s p q + s q p := by
    refine ⟨fun p => ?_, fun p q hpq => ?_⟩
    · rcases hidx p with rfl | rfl | rfl
      exacts [hs00.symm, hs11.symm, hs22.symm]
    · rcases hidx p with rfl | rfl | rfl
      · rcases hidx q with rfl | rfl | rfl
        · exact absurd hpq (by decide)
        · rw [hs01, hs10]; ring
        · rw [hs02, hs20]; ring
      · rcases hidx q with rfl | rfl | rfl
        · exact absurd hpq (by decide)
        · exact absurd hpq (by decide)
        · rw [hs12, hs21]; ring
      · rcases hidx q with rfl | rfl | rfl <;> exact absurd hpq (by decide)
  have hres : ∀ p q, residue A (s p q) = residue A (a' p q) := by
    intro p q
    rcases hidx p with rfl | rfl | rfl <;> rcases hidx q with rfl | rfl | rfl <;>
      simp only [hs00, hs01, hs02, hs10, hs11, hs12, hs20, hs21, hs22, ha'00, ha'01, ha'02,
        ha'10, ha'11, ha'12, ha'20, ha'21, ha'22, map_zero, map_add, hT00, hT01, hT02]
  obtain ⟨b'', hb''⟩ := exists_quadraticRelation_sub y hspan' s a' b'
    (fun p q => (residue_eq_zero_iff _).mp (by rw [map_sub, hres, sub_self]))
    ((sum_quadratic_congr_of_symm y T s hTs.1 hTs.2).symm.trans hrelT)
  have hTcase : ¬ IsScalarSqLinear fun p q => residue A (T p q) := by
    intro hcon
    refine hcase ?_
    have heq : (fun p q => residue A (T p q))
        = transportForm (fun i j => residue A (a i j))
          fun i p => chartTranslation (c 0) (c 1) i p := by
      funext p q
      rw [hT, transportForm_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_mul, map_chartTranslation, map_chartTranslation, hu, hv]
    rw [heq] at hcon
    exact (isScalarSqLinear_transportForm_matrix_iff _ _
      (isUnit_det_chartTranslation (c 0) (c 1))).mp hcon
  have ha'case : ¬ IsScalarSqLinear fun p q => residue A (a' p q) := fun hcon =>
    hTcase ((isScalarSqLinear_congr (a' := fun p q => residue A (s p q))
      (fun p => congrArg (residue A) (hTs.1 p)) fun p q hpq => by
        simp only [← map_add, hTs.2 p q hpq]).mpr (by simpa only [hres] using hcon))
  have hgood : IsGoodCoordinateForm fun p q => residue A (a' p q) :=
    isGoodCoordinateForm_of_upperTriangular_fin_three
      (fun p q hpq => by rw [hupper' p q hpq, map_zero])
      (by rw [ha'00, map_zero]) (by rw [ha'01, map_zero]) (by rw [ha'02, map_zero]) ha'case
  have hrestrict : ∀ p q : Fin 2, a' p.succ q.succ = a p.succ q.succ := by
    have h21 : a 2 1 = 0 := hupper 2 1 (by decide)
    intro p q
    rcases hidx2 p with rfl | rfl <;> rcases hidx2 q with rfl | rfl
    · rw [e1, ha'11, hT, e11]
    · rw [e1, e2, ha'12, hT, hT, e12, e21, h21, add_zero]
    · rw [e2, e1, ha'21, h21]
    · rw [e2, ha'22, hT, e22]
  have hunit' : ∃ p q : Fin 3, p ≤ q ∧ a' p q ∉ maximalIdeal A := by
    by_contra hcontra
    have hcon : ∀ p q : Fin 3, p ≤ q → a' p q ∈ maximalIdeal A := fun p q hpq =>
      Classical.byContradiction fun hm => hcontra ⟨p, q, hpq, hm⟩
    refine hgood ⟨0, 0, fun p => ?_, fun p q hpq => ?_⟩
    · rw [restrictFirstVar_apply, (residue_eq_zero_iff _).mpr (hcon _ _ le_rfl)]
      ring
    · rcases hidx2 p with rfl | rfl
      · rcases hidx2 q with rfl | rfl
        · exact absurd hpq (by decide)
        · rw [restrictFirstVar_apply, restrictFirstVar_apply, e1, e2, ha'21, map_zero,
            (residue_eq_zero_iff _).mpr (hcon 1 2 (by decide))]
          ring
      · rcases hidx2 q with rfl | rfl <;> exact absurd hpq (by decide)
  exact ⟨y, a', b'', hspan', hupper', ha'00, ha'01, ha'02, hrestrict, hunit', hb'', hgood,
    hy0, u, v, hu, hv, hy1, hy2⟩

end AlgebraicGeometry

end
