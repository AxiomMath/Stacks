module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Genus
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Graph
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Defs
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Tactic

/-!
# The topological genus bounds the genus of a minimal numerical type

For a minimal numerical type the topological genus `1 - n + e` of its
intersection graph is at most its genus.

## Main results

* `AlgebraicGeometry.NumericalType.one_sub_componentCount_add_edgeCount_le_genus_of_isMinimal`.

## References

* [Stacks Project, Tag 0C7C](https://stacks.math.columbia.edu/tag/0C7C)
-/

@[expose] public section

namespace AlgebraicGeometry.NumericalType

/-- The components meeting a given component: the neighbours of a vertex of the
intersection graph. -/
public def neighbors (T : NumericalType) (i : Fin T.componentCount) :
    Finset (Fin T.componentCount) :=
  Finset.univ.filter fun j : Fin T.componentCount => i ≠ j ∧ 0 < T.intersection i j

/-- The number of components meeting a given component: the degree of a vertex of
the intersection graph. -/
public def neighborCount (T : NumericalType) (i : Fin T.componentCount) : ℕ :=
  (neighbors T i).card

/-- The degrees of the intersection graph sum to twice the number of edges. -/
public lemma sum_neighborCount_eq_two_edgeCount (T : NumericalType) :
  (∑ i, neighborCount T i) = 2 * edgeCount T := by
  classical
  have hdegree : ∀ i, neighborCount T i = (intersectionGraph T).degree i := by
    intro i
    unfold neighborCount neighbors
    rw [SimpleGraph.degree]
    congr 1
    ext j
    rw [SimpleGraph.mem_neighborFinset]
    simp [intersectionGraph]
  have hsum := (intersectionGraph T).sum_degrees_eq_twice_card_edges
  have hcard : (intersectionGraph T).edgeFinset.card = edgeCount T := by
    calc
      (intersectionGraph T).edgeFinset.card =
          Nat.card (intersectionGraph T).edgeSet := by
        rw [SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]
      _ = edgeCount T := (edgeCount_eq_card_edgeFinset T).symm
  calc
    (∑ i, neighborCount T i) = ∑ i, (intersectionGraph T).degree i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hdegree i
    _ = 2 * (intersectionGraph T).edgeFinset.card := hsum
    _ = 2 * edgeCount T := by rw [hcard]

public lemma exists_neighbor (T : NumericalType) (hn : 1 < T.componentCount)
    (i : Fin T.componentCount) :
    ∃ j, i ≠ j ∧ 0 < T.intersection i j := by
  let I : Set (Fin T.componentCount) := {i}
  have hnot : I ≠ Set.univ := by
    intro h
    let i₀ : Fin T.componentCount := ⟨0, by omega⟩
    let i₁ : Fin T.componentCount := ⟨1, by omega⟩
    have h₀ : i₀ = i := by
      have : i₀ ∈ I := by rw [h]; exact Set.mem_univ _
      simpa [I] using this
    have h₁ : i₁ = i := by
      have : i₁ ∈ I := by rw [h]; exact Set.mem_univ _
      simpa [I] using this
    have h01 : i₀ ≠ i₁ := by
      intro heq
      have := congrArg Fin.val heq
      norm_num [i₀, i₁] at this
    exact h01 (h₀.trans h₁.symm)
  have hsep : ¬ ∀ a, a ∈ I → ∀ b, b ∉ I → T.intersection a b = 0 := by
    intro h
    exact T.connected ⟨I, ⟨i, by simp [I]⟩, hnot, h⟩
  push Not at hsep
  obtain ⟨a, ha, b, hb, hab⟩ := hsep
  have hai : a = i := by simpa [I] using ha
  subst a
  have hbi : b ≠ i := by simpa [I] using hb
  have hnonzero : T.intersection i b ≠ 0 := hab
  exact ⟨b, hbi.symm,
    lt_of_le_of_ne (T.intersection_nonneg i b hbi.symm) (Ne.symm hnonzero)⟩

/-! The diagonal entries provide a useful integral normalization of the row
equations.  The resulting ratios control the total number of edges. -/

private def diagonalRatio (T : NumericalType) (i : Fin T.componentCount) : ℚ :=
  -(T.intersection i i : ℚ) / (T.weight i : ℚ)

private def edgeRatio (T : NumericalType) (i j : Fin T.componentCount) : ℚ :=
  ((T.intersection i j : ℚ) / (T.weight i : ℚ)) *
    ((T.multiplicity j : ℚ) / (T.multiplicity i : ℚ))

/-- The weight of a component, cast to `ℚ`, is nonzero. -/
private lemma weight_cast_ne_zero (T : NumericalType) (i : Fin T.componentCount) :
    (T.weight i : ℚ) ≠ 0 := by
  exact_mod_cast (T.weight_pos i).ne'

/-- The multiplicity of a component, cast to `ℚ`, is nonzero. -/
private lemma multiplicity_cast_ne_zero (T : NumericalType) (i : Fin T.componentCount) :
    (T.multiplicity i : ℚ) ≠ 0 := by
  exact_mod_cast (T.multiplicity_pos i).ne'

/-- The diagonal ratio normalizes the self-intersection by the weight. -/
private lemma weight_mul_diagonalRatio (T : NumericalType) (i : Fin T.componentCount) :
    (T.weight i : ℚ) * diagonalRatio T i = -(T.intersection i i : ℚ) := by
  unfold diagonalRatio
  field_simp [weight_cast_ne_zero T i]

private lemma diagonalRatio_eq_edgeRatio_sum (T : NumericalType)
    (i : Fin T.componentCount) :
    diagonalRatio T i =
      ∑ j ∈ Finset.univ.erase i, edgeRatio T i j := by
  classical
  have hrow := T.intersection_mul_multiplicity i
  rw [← Finset.add_sum_erase Finset.univ
    (fun j => T.intersection i j * T.multiplicity j) (Finset.mem_univ i)] at hrow
  have hrowQ : (T.intersection i i : ℚ) * (T.multiplicity i : ℚ) +
      ∑ j ∈ Finset.univ.erase i,
        (T.intersection i j : ℚ) * (T.multiplicity j : ℚ) = 0 := by
    exact_mod_cast hrow
  have hw := weight_cast_ne_zero T i
  have hm := multiplicity_cast_ne_zero T i
  have hscale : (T.weight i : ℚ) * (T.multiplicity i : ℚ) *
      (∑ j ∈ Finset.univ.erase i, edgeRatio T i j) =
      ∑ j ∈ Finset.univ.erase i,
        (T.intersection i j : ℚ) * (T.multiplicity j : ℚ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    unfold edgeRatio
    field_simp [hw, hm]
  have hdiag : (T.weight i : ℚ) * (T.multiplicity i : ℚ) *
      diagonalRatio T i = -(T.intersection i i : ℚ) * (T.multiplicity i : ℚ) := by
    rw [mul_right_comm, weight_mul_diagonalRatio]
  apply (mul_left_cancel₀ (mul_ne_zero hw hm))
  rw [hdiag, hscale]
  linarith

private lemma edgeRatio_nonneg (T : NumericalType) (i j : Fin T.componentCount)
    (hij : i ≠ j) : 0 ≤ edgeRatio T i j := by
  unfold edgeRatio
  apply mul_nonneg
  · exact div_nonneg (by exact_mod_cast T.intersection_nonneg i j hij)
      (le_of_lt (by exact_mod_cast T.weight_pos i))
  · exact div_nonneg (by exact_mod_cast (le_of_lt (T.multiplicity_pos j)))
      (le_of_lt (by exact_mod_cast T.multiplicity_pos i))

private lemma edgeRatio_pair_ge_two (T : NumericalType) (i j : Fin T.componentCount)
    (hij : i ≠ j) (hpos : 0 < T.intersection i j) :
    2 ≤ edgeRatio T i j + edgeRatio T j i := by
  obtain ⟨qᵢ, hqᵢ⟩ := T.weight_dvd_intersection i j
  obtain ⟨qⱼ, hqⱼ⟩ := T.weight_dvd_intersection j i
  have hqiPos : 0 < qᵢ := by
    rw [hqᵢ] at hpos
    have := T.weight_pos i
    nlinarith
  have hqjPos : 0 < qⱼ := by
    have hpos' : 0 < T.intersection j i := by simpa [T.intersection_symm] using hpos
    rw [hqⱼ] at hpos'
    have := T.weight_pos j
    nlinarith
  have hqicast : (T.intersection i j : ℚ) =
      (T.weight i : ℚ) * qᵢ := by exact_mod_cast hqᵢ
  have hqjcast : (T.intersection j i : ℚ) =
      (T.weight j : ℚ) * qⱼ := by exact_mod_cast hqⱼ
  have hqi : 1 ≤ (qᵢ : ℚ) := by exact_mod_cast (show 1 ≤ qᵢ by omega)
  have hqj : 1 ≤ (qⱼ : ℚ) := by exact_mod_cast (show 1 ≤ qⱼ by omega)
  have hmi := multiplicity_cast_ne_zero T i
  have hmj := multiplicity_cast_ne_zero T j
  have hwi := weight_cast_ne_zero T i
  have hwj := weight_cast_ne_zero T j
  have hx : edgeRatio T i j = (qᵢ : ℚ) *
      ((T.multiplicity j : ℚ) / (T.multiplicity i : ℚ)) := by
    unfold edgeRatio
    rw [hqicast]
    field_simp [hwi]
  have hy : edgeRatio T j i = (qⱼ : ℚ) *
      ((T.multiplicity i : ℚ) / (T.multiplicity j : ℚ)) := by
    unfold edgeRatio
    rw [hqjcast]
    field_simp [hwj]
  have hprodEq : edgeRatio T i j * edgeRatio T j i = (qᵢ : ℚ) * qⱼ := by
    rw [hx, hy]
    field_simp [hmi, hmj]
  have hqprod : 1 ≤ (qᵢ : ℚ) * qⱼ := by
    have haux := mul_nonneg (sub_nonneg.mpr hqi) (sub_nonneg.mpr hqj)
    nlinarith
  have hprod : 1 ≤ edgeRatio T i j * edgeRatio T j i := by
    rw [hprodEq]
    exact hqprod
  have hxnonneg := edgeRatio_nonneg T i j hij
  have hynonneg := edgeRatio_nonneg T j i hij.symm
  nlinarith [sq_nonneg (edgeRatio T i j - edgeRatio T j i)]

private lemma sum_diagonalRatio_ge_two_edgeCount (T : NumericalType) :
    2 * (edgeCount T : ℚ) ≤ ∑ i, diagonalRatio T i := by
  classical
  let N (i : Fin T.componentCount) :=
    (Finset.univ.erase i).filter fun j => 0 < T.intersection i j
  let P : Finset (Fin T.componentCount × Fin T.componentCount) :=
    Finset.univ.filter fun ij => ij.1 ≠ ij.2 ∧ 0 < T.intersection ij.1 ij.2
  have hmem (ij : Fin T.componentCount × Fin T.componentCount) :
      ij ∈ P ↔ ij.1 ∈ Finset.univ ∧ ij.2 ∈ N ij.1 := by
    simp [P, N, Finset.mem_erase, ne_comm, and_comm]
  have hsumP (f : Fin T.componentCount → Fin T.componentCount → ℚ) :
      (∑ i, ∑ j ∈ N i, f i j) = ∑ ij ∈ P, f ij.1 ij.2 := by
    symm
    exact Finset.sum_finset_product P Finset.univ N hmem
  have hswap : (∑ ij ∈ P, edgeRatio T ij.1 ij.2) =
      ∑ ij ∈ P, edgeRatio T ij.2 ij.1 := by
    apply Finset.sum_equiv (Equiv.prodComm _ _)
    · intro ij
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and,
        Equiv.prodComm_apply]
      constructor
      · rintro ⟨hne, hpos⟩
        exact ⟨hne.symm, by simpa [T.intersection_symm] using hpos⟩
      · rintro ⟨hne, hpos⟩
        exact ⟨hne.symm, by simpa [T.intersection_symm] using hpos⟩
    · intro ij hij
      rfl
  have hpairsum :
      (∑ ij ∈ P, (edgeRatio T ij.1 ij.2 + edgeRatio T ij.2 ij.1)) =
        2 * (∑ ij ∈ P, edgeRatio T ij.1 ij.2) := by
    rw [Finset.sum_add_distrib, hswap]
    ring
  have hpairLower : (2 * (P.card : ℚ)) ≤
      ∑ ij ∈ P, (edgeRatio T ij.1 ij.2 + edgeRatio T ij.2 ij.1) := by
    calc
      2 * (P.card : ℚ) = ∑ ij ∈ P, (2 : ℚ) := by simp; ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro ij hij
        exact edgeRatio_pair_ge_two T ij.1 ij.2
          (Finset.mem_filter.mp hij).2.1 (Finset.mem_filter.mp hij).2.2
  have hNsum : ∑ i, (N i).card = 2 * edgeCount T := by
    have hN : ∀ i, (N i).card = neighborCount T i := by
      intro i
      unfold N neighborCount neighbors
      congr 1
      ext j
      simp [Finset.mem_filter, Finset.mem_erase, ne_comm]
    calc
      _ = ∑ i, neighborCount T i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hN i
      _ = _ := sum_neighborCount_eq_two_edgeCount T
  have hcard : (P.card : ℚ) = 2 * edgeCount T := by
    calc
      (P.card : ℚ) = ∑ ij ∈ P, (1 : ℚ) := by simp
      _ = ∑ i, ∑ j ∈ N i, (1 : ℚ) := (hsumP (fun _ _ => 1)).symm
      _ = ∑ i, (N i).card := by simp
      _ = (2 * edgeCount T : ℚ) := by exact_mod_cast hNsum
  have hPbound : 2 * (2 * edgeCount T : ℚ) ≤
      2 * (∑ ij ∈ P, edgeRatio T ij.1 ij.2) := by
    rw [← hcard]
    calc
      2 * (P.card : ℚ) ≤
          ∑ ij ∈ P, (edgeRatio T ij.1 ij.2 + edgeRatio T ij.2 ij.1) := hpairLower
      _ = 2 * (∑ ij ∈ P, edgeRatio T ij.1 ij.2) := hpairsum
  have hfull : (∑ i, ∑ j ∈ Finset.univ.erase i, edgeRatio T i j) ≥
      ∑ i, ∑ j ∈ N i, edgeRatio T i j := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      exact (Finset.mem_filter.mp hj).1
    · intro j hj hjN
      exact edgeRatio_nonneg T i j (Finset.mem_erase.mp hj).1.symm
  calc
    2 * (edgeCount T : ℚ) ≤ ∑ ij ∈ P, edgeRatio T ij.1 ij.2 := by
      nlinarith [hPbound]
    _ = ∑ i, ∑ j ∈ N i, edgeRatio T i j := (hsumP _).symm
    _ ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, edgeRatio T i j := hfull
    _ = ∑ i, diagonalRatio T i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (diagonalRatio_eq_edgeRatio_sum T i).symm

private lemma diagonalRatio_pos_and_integral (T : NumericalType)
    (hn : 1 < T.componentCount) (i : Fin T.componentCount) :
    ∃ c : ℤ, 0 < c ∧ diagonalRatio T i = c := by
  obtain ⟨d, hd⟩ := T.weight_dvd_intersection i i
  have hc : diagonalRatio T i = -d := by
    have hdcast : (T.intersection i i : ℚ) =
        (T.weight i : ℚ) * d := by exact_mod_cast hd
    apply mul_left_cancel₀ (weight_cast_ne_zero T i)
    rw [weight_mul_diagonalRatio, hdcast]
    ring
  have hsum := diagonalRatio_eq_edgeRatio_sum T i
  obtain ⟨j, hij, hpos⟩ := exists_neighbor T hn i
  have hjpos : 0 < edgeRatio T i j := by
    unfold edgeRatio
    have ha : 0 < (T.intersection i j : ℚ) := by exact_mod_cast hpos
    have hw : 0 < (T.weight i : ℚ) := by exact_mod_cast T.weight_pos i
    have hmi : 0 < (T.multiplicity i : ℚ) := by exact_mod_cast T.multiplicity_pos i
    have hmj : 0 < (T.multiplicity j : ℚ) := by exact_mod_cast T.multiplicity_pos j
    positivity
  have hjmem : j ∈ Finset.univ.erase i := by
    simp [hij, ne_comm]
  have hsumge : edgeRatio T i j ≤
      ∑ k ∈ Finset.univ.erase i, edgeRatio T i k :=
    Finset.single_le_sum
      (fun k hk => edgeRatio_nonneg T i k (Finset.mem_erase.mp hk).1.symm) hjmem
  have hpositive : 0 < diagonalRatio T i := by
    rw [hsum]
    exact lt_of_lt_of_le hjpos hsumge
  refine ⟨-d, ?_, hc⟩
  have hposQ : (0 : ℚ) < -d := by simpa [hc] using hpositive
  exact_mod_cast hposQ

private lemma diagonalRatio_ge_two_of_genus_zero (T : NumericalType)
    (hT : IsMinimal T) (hn : 1 < T.componentCount) (i : Fin T.componentCount)
    (hgen : T.componentGenus i = 0) :
    (2 : ℚ) ≤ diagonalRatio T i := by
  obtain ⟨c, hcpos, hratio⟩ := diagonalRatio_pos_and_integral T hn i
  have hcne : c ≠ 1 := by
    intro heq
    apply hT
    refine ⟨i, hgen, ?_⟩
    have hdiag : (T.intersection i i : ℚ) = -(T.weight i : ℚ) := by
      have := weight_mul_diagonalRatio T i
      rw [hratio, heq] at this
      push_cast at this
      linarith
    exact_mod_cast hdiag
  have hcle : 2 ≤ c := by omega
  rw [hratio]
  exact_mod_cast hcle

private lemma genus_cast_eq_diagonalRatioSum (T : NumericalType) :
    (genus T : ℚ) = 1 + ∑ i,
      (T.multiplicity i : ℚ) * (T.weight i : ℚ) *
        ((T.componentGenus i : ℚ) - 1 + diagonalRatio T i / 2) := by
  rw [cast_genus T]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  linear_combination -(T.multiplicity i : ℚ) * weight_mul_diagonalRatio T i / 2

private lemma diagonalRatio_local_bound (T : NumericalType)
    (hT : IsMinimal T) (hn : 1 < T.componentCount)
    (i : Fin T.componentCount) :
    ((1 : ℚ) / 2) * (diagonalRatio T i - 2) ≤
      (T.multiplicity i : ℚ) * (T.weight i : ℚ) *
        ((T.componentGenus i : ℚ) - 1 + diagonalRatio T i / 2) := by
  obtain ⟨c, hcpos, hratio⟩ := diagonalRatio_pos_and_integral T hn i
  have hs : (1 : ℚ) ≤ (T.multiplicity i : ℚ) * (T.weight i : ℚ) := by
    have hp := mul_pos (T.multiplicity_pos i) (T.weight_pos i)
    exact_mod_cast (show 1 ≤ T.multiplicity i * T.weight i by omega)
  have hgen : 0 ≤ T.componentGenus i := T.componentGenus_nonneg i
  by_cases hgen0 : T.componentGenus i = 0
  · have hdiag : (2 : ℚ) ≤ diagonalRatio T i :=
      diagonalRatio_ge_two_of_genus_zero T hT hn i hgen0
    rw [hgen0]
    push_cast
    have hcm : 0 ≤ diagonalRatio T i - 2 := by linarith
    have hmul : 0 ≤
        (((T.multiplicity i : ℚ) * (T.weight i : ℚ)) - 1) *
          (diagonalRatio T i - 2) :=
      mul_nonneg (by linarith [hs]) hcm
    nlinarith
  · have hgen1 : (1 : ℚ) ≤ (T.componentGenus i : ℚ) := by
      have hgi : 1 ≤ T.componentGenus i := by omega
      exact_mod_cast hgi
    have hdpos : (1 : ℚ) ≤ diagonalRatio T i := by
      rw [hratio]
      exact_mod_cast (show 1 ≤ c by omega)
    have hA : 0 ≤
        ((T.multiplicity i : ℚ) * (T.weight i : ℚ)) *
          ((T.componentGenus i : ℚ) - 1) :=
      mul_nonneg (by positivity) (by linarith [hgen1])
    have hB : 0 ≤
        (((T.multiplicity i : ℚ) * (T.weight i : ℚ)) - 1) *
          diagonalRatio T i :=
      mul_nonneg (by linarith [hs]) (by linarith [hdpos])
    nlinarith

/-- The topological genus of a minimal numerical type with more than one
component is at most its genus. -/
@[stacks 0C7C]
public lemma one_sub_componentCount_add_edgeCount_le_genus_of_isMinimal
    (T : NumericalType) (hT : IsMinimal T) (hn : 1 < T.componentCount) :
    (1 : ℤ) - T.componentCount + edgeCount T ≤ genus T := by
  have hlocal :
      ∑ i, ((1 : ℚ) / 2) * (diagonalRatio T i - 2) ≤
        ∑ i, (T.multiplicity i : ℚ) * (T.weight i : ℚ) *
          ((T.componentGenus i : ℚ) - 1 + diagonalRatio T i / 2) := by
    apply Finset.sum_le_sum
    intro i hi
    exact diagonalRatio_local_bound T hT hn i
  have hedge := sum_diagonalRatio_ge_two_edgeCount T
  have hsumHalf :
      ∑ i, ((1 : ℚ) / 2) * (diagonalRatio T i - 2) =
        (∑ i, diagonalRatio T i) / 2 - (T.componentCount : ℚ) := by
    calc
      _ = ∑ i, (diagonalRatio T i - 2) / 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i, (diagonalRatio T i - 2)) / 2 := by rw [Finset.sum_div]
      _ = ((∑ i, diagonalRatio T i) - (T.componentCount : ℚ) * 2) / 2 := by
        rw [Finset.sum_sub_distrib]
        simp [Finset.sum_const]
      _ = (∑ i, diagonalRatio T i) / 2 - (T.componentCount : ℚ) := by ring
  have hcastMain :
      (1 : ℚ) - (T.componentCount : ℚ) + edgeCount T ≤
        (genus T : ℚ) := by
    rw [genus_cast_eq_diagonalRatioSum]
    calc
      (1 : ℚ) - (T.componentCount : ℚ) + edgeCount T ≤
          1 + (∑ i, diagonalRatio T i) / 2 - (T.componentCount : ℚ) := by
        have hedges' : (edgeCount T : ℚ) ≤ (∑ i, diagonalRatio T i) / 2 := by
          linarith
        linarith
      _ = 1 + ∑ i, ((1 : ℚ) / 2) * (diagonalRatio T i - 2) := by
        rw [hsumHalf]
        ring
      _ ≤ 1 + ∑ i, (T.multiplicity i : ℚ) * (T.weight i : ℚ) *
            ((T.componentGenus i : ℚ) - 1 + diagonalRatio T i / 2) :=
        by simpa [add_comm] using add_le_add_left hlocal 1
  exact_mod_cast hcastMain

end AlgebraicGeometry.NumericalType
