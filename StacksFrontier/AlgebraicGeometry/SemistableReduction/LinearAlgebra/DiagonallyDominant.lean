module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Gershgorin
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Tactic
public import Mathlib.Tactic.Linarith
public import StacksCore.Tactic.StacksAttribute

/-!
# Diagonally dominant symmetric matrices

Let `A` be a symmetric matrix with nonnegative off-diagonal entries which is
diagonally dominant relative to a strictly positive vector `m`. This file
describes the kernel of `A` and shows that its quadratic form is nonpositive,
with equality exactly along the line spanned by `m` when `A` has connected
support.

These are the linear-algebra inputs to the theory of numerical types: for a
numerical type the intersection matrix is such an `A` and the multiplicity
vector is such an `m`.

## Main results

* `Matrix.ker_mulVecLin_eq_span_indicator`: the kernel is spanned by the
  weighted indicators of the isolated subsets on which diagonal dominance is an
  equality.
* `Matrix.dotProduct_mulVec_nonpos_of_positive_kernel`: the quadratic form of a
  symmetric matrix annihilating a strictly positive vector is nonpositive.
* `Matrix.dotProduct_mulVec_eq_zero_iff_of_positive_kernel`: when no proper
  nonempty set of indices is disconnected from its complement, the zero locus of
  the quadratic form is the line spanned by that positive kernel vector.

## Implementation notes

The finite index set of the source is an arbitrary `Fintype`, or `Fin n` where
the source's enumeration is used. For a set `I` of indices the source's vector
`x_I` is `Set.indicator I m`.

## References

* [Stacks Project, Tag 0C5U](https://stacks.math.columbia.edu/tag/0C5U)
* [Stacks Project, Tag 0C5V](https://stacks.math.columbia.edu/tag/0C5V)
* [Stacks Project, Tag 0C5X](https://stacks.math.columbia.edu/tag/0C5X)
-/

@[expose] public section

open Matrix

namespace Matrix

/-! ### The kernel -/

/-- The kernel of a symmetric matrix with nonnegative off-diagonal entries,
diagonally dominant relative to a positive vector `m`, is spanned by the
weighted indicator vectors of its isolated equality subsets. -/
@[stacks 0C5V]
public lemma ker_mulVecLin_eq_span_indicator {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (m : Fin n → ℝ)
    (hA : A.IsSymm)
    (hoff : ∀ i j, i ≠ j → 0 ≤ A i j)
    (hm : ∀ i, 0 < m i)
    (hdom : ∀ i, ∑ j ∈ Finset.univ.erase i, A i j * m j ≤ -A i i * m i) :
    LinearMap.ker A.mulVecLin =
      Submodule.span ℝ {x | ∃ I : Set (Fin n),
        x = I.indicator m ∧
        (∀ i ∈ I, ∀ j ∉ I, A i j = 0) ∧
        (∀ i ∈ I, -A i i * m i = ∑ j ∈ Finset.univ.erase i, A i j * m j)} := by
  classical
  -- The weighted indicator of an isolated equality subset lies in the kernel.
  have hind (I : Set (Fin n)) (hzero : ∀ i ∈ I, ∀ j ∉ I, A i j = 0)
      (heq : ∀ i ∈ I, -A i i * m i = ∑ j ∈ Finset.univ.erase i, A i j * m j) :
      A *ᵥ I.indicator m = 0 := by
    ext i
    show (∑ j : Fin n, A i j * I.indicator m j) = 0
    by_cases hi : i ∈ I
    · have hsum : (∑ j ∈ Finset.univ.erase i, A i j * I.indicator m j) =
          ∑ j ∈ Finset.univ.erase i, A i j * m j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hjI : j ∈ I
        · simp [Set.indicator_of_mem hjI]
        · simp [Set.indicator, hjI, hzero i hi j hjI]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), Set.indicator_of_mem hi, hsum,
        ← heq i hi]
      ring
    · refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hjI : j ∈ I
      · rw [← hA.apply i j, hzero j hjI i hi, zero_mul]
      · simp [Set.indicator, hjI]
  -- A kernel vector `u ≤ t • m` with equality at `i` makes row `i` tight there.
  have htight (u : Fin n → ℝ) (t : ℝ) (hu : A *ᵥ u = 0) (ht : 0 ≤ t)
      (hle : ∀ j, u j ≤ t * m j) (i : Fin n) (hi : u i = t * m i) :
      (∀ j ∈ Finset.univ.erase i, A i j * (t * m j - u j) = 0) ∧
        t * ∑ j ∈ Finset.univ.erase i, A i j * m j = t * (-A i i * m i) := by
    have hrow : ∑ j ∈ Finset.univ.erase i, A i j * u j = -A i i * u i := by
      have h : ∑ j, A i j * u j = 0 := congrFun hu i
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at h
      linarith
    have hnn : ∀ j ∈ Finset.univ.erase i, 0 ≤ A i j * (t * m j - u j) := fun j hj =>
      mul_nonneg (hoff i j (Finset.mem_erase.mp hj).1.symm) (sub_nonneg.mpr (hle j))
    have hsum : ∑ j ∈ Finset.univ.erase i, A i j * (t * m j - u j) =
        t * ∑ j ∈ Finset.univ.erase i, A i j * m j - ∑ j ∈ Finset.univ.erase i, A i j * u j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hrow, hi] at hsum
    have hdom' := mul_le_mul_of_nonneg_left (hdom i) ht
    have hS : ∑ j ∈ Finset.univ.erase i, A i j * (t * m j - u j) = 0 :=
      le_antisymm (by linarith) (Finset.sum_nonneg hnn)
    exact ⟨(Finset.sum_eq_zero_iff_of_nonneg hnn).mp hS, by linarith⟩
  -- A nonzero kernel vector is a multiple of `m` on an isolated equality subset
  -- (the coordinates maximizing `|v i / m i|`) on which it does not vanish.
  have hiso (v : Fin n → ℝ) (hv : A *ᵥ v = 0) (hv0 : v ≠ 0) :
      ∃ c : ℝ, ∃ I : Set (Fin n), (∀ i ∈ I, ∀ j ∉ I, A i j = 0) ∧
        (∀ i ∈ I, -A i i * m i = ∑ j ∈ Finset.univ.erase i, A i j * m j) ∧
        (∀ i ∈ I, v i = c * m i) ∧ ∃ p ∈ I, v p ≠ 0 := by
    obtain ⟨p₀, hp₀⟩ : ∃ p, v p ≠ 0 := by
      by_contra! h
      exact hv0 (funext h)
    obtain ⟨p, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => |v i / m i|)
      ⟨p₀, Finset.mem_univ _⟩
    have hp : v p ≠ 0 := by
      intro h
      have := hmax p₀ (Finset.mem_univ _)
      simp only [h, zero_div, abs_zero, abs_nonpos_iff, div_eq_zero_iff] at this
      exact this.elim hp₀ (hm p₀).ne'
    obtain ⟨c, hc⟩ : ∃ c, c = v p / m p := ⟨_, rfl⟩
    have hc0 : c ≠ 0 := by
      rw [hc]
      exact div_ne_zero hp (hm p).ne'
    have hvp : v p = c * m p := by rw [hc, div_mul_cancel₀ _ (hm p).ne']
    have hle (j : Fin n) : c * v j ≤ c ^ 2 * m j := by
      have h : |v j / m j| ≤ |c| := by
        rw [hc]
        exact hmax j (Finset.mem_univ j)
      rw [abs_div, abs_of_pos (hm j), div_le_iff₀ (hm j)] at h
      calc c * v j ≤ |c| * |v j| := by rw [← abs_mul]; exact le_abs_self _
        _ ≤ |c| * (|c| * m j) := mul_le_mul_of_nonneg_left h (abs_nonneg c)
        _ = c ^ 2 * m j := by rw [← mul_assoc, abs_mul_abs_self, sq]
    have hu : A *ᵥ (fun j => c * v j) = 0 := by
      rw [show (fun j => c * v j) = c • v from rfl, Matrix.mulVec_smul, hv, smul_zero]
    let I : Set (Fin n) := {j | c * v j = c ^ 2 * m j}
    have hrow (i : Fin n) (hi : i ∈ I) := htight _ _ hu (sq_nonneg c) hle i hi
    refine ⟨c, I, fun i hi j hj => ?_, fun i hi => ?_, fun i hi => ?_, p, ?_, hp⟩
    · have hji : j ≠ i := by
        rintro rfl
        exact hj hi
      exact (mul_eq_zero.mp ((hrow i hi).1 j (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩))
        ).resolve_right fun h => hj (sub_eq_zero.mp h).symm
    · exact (mul_left_cancel₀ (pow_ne_zero 2 hc0) (hrow i hi).2).symm
    · exact mul_left_cancel₀ hc0 (by rw [show c * v i = c ^ 2 * m i from hi]; ring)
    · show c * v p = c ^ 2 * m p
      rw [hvp]
      ring
  let G : Set (Fin n → ℝ) := {x | ∃ I : Set (Fin n),
    x = I.indicator m ∧
    (∀ i ∈ I, ∀ j ∉ I, A i j = 0) ∧
    (∀ i ∈ I, -A i i * m i = ∑ j ∈ Finset.univ.erase i, A i j * m j)}
  show LinearMap.ker A.mulVecLin = Submodule.span ℝ G
  refine le_antisymm ?_ (Submodule.span_le.mpr ?_)
  · intro x hx
    -- The converse follows by repeatedly removing a maximal weighted coordinate.
    -- We induct on the finite support of the vector.
    let supp (v : Fin n → ℝ) : Finset (Fin n) := Finset.univ.filter fun i => v i ≠ 0
    have key : ∀ k : ℕ, ∀ v : Fin n → ℝ,
        A *ᵥ v = 0 → (supp v).card = k → v ∈ Submodule.span ℝ G := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
        intro v hv hcard
        by_cases hv0 : v = 0
        · subst v
          exact Submodule.zero_mem _
        obtain ⟨c, I, hzero, heq, hval, p, hpI, hp⟩ := hiso v hv hv0
        have hv' : A *ᵥ (v - c • I.indicator m) = 0 := by
          rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hv, hind I hzero heq,
            smul_zero, sub_zero]
        have hss : supp (v - c • I.indicator m) ⊂ supp v := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, fun h => ?_⟩
          · intro j hj
            by_cases hjI : j ∈ I
            · simp [supp, Set.indicator_of_mem hjI, hval j hjI] at hj
            · simpa [supp, Set.indicator, hjI] using hj
          · have hp' : p ∈ supp (v - c • I.indicator m) := by
              rw [h]
              simpa [supp] using hp
            simp [supp, Set.indicator_of_mem hpI, hval p hpI] at hp'
        rw [show v = c • I.indicator m + (v - c • I.indicator m) by abel]
        refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ?_))
          (ih _ (by rw [← hcard]; exact Finset.card_lt_card hss) _ hv' rfl)
        exact ⟨I, rfl, hzero, heq⟩
    exact key _ x (LinearMap.mem_ker.mp hx) rfl
  · rintro x ⟨I, rfl, hzero, heq⟩
    exact LinearMap.mem_ker.mpr (hind I hzero heq)

/-! ### The quadratic form -/

variable {ι R : Type*} [Fintype ι] [Field R] [LinearOrder R] [IsStrictOrderedRing R]

omit [Fintype ι] in private lemma weighted_square_nonneg {A : Matrix ι ι R} {m y : ι → R}
    (hoff : ∀ i j, i ≠ j → 0 ≤ A i j) (hm : ∀ i, 0 < m i) (i j : ι) :
    0 ≤ A i j * m i * m j * (y i - y j) ^ 2 := by
  by_cases hij : i = j
  · subst j
    simp
  · exact mul_nonneg
      (mul_nonneg (mul_nonneg (hoff i j hij) (le_of_lt (hm i)))
        (le_of_lt (hm j))) (sq_nonneg _)

omit [LinearOrder R] [IsStrictOrderedRing R] in
private lemma weighted_quadratic_identity
    {A : Matrix ι ι R} {m : ι → R} (hA : A.IsSymm)
    (hAm : A *ᵥ m = 0) (y : ι → R) :
    2 * ((fun i => m i * y i) ⬝ᵥ
      (A *ᵥ (fun i => m i * y i))) =
      -∑ i, ∑ j, A i j * m i * m j * (y i - y j) ^ 2 := by
  classical
  have hrow (i : ι) : ∑ j, A i j * m j = 0 := by
    simpa only [Matrix.mulVec, dotProduct, Pi.zero_apply] using congrFun hAm i
  have hzero (i : ι) : ∑ j, A i j * m i * m j * (y i) ^ 2 = 0 := by
    calc
      _ = (m i * (y i) ^ 2) * ∑ j, A i j * m j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by simp [hrow]
  have hsym : (∑ i, ∑ j, A i j * m i * m j * (y j) ^ 2) =
      ∑ i, ∑ j, A i j * m i * m j * (y i) ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hA.apply]
    ring
  simp only [Matrix.mulVec, dotProduct]
  calc
    2 * (∑ i, m i * y i * ∑ j, A i j * (m j * y j)) =
        ∑ i, ∑ j, 2 * (A i j * m i * m j * (y i * y j)) := by
          simp_rw [Finset.mul_sum]
          congr 1; ext i; congr 1; ext j; ring
    _ = -∑ i, ∑ j, A i j * m i * m j * (y i - y j) ^ 2 := by
      simp_rw [sub_sq, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [hsym, Finset.sum_eq_zero fun i _ => hzero i]
      simp only [zero_sub, neg_neg, add_zero]
      congr 1; ext i; congr 1; ext j; ring

/-- A symmetric matrix with nonnegative off-diagonal entries which kills a
strictly positive vector has nonpositive associated quadratic form. -/
@[stacks 0C5X "negative semidefiniteness"]
lemma dotProduct_mulVec_nonpos_of_positive_kernel
    {A : Matrix ι ι R} {m : ι → R} (hA : A.IsSymm)
    (hoffDiag : ∀ i j, i ≠ j → 0 ≤ A i j) (hm : ∀ i, 0 < m i)
    (hAm : A *ᵥ m = 0) (x : ι → R) :
    x ⬝ᵥ (A *ᵥ x) ≤ 0 := by
  classical
  let y : ι → R := fun i => x i / m i
  have hxy : (fun i => m i * y i) = x := funext fun i => mul_div_cancel₀ (x i) (hm i).ne'
  have hsum : 0 ≤ ∑ i, ∑ j, A i j * m i * m j * (y i - y j) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      weighted_square_nonneg hoffDiag hm i j
  have hid := weighted_quadratic_identity hA hAm y
  rw [hxy] at hid
  linarith

/-- If, in addition, no proper nonempty set of indices is disconnected from
its complement, the zero locus of the quadratic form is the line spanned by
the positive kernel vector. -/
@[stacks 0C5X "equality case"]
lemma dotProduct_mulVec_eq_zero_iff_of_positive_kernel
    {A : Matrix ι ι R} {m x : ι → R} (hA : A.IsSymm)
    (hoffDiag : ∀ i j, i ≠ j → 0 ≤ A i j) (hm : ∀ i, 0 < m i)
    (hAm : A *ᵥ m = 0)
    (hconnected : ∀ I : Set ι, I.Nonempty → I ≠ Set.univ →
      ¬ ∀ i ∈ I, ∀ j ∉ I, A i j = 0) :
    x ⬝ᵥ (A *ᵥ x) = 0 ↔ ∃ q : R, x = q • m := by
  classical
  refine ⟨fun hx => ?_, ?_⟩
  · let y : ι → R := fun i => x i / m i
    have hxy (i : ι) : m i * y i = x i := mul_div_cancel₀ (x i) (hm i).ne'
    have hsum : (∑ i, ∑ j, A i j * m i * m j * (y i - y j) ^ 2) = 0 := by
      have hid := weighted_quadratic_identity hA hAm y
      simp only [hxy, hx, mul_zero] at hid
      exact neg_eq_zero.mp hid.symm
    have hterm (i j : ι) := weighted_square_nonneg hoffDiag hm (y := y) i j
    have hedge (i j : ι) (hij : A i j ≠ 0) : y i = y j := by
      have houter := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        fun i _ => Finset.sum_nonneg fun j _ => hterm i j).mp hsum i (Finset.mem_univ i)
      have hinner := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        fun j _ => hterm i j).mp houter j (Finset.mem_univ j)
      have hsquare : (y i - y j) ^ 2 = 0 := (mul_eq_zero.mp hinner).resolve_left
        (mul_ne_zero (mul_ne_zero hij (hm i).ne') (hm j).ne')
      exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hsquare)
    by_cases hι : Nonempty ι
    · let i₀ : ι := Classical.choice hι
      have hall (i : ι) : y i = y i₀ := by
        by_contra hne
        let I : Set ι := {j | y j = y i₀}
        exact hconnected I ⟨i₀, rfl⟩ (fun hI => hne (Set.eq_univ_iff_forall.mp hI i))
          fun j hj k hk => Classical.byContradiction fun hAne =>
            hk ((hedge j k hAne).symm.trans hj)
      refine ⟨y i₀, ?_⟩
      funext i
      show x i = y i₀ * m i
      rw [← hxy i, hall i]
      ring
    · refine ⟨0, ?_⟩
      funext i
      exact (hι ⟨i⟩).elim
  · rintro ⟨q, rfl⟩
    simp [Matrix.mulVec_smul, hAm]

/-! ### Strict diagonal dominance relative to a weight vector -/

/-- **Stacks 0C5U, part (2).** A square matrix over a normed field whose diagonal strictly
dominates its off-diagonal entries after weighting the columns by a vector `m` has nonzero
determinant.

Weighting the columns is right multiplication by `Matrix.diagonal m`, whose determinant is the
product of the `m i`, so the weighted matrix has nonzero determinant by part (1) and the
determinants differ by that product. Positivity of the weights is not needed: the hypothesis
already forces each `m i` to be nonzero. -/
@[stacks 0C5U "part (2)"]
public theorem det_ne_zero_of_sum_row_lt_diag_weighted {K n : Type*} [NormedField K] [Fintype n]
    [DecidableEq n] (A : Matrix n n K) (m : n → K)
    (h : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j * m j‖ < ‖A i i * m i‖) :
    A.det ≠ 0 := by
  have hB : (A * Matrix.diagonal m).det ≠ 0 :=
    det_ne_zero_of_sum_row_lt_diag fun k => by simpa [Matrix.mul_diagonal] using h k
  rw [Matrix.det_mul] at hB
  exact left_ne_zero_of_mul hB

end Matrix

/-! ### Strict diagonal dominance without weights

Part (1) of Stacks 0C5U, that a square matrix over a normed field whose diagonal entry in each row
strictly dominates the sum of the norms of the other entries of that row has nonzero determinant,
is `det_ne_zero_of_sum_row_lt_diag`.
-/

add_to_stacks 0C5U "part (1)" det_ne_zero_of_sum_row_lt_diag
