module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ChosenDifferential
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.GradeOne

/-!
# The augmentation kills every boundary

An augmentation of a graded divided-power polynomial algebra which vanishes in every positive
degree kills the differential prescribed by a boundary as soon as it kills the boundary of every
variable of degree one. This is the `augmentation_differential` field of a Tate resolution, and
the hypothesis is the only part of it that constrains the prescribed boundary: in every other
degree the conclusion already follows from vanishing in positive degrees.

The reduction is by degree. An element of degree zero is killed by the differential outright. An
element of degree `n + 2` has its differential in degree `n + 1`, which is positive, so the
augmentation kills it. Only degree one is left, and there `grade_one_le_span` writes the element
as a combination of coefficients and coefficient multiples of the variables of degree one; the
differential of a coefficient vanishes and the differential of `coefficient p * gen j` is
`coefficient p * t j` by the Leibniz rule, since the coefficient has degree zero.

## Main results

* `DividedPowers.TateResolution.IndexedPresentation.augmentation_chosenDifferential_eq_zero` —
  the `augmentation_differential` field, reduced to the boundaries of the variables of degree
  one.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w z

namespace IndexedPresentation

variable {R : Type u} {P : Type v} [CommRing R] [CommRing P] [Algebra R P]
  {idx : ℕ → Type (max u v w)}

variable (T : IndexedPresentation.{u, v, w} R P idx) (t : (Σ n : ℕ, idx n) → T.A)
  (ht : ∀ j, t j ∈ T.grade j.1)

/-- The prescribed differential of a coefficient multiple of a variable of degree one is that
coefficient multiple of the variable's prescribed boundary: the differential kills the
coefficient, and the Leibniz sign in degree zero is `+1`. -/
public theorem chosenDifferential_coefficient_mul_gen (p : P) (j : Σ n : ℕ, idx n)
    (hj : j.1 = 0) :
    T.chosenDifferential t ht (T.coefficient p * T.gen j) = T.coefficient p * t j := by
  have hg1 : T.gen j ∈ T.grade 1 := by
    have hg := T.gen_mem j
    rwa [hj, Nat.zero_add] at hg
  rw [T.chosenDifferential_leibniz t ht 0 1 _ _ (T.coefficient_mem_grade_zero p) hg1,
    T.chosenDifferential_coefficient t ht p, T.chosenDifferential_gen t ht j, zero_mul,
    zero_add, pow_zero, one_smul]

/-- **The `augmentation_differential` field of a Tate resolution, reduced to the variables of
degree one.** An algebra map vanishing in every positive degree kills every prescribed boundary
as soon as it kills the boundaries of the variables of degree one. -/
public theorem augmentation_chosenDifferential_eq_zero {B : Type z} [CommRing B] [Algebra R B]
    (a : T.A →ₐ[R] B)
    (hpos : ∀ (n : ℕ) (x : T.A), 0 < n → x ∈ T.grade n → a x = 0)
    (hzero : ∀ j : Σ n : ℕ, idx n, j.1 = 0 → a (t j) = 0) (x : T.A) :
    a (T.chosenDifferential t ht x) = 0 := by
  classical
  have hspan : ∀ y : T.A, y ∈ Submodule.span R (gradeOneGenerators T.polynomial) →
      a (T.chosenDifferential t ht y) = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
        rcases hz with ⟨p, rfl⟩ | ⟨p, j', hj', rfl⟩
        · rw [T.chosenDifferential_coefficient t ht p, map_zero]
        · have hj2 : (T.indexEquiv.symm j').1 = 0 := by
            rw [T.indexEquiv_symm_fst]; exact hj'
          have hgeq : T.polynomial.generator j' = T.gen (T.indexEquiv.symm j') := by
            rw [IndexedPresentation.gen, T.indexEquiv.apply_symm_apply]
          rw [hgeq, T.chosenDifferential_coefficient_mul_gen t ht p _ hj2, map_mul,
            hzero _ hj2, mul_zero]
    | zero => rw [map_zero, map_zero]
    | add u v _ _ hu hv => rw [map_add, map_add, hu, hv, add_zero]
    | smul r u _ hu => rw [map_smul, map_smul, hu, smul_zero]
  have hone : ∀ y : T.A, y ∈ T.grade 1 → a (T.chosenDifferential t ht y) = 0 :=
    fun y hy => hspan y (grade_one_le_span T.polynomial hy)
  have hdeg : ∀ (n : ℕ) (y : T.A), y ∈ T.grade n → a (T.chosenDifferential t ht y) = 0 := by
    intro n y hy
    match n with
    | 0 => rw [T.chosenDifferential_grade_zero t ht y hy, map_zero]
    | 1 => exact hone y hy
    | (k + 2) =>
        exact hpos (k + 1) _ (Nat.succ_pos k)
          (T.chosenDifferential_mem_grade t ht (k + 1) y hy)
  rw [← DirectSum.sum_support_decompose T.grade x, map_sum, map_sum]
  exact Finset.sum_eq_zero fun n _ => hdeg n _ (DirectSum.decompose T.grade x n).2

end IndexedPresentation

end DividedPowers.TateResolution

end
