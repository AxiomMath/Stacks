module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorConditions
public import StacksFrontier.AlgebraicGeometry.Topologies.WeakNormalization.TwoGeneratorGlue

/-!
# The two charts of the two-generator almost blowup, read on degree-zero fractions

Let `f₁, f₂` be elements of a commutative ring `A` and let `𝒮` be the grading of
`A[T₀,T₁]/(f₂T₀-f₁T₁)`. The modification `X' = Proj 𝒮` is covered by the two standard opens
`D₊(T₀)` and `D₊(T₁)`, whose rings of functions are the degree-zero localizations
`Away 𝒮 T₀` and `Away 𝒮 T₁`, and whose overlap `D₊(T₀T₁)` has ring `Away 𝒮 (T₀T₁)`.

This file proves the two statements about those three rings that [Stacks, Tag 0EVJ] needs:

* the two charts already generate the functions on the overlap, additively;
* a pair of functions on the two charts agreeing on the overlap is a single constant of `A`.

## Main results

* `Stacks.AlmostBlowUp.exists_awayMap_add_awayMap_eq`: every degree-zero fraction on the overlap
  is a sum of one restricted from each chart.
* `Stacks.AlmostBlowUp.exists_chartAwayMap_eq`: **the glueing statement**. Two degree-zero
  fractions, one on each chart, with the same image on the overlap, are the images of one element
  of `A` under the two chart structure maps.

## Implementation notes

Both proofs clear denominators and move to `A[T₀,T₁]`: a degree-zero fraction on `D₊(Tᵢ)` is
`b/Tᵢⁿ` with `b` the class of a form of degree `n`, by
`HomogeneousLocalization.Away.mk_surjective`, and the grading of the relation quotient is the
degreewise image of the polynomial grading, so such a form exists.

The first statement is then the splitting of a form of degree `2n` as `T₁ⁿ` times a form of
degree `n` plus `T₀ⁿ` times a form of degree `n`, which is
`Stacks.AlmostBlowUp.exists_isHomogeneous_X_one_pow_mul_add`; the second is
`Stacks.AlmostBlowUp.exists_const_of_relationForm_mem`.

Degrees are tracked as `n • 1` and `n • (1 + 1)` because that is the shape
`HomogeneousLocalization.Away.mk` produces from a degree-one, resp. degree-two, denominator;
`Stacks.AlmostBlowUp.gradingSmulOne` and `Stacks.AlmostBlowUp.gradingSmulTwo` move memberships to
the normalized degrees `n` and `n * 2`.

## References

* [Stacks Project, Tag 0EVJ](https://stacks.math.columbia.edu/tag/0EVJ)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

namespace Stacks.AlmostBlowUp

universe u

variable {A : Type u} [CommRing A] {f₁ f₂ : A}
  [GradedRing (modificationGrading A f₁ f₂)]

/-! ### Lifting homogeneous elements of the modification ring to forms -/

omit [GradedRing (modificationGrading A f₁ f₂)] in
/-- The class of a form of degree `k` is homogeneous of degree `k`: the grading of the relation
quotient is the degreewise image of the polynomial grading. -/
theorem mk_mem_modificationGrading {k : ℕ} {P : MvPolynomial (Fin 2) A} (hP : P.IsHomogeneous k) :
    Ideal.Quotient.mk (relationIdeal A f₁ f₂) P ∈ modificationGrading A f₁ f₂ k :=
  AddSubgroup.mem_map_of_mem _ ((Submodule.mem_toAddSubgroup _).mpr
    ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr hP))

omit [GradedRing (modificationGrading A f₁ f₂)] in
/-- Every homogeneous element of the modification ring is the class of a form of the same
degree. -/
theorem exists_isHomogeneous_mk_eq {k : ℕ} {c : modificationRing A f₁ f₂}
    (hc : c ∈ modificationGrading A f₁ f₂ k) :
    ∃ P : MvPolynomial (Fin 2) A, P.IsHomogeneous k ∧
      Ideal.Quotient.mk (relationIdeal A f₁ f₂) P = c := by
  obtain ⟨P, hP, hPc⟩ := AddSubgroup.mem_map.mp hc
  exact ⟨P, (MvPolynomial.mem_homogeneousSubmodule _ _).mp
    ((Submodule.mem_toAddSubgroup _).mp hP), hPc⟩

/-- The degree `n • 1` produced by a degree-one denominator is `n`. -/
theorem gradingSmulOne (n : ℕ) : n • 1 = n := by simp

/-- The degree `n • (1 + 1)` produced by a degree-two denominator is `n * 2`. -/
theorem gradingSmulTwo (n : ℕ) : n • (1 + 1) = n * 2 := by simp

/-! ### The two charts generate the functions on the overlap -/

/-- **Every degree-zero fraction on `D₊(T₀T₁)` is a sum of one from each chart.** A fraction on
the overlap is `c/(T₀T₁)ⁿ` with `c` of degree `2n`; splitting a form of degree `2n` as
`T₁ⁿQ₀ + T₀ⁿQ₁` with `Q₀`, `Q₁` of degree `n` writes the fraction as the restriction of `Q₀/T₀ⁿ`
plus the restriction of `Q₁/T₁ⁿ`.

This is the vanishing of the Čech `H¹` of the two-chart cover, and hence of
`H¹(X', 𝒪_{X'})`. -/
theorem exists_awayMap_add_awayMap_eq
    (w : Away (modificationGrading A f₁ f₂)
      (modificationCoord A f₁ f₂ 0 * modificationCoord A f₁ f₂ 1)) :
    ∃ (z₀ : Away (modificationGrading A f₁ f₂) (modificationCoord A f₁ f₂ 0))
      (z₁ : Away (modificationGrading A f₁ f₂) (modificationCoord A f₁ f₂ 1)),
      awayMap (modificationGrading A f₁ f₂) (modificationCoord_mem A f₁ f₂ 1) rfl z₀
        + awayMap (modificationGrading A f₁ f₂) (modificationCoord_mem A f₁ f₂ 0)
            (mul_comm (modificationCoord A f₁ f₂ 0) (modificationCoord A f₁ f₂ 1)) z₁ = w := by
  obtain ⟨n, c, hc, rfl⟩ := Away.mk_surjective (modificationGrading A f₁ f₂)
    (SetLike.mul_mem_graded (modificationCoord_mem A f₁ f₂ 0)
      (modificationCoord_mem A f₁ f₂ 1)) w
  obtain ⟨P, hP, hPc⟩ := exists_isHomogeneous_mk_eq (gradingSmulTwo n ▸ hc)
  obtain ⟨Q₀, Q₁, hQ₀, hQ₁, hsplit⟩ := exists_isHomogeneous_X_one_pow_mul_add n hP
  refine ⟨Away.mk _ (modificationCoord_mem A f₁ f₂ 0) n
      (Ideal.Quotient.mk (relationIdeal A f₁ f₂) Q₀)
      ((gradingSmulOne n).symm ▸ mk_mem_modificationGrading hQ₀),
    Away.mk _ (modificationCoord_mem A f₁ f₂ 1) n
      (Ideal.Quotient.mk (relationIdeal A f₁ f₂) Q₁)
      ((gradingSmulOne n).symm ▸ mk_mem_modificationGrading hQ₁), ?_⟩
  rw [awayMap_mk, awayMap_mk]
  refine HomogeneousLocalization.val_injective _ ?_
  rw [HomogeneousLocalization.val_add, Away.val_mk, Away.val_mk, Away.val_mk,
    Localization.add_mk_self]
  congr 1
  rw [← hPc, hsplit]
  simp only [map_add, map_mul, map_pow, modificationCoord]
  ring

/-- The fraction `b/Tᵢⁿ`, with `b` the class of a form `P`, is the constant `a` once
`Tᵢʲ P - a Tᵢʲ⁺ⁿ` lies in the relation ideal. -/
private theorem away_mk_eq_chartAwayMap (i : Fin 2) {n j : ℕ} {P : MvPolynomial (Fin 2) A}
    {b : modificationRing A f₁ f₂} (hPb : Ideal.Quotient.mk (relationIdeal A f₁ f₂) P = b)
    (hb : b ∈ modificationGrading A f₁ f₂ (n • 1)) (a : A)
    (h : MvPolynomial.X i ^ j * P - MvPolynomial.C a * MvPolynomial.X i ^ (j + n)
      ∈ relationIdeal A f₁ f₂) :
    Away.mk _ (modificationCoord_mem A f₁ f₂ i) n b hb = chartAwayMap A f₁ f₂ i a := by
  rw [← Ideal.Quotient.eq_zero_iff_mem] at h
  simp only [map_mul, map_sub, map_pow, hPb] at h
  refine HomogeneousLocalization.val_injective _ ?_
  rw [Away.val_mk, chartAwayMap_val, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨⟨modificationCoord A f₁ f₂ i ^ j, j, rfl⟩, by
    push_cast
    simp only [modificationCoord]
    linear_combination h⟩

/-! ### Glueing a pair of chart functions to a constant -/

/-- **The glueing statement of [Stacks, Tag 0EVJ].** Two degree-zero fractions, one on `D₊(T₀)`
and one on `D₊(T₁)`, with the same image on the overlap `D₊(T₀T₁)`, are the images of a single
element of `A` under the two chart structure maps.

Clearing the denominators of the equality on the overlap puts a product of powers of `T₀` and
`T₁` times `T₁ᵐP₀ - T₀ⁿP₁` in the relation ideal, which is the hypothesis of
`Stacks.AlmostBlowUp.exists_const_of_relationForm_mem`. -/
theorem exists_chartAwayMap_eq
    (z₀ : Away (modificationGrading A f₁ f₂) (modificationCoord A f₁ f₂ 0))
    (z₁ : Away (modificationGrading A f₁ f₂) (modificationCoord A f₁ f₂ 1))
    (h : awayMap (modificationGrading A f₁ f₂) (modificationCoord_mem A f₁ f₂ 1) rfl z₀
        = awayMap (modificationGrading A f₁ f₂) (modificationCoord_mem A f₁ f₂ 0)
            (mul_comm (modificationCoord A f₁ f₂ 0) (modificationCoord A f₁ f₂ 1)) z₁) :
    ∃ a : A, z₀ = chartAwayMap A f₁ f₂ 0 a ∧ z₁ = chartAwayMap A f₁ f₂ 1 a := by
  obtain ⟨n, b₀, hb₀, rfl⟩ :=
    Away.mk_surjective (modificationGrading A f₁ f₂) (modificationCoord_mem A f₁ f₂ 0) z₀
  obtain ⟨m, b₁, hb₁, rfl⟩ :=
    Away.mk_surjective (modificationGrading A f₁ f₂) (modificationCoord_mem A f₁ f₂ 1) z₁
  obtain ⟨P₀, hP₀, hP₀c⟩ := exists_isHomogeneous_mk_eq (gradingSmulOne n ▸ hb₀)
  obtain ⟨P₁, hP₁, hP₁c⟩ := exists_isHomogeneous_mk_eq (gradingSmulOne m ▸ hb₁)
  rw [awayMap_mk, awayMap_mk] at h
  have hval := congrArg HomogeneousLocalization.val h
  rw [Away.val_mk, Away.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists] at hval
  obtain ⟨c, hc⟩ := hval
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff
    (c : modificationRing A f₁ f₂)
    (modificationCoord A f₁ f₂ 0 * modificationCoord A f₁ f₂ 1)).mp c.property
  rw [← hk] at hc
  have hmemrel : MvPolynomial.X 0 ^ (k + m + 1) * MvPolynomial.X 1 ^ (k + n) *
      (MvPolynomial.X 1 ^ m * P₀ - MvPolynomial.X 0 ^ n * P₁) ∈ relationIdeal A f₁ f₂ := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [map_mul, map_sub, map_pow, hP₀c, hP₁c]
    simp only [modificationCoord] at hc ⊢
    linear_combination Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.X 0) * hc
  obtain ⟨a, j, h₀, h₁⟩ :=
    exists_const_of_relationForm_mem f₁ f₂ (p := k + m + 1) (q := k + n) (by omega) hP₀ hP₁ hmemrel
  exact ⟨a, away_mk_eq_chartAwayMap 0 hP₀c _ a h₀, away_mk_eq_chartAwayMap 1 hP₁c _ a h₁⟩

end Stacks.AlmostBlowUp

end
