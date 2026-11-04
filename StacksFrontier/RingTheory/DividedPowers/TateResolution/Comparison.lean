module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.PolynomialPresentation

/-!
# Comparing two graded divided-power polynomial algebras over the same coefficients

Two graded divided-power polynomial algebras over the same coefficient algebra are compared by
sending coefficients to coefficients and each variable to a variable of the same degree. This
file assembles that comparison out of the graded universal property, which
`exists_gradedDividedPowerPolynomial_of_indices` returns alongside the algebra it builds.

The comparison is what lets a degree-by-degree construction of a Tate resolution choose the
boundary of a new variable in the algebra built so far and then transport it to the final
algebra: the truncated index family `fun n => {x : idx n // n < k}` maps to the full family `idx`
by `Subtype.val`, degree for degree, so the comparison applies to it.

## Main results

* `DividedPowers.TateResolution.DividedPowerStructure.dpow_eval_zero` — a positive divided power
  of zero is zero.
* `DividedPowers.TateResolution.mem_grade_of_mem_degreeZeroGrade` — a map of the coefficient
  algebra landing in degree zero is graded for the degree-zero grading of the source.
* `DividedPowers.TateResolution.exists_comparison_of_indexMap` — the comparison map determined by
  a degree-preserving map of index families.

## Implementation notes

The universal property is taken as a hypothesis rather than as a field of
`GradedDividedPowerPolynomial`, because the structure does not record it; it is supplied at a use
site by the conclusion of `exists_gradedDividedPowerPolynomial_of_indices`, instantiated at the
target algebra. Taking it already instantiated keeps the hypothesis short and avoids a second
universe parameter for the target.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w z

namespace DividedPowerStructure

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-- A positive divided power of zero is zero. Zero lies in the positive even part, so
`dpow_null` does not apply; the identity comes from extracting the even factor `0` out of
`0 = 0 * 0`. -/
public theorem dpow_eval_zero (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜) {n : ℕ} (hn : n ≠ 0) : γ.dpow n 0 = 0 := by
  have h : γ.dpow n ((0 : A) * 0) = 0 := by
    rw [γ.dpow_mul_even hn (Submodule.zero_mem _) (Submodule.zero_mem _), zero_pow hn, zero_mul]
  simpa using h

end DividedPowerStructure

section Comparison

variable {R : Type u} {P : Type v} {B : Type w}
  [CommRing R] [CommRing P] [Algebra R P] [Ring B] [Algebra R B]

/-- A map of the coefficient algebra whose image lies in degree zero is graded when the source is
given the grading concentrated in degree zero: in positive degrees the source piece is trivial. -/
public theorem mem_grade_of_mem_degreeZeroGrade (ℬ : ℕ → Submodule R B) (κ : P →ₐ[R] B)
    (hκ : ∀ p : P, κ p ∈ ℬ 0) (m : ℕ) (p : P) (hp : p ∈ degreeZeroGrade R P m) : κ p ∈ ℬ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact hκ p
  · rw [eq_zero_of_mem_degreeZeroGrade R P hm.ne' hp, map_zero]
    exact Submodule.zero_mem _

/-- The divided powers of a map of the coefficient algebra are automatically compatible with the
degree-zero divided powers of the source: the positive even part of a grading concentrated in
degree zero is trivial, so the only element to check is zero. -/
public theorem dpow_comp_of_degreeZero (ℬ : ℕ → Submodule R B) [GradedAlgebra ℬ]
    [IsStrictlyGradedComm ℬ] (δ : DividedPowerStructure ℬ) (κ : P →ₐ[R] B) (n : ℕ) (p : P)
    (hp : p ∈ positiveEvenPart (degreeZeroGrade R P)) :
    δ.dpow n (κ p) = κ ((degreeZeroDividedPowers R P).dpow n p) := by
  have hp0 : p = 0 := by
    rw [positiveEvenPart_degreeZeroGrade] at hp
    simpa using hp
  subst hp0
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [map_zero, δ.dpow_zero (Submodule.zero_mem _),
      (degreeZeroDividedPowers R P).dpow_zero (Submodule.zero_mem _), map_one]
  · rw [map_zero, DividedPowerStructure.dpow_eval_zero ℬ δ hn.ne',
      DividedPowerStructure.dpow_eval_zero (degreeZeroGrade R P)
        (degreeZeroDividedPowers R P) hn.ne', map_zero]

end Comparison

section IndexMap

variable {R : Type u} {P : Type v} {A : Type w} {B : Type z}
  [CommRing R] [CommRing P] [Algebra R P] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

/-- **The comparison map of two graded divided-power polynomial algebras over the same
coefficient algebra**, determined by a degree-preserving map of their index families: it sends
coefficients to coefficients and the variable at `j` to the variable at `e j`, and it is graded
and compatible with the divided powers.

The universal property of the source is a hypothesis because
`GradedDividedPowerPolynomial` does not record it; it is supplied at a use site by the conclusion
of `exists_gradedDividedPowerPolynomial_of_indices` instantiated at the target. Nothing is
assumed about the target beyond its being such an algebra, so this is the comparison of a
truncated family of variables with the full one as well as the comparison of two presentations
of the same algebra. -/
public theorem exists_comparison_of_indexMap
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜) (ι : P →ₐ[R] A)
    (h : GradedDividedPowerPolynomial 𝒜 γ ι)
    (ℬ : ℕ → Submodule R B) [GradedAlgebra ℬ] [IsStrictlyGradedComm ℬ]
    (δ : DividedPowerStructure ℬ) (κ : P →ₐ[R] B)
    (hB : GradedDividedPowerPolynomial ℬ δ κ)
    (huniv : ∀ (f : P →ₐ[R] B) (t : (Σ n : ℕ, h.indices n) → B),
      (∀ (m : ℕ) (p : P), p ∈ degreeZeroGrade R P m → f p ∈ ℬ m) →
      (∀ (n : ℕ) (p : P), p ∈ positiveEvenPart (degreeZeroGrade R P) →
        δ.dpow n (f p) = f ((degreeZeroDividedPowers R P).dpow n p)) →
      (∀ j : Σ n : ℕ, h.indices n, t j ∈ ℬ (j.1 + 1)) →
      ∃! g : A →ₐ[R] B,
        (∀ p : P, g (ι p) = f p) ∧
        (∀ j : Σ n : ℕ, h.indices n, g (h.generator j) = t j) ∧
        (∀ (m : ℕ) (x : A), x ∈ 𝒜 m → g x ∈ ℬ m) ∧
        (∀ (n : ℕ) (x : A), x ∈ positiveEvenPart 𝒜 → δ.dpow n (g x) = g (γ.dpow n x)))
    (e : (Σ n : ℕ, h.indices n) → Σ n : ℕ, hB.indices n) (he : ∀ j, (e j).1 = j.1) :
    ∃ g : A →ₐ[R] B,
      (∀ p : P, g (ι p) = κ p) ∧
      (∀ j : Σ n : ℕ, h.indices n, g (h.generator j) = hB.generator (e j)) ∧
      (∀ (m : ℕ) (x : A), x ∈ 𝒜 m → g x ∈ ℬ m) ∧
      (∀ (n : ℕ) (x : A), x ∈ positiveEvenPart 𝒜 → δ.dpow n (g x) = g (γ.dpow n x)) := by
  obtain ⟨g, hg, -⟩ := huniv κ (fun j => hB.generator (e j))
    (mem_grade_of_mem_degreeZeroGrade ℬ κ hB.coefficient_mem)
    (dpow_comp_of_degreeZero ℬ δ κ)
    (fun j => by
      have hj := hB.generator_mem (e j)
      rwa [he j] at hj)
  exact ⟨g, hg⟩

end IndexMap

end DividedPowers.TateResolution

end
