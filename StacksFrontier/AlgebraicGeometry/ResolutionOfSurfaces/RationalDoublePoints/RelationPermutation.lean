module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.CaseTwoAlternative
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.CoordinatePredicates

/-!
# Permuting the generators of a quadratic relation

A quadratic relation `Σ aᵢⱼ xᵢxⱼ ∈ 𝔪³` among three generators of the maximal ideal is a relation
among the permuted generators `x ∘ σ`, with the upper triangular coefficient matrix obtained by
permuting and re-symmetrizing `a`. Whether the quadratic form is a scalar times a square does not
change. This lets every statement about the first chart `A[𝔪/x₁]` be applied to the chart of any
of the three generators.

## Main definitions

* `AlgebraicGeometry.permuteRelation`: the permuted upper triangular matrix.

## Main results

* `AlgebraicGeometry.sum_permuteRelation`: the quadratic expression is unchanged by the
  permutation.
* `AlgebraicGeometry.isScalarSqLinear_permuteRelation_iff`: the permuted matrix is a scalar times
  a square if and only if the original one is.
-/

@[expose] public section

open IsLocalRing

universe u

namespace AlgebraicGeometry

variable {R : Type*} [CommRing R]

/-- The upper triangular coefficient matrix of the quadratic form `Σ aᵢⱼ tᵢtⱼ` in the permuted
variables `sₚ = t_{σ p}`. -/
def permuteRelation (a : Fin 3 → Fin 3 → R) (σ : Equiv.Perm (Fin 3)) : Fin 3 → Fin 3 → R :=
  fun p q => if p < q then a (σ p) (σ q) + a (σ q) (σ p) else if p = q then a (σ p) (σ p) else 0

/-- The permuted coefficient matrix is upper triangular. -/
theorem permuteRelation_upper (a : Fin 3 → Fin 3 → R) (σ : Equiv.Perm (Fin 3)) :
    ∀ p q, q < p → permuteRelation a σ p q = 0 := by
  intro p q h
  simp [permuteRelation, not_lt.mpr h.le, h.ne']

/-- The diagonal entry of the permuted matrix at `p` is the diagonal entry of `a` at `σ p`. -/
theorem permuteRelation_diag (a : Fin 3 → Fin 3 → R) (σ : Equiv.Perm (Fin 3)) (p : Fin 3) :
    permuteRelation a σ p p = a (σ p) (σ p) := by
  simp [permuteRelation]

/-- For `p < q`, the sum of the two off-diagonal entries of the permuted matrix at `(p, q)` and
`(q, p)` equals `a (σ p) (σ q) + a (σ q) (σ p)`. -/
theorem permuteRelation_off (a : Fin 3 → Fin 3 → R) (σ : Equiv.Perm (Fin 3)) {p q : Fin 3}
    (h : p < q) :
    permuteRelation a σ p q + permuteRelation a σ q p = a (σ p) (σ q) + a (σ q) (σ p) := by
  simp [permuteRelation, h, not_lt.mpr h.le, h.ne']

/-- The quadratic expression is unchanged by the permutation. -/
theorem sum_permuteRelation (a : Fin 3 → Fin 3 → R) (σ : Equiv.Perm (Fin 3)) (x : Fin 3 → R) :
    ∑ p, ∑ q, permuteRelation a σ p q * (x (σ p) * x (σ q)) = ∑ i, ∑ j, a i j * (x i * x j) := by
  rw [sum_quadratic_congr_of_symm (fun p => x (σ p)) (permuteRelation a σ)
    (fun p q => a (σ p) (σ q)) (fun p => permuteRelation_diag a σ p)
    (fun p q h => permuteRelation_off a σ h),
    ← Equiv.sum_comp σ (fun i => ∑ j, a i j * (x i * x j))]
  exact Finset.sum_congr rfl fun p _ => Equiv.sum_comp σ (fun j => a (σ p) j * (x (σ p) * x j))

/-- Being a scalar times a square is invariant under passing to the permuted upper triangular
matrix. -/
theorem isScalarSqLinear_permuteRelation_iff {k : Type*} [CommRing k] (a : Fin 3 → Fin 3 → k)
    (σ : Equiv.Perm (Fin 3)) :
    IsScalarSqLinear (permuteRelation a σ) ↔ IsScalarSqLinear a := by
  rw [← isScalarSqLinear_comp_perm_iff a σ]
  refine exists_congr fun c => exists_congr fun l => and_congr (forall_congr' fun p => ?_)
    (forall_congr' fun p => forall_congr' fun q => imp_congr_right fun h => ?_)
  · rw [permuteRelation_diag]
  · rw [permuteRelation_off a σ h]

/-- Applying a ring homomorphism entrywise commutes with forming the permuted matrix. -/
theorem permuteRelation_map {S : Type*} [CommRing S] (f : R →+* S) (a : Fin 3 → Fin 3 → R)
    (σ : Equiv.Perm (Fin 3)) (p q : Fin 3) :
    f (permuteRelation a σ p q) = permuteRelation (fun i j => f (a i j)) σ p q := by
  simp only [permuteRelation]
  split_ifs <;> simp

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- If an upper triangular relation `Σ aᵢⱼ xᵢxⱼ ∈ 𝔪³` has a unit coefficient and its residue
quadratic form is not a scalar times a square, then the same holds for the permuted matrix
`permuteRelation a σ` and the permuted generators `x ∘ σ`. -/
theorem exists_permuted_caseOne_relation {x : Fin 3 → A} {a : Fin 3 → Fin 3 → A}
    (_hunit : ∃ p q, p ≤ q ∧ a p q ∉ maximalIdeal A) (_hupper : ∀ p q, q < p → a p q = 0)
    (hrel : ∑ p, ∑ q, a p q * (x p * x q) ∈ maximalIdeal A ^ 3)
    (hcase : ¬ IsScalarSqLinear fun p q => residue A (a p q)) (σ : Equiv.Perm (Fin 3)) :
    (∀ p q, q < p → permuteRelation a σ p q = 0) ∧
      (∃ p q, p ≤ q ∧ permuteRelation a σ p q ∉ maximalIdeal A) ∧
      (∑ p, ∑ q, permuteRelation a σ p q * (x (σ p) * x (σ q))) ∈ maximalIdeal A ^ 3 ∧
      ¬ IsScalarSqLinear fun p q => residue A (permuteRelation a σ p q) := by
  have hcase' : ¬ IsScalarSqLinear fun p q => residue A (permuteRelation a σ p q) := by
    simp only [permuteRelation_map (residue A)]
    rwa [isScalarSqLinear_permuteRelation_iff]
  refine ⟨permuteRelation_upper a σ, ?_, by rwa [sum_permuteRelation], hcase'⟩
  by_contra hall
  push Not at hall
  apply hcase'
  refine ⟨0, fun _ => 0, fun p => ?_, fun p q hpq => ?_⟩
  · simp [(residue_eq_zero_iff _).mpr (hall p p le_rfl)]
  · simp [(residue_eq_zero_iff _).mpr (hall p q hpq.le), permuteRelation_upper a σ q p hpq]

end AlgebraicGeometry

end
