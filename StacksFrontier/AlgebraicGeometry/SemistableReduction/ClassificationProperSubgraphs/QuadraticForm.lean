module

public import Mathlib.Data.Matrix.Mul
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.LinearAlgebra.DiagonallyDominant
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Defs

/-!
# The quadratic form of an intersection matrix on a finite set of components

The classification of proper subgraphs of a numerical type proceeds by
evaluating the quadratic form of the intersection matrix on a vector supported
on finitely many components. This file records the two facts that computation
needs: the value of the form on such a vector is the obvious finite double sum,
and no vector with strictly positive coefficients supported on a *proper* set of
components can lie in the zero locus of the form.

The second statement is the engine of the chapter's nonexistence arguments. The
intersection matrix is negative semidefinite with the multiplicity vector
spanning the zero locus, so a supported vector in the zero locus is a multiple
of the multiplicity vector; since the multiplicity vector is nowhere zero and
the support is proper, the multiple is zero, and then so are the coefficients.

## Main results

* `Matrix.dotProduct_mulVec_sum_single`: the quadratic form of a matrix on a
  linear combination of standard basis vectors.
* `Matrix.dotProduct_mulVec_parallelogram`: the parallelogram law for the
  quadratic form of a matrix.
* `AlgebraicGeometry.NumericalType.intersection_quadratic_nonpos` and
  `AlgebraicGeometry.NumericalType.intersection_quadratic_eq_zero_iff`: the
  intersection form of a numerical type is negative semidefinite, with zero
  locus the line spanned by the multiplicity vector.
* `AlgebraicGeometry.NumericalType.no_positive_supported_kernel`: a strictly
  positive combination of standard basis vectors indexed by a proper subset of
  the components is not in the zero locus of the intersection form.

## Implementation notes

The index map of `Matrix.dotProduct_mulVec_sum_single` is an arbitrary function,
not an embedding: both sides of the identity are unchanged by repetitions, since
a repeated index merely merges coefficients on the left and duplicates terms on
the right in the same way.

## References

* [Stacks Project, Tag 0C5X](https://stacks.math.columbia.edu/tag/0C5X)
-/

@[expose] public section

namespace Matrix

/-- The quadratic form of `A` evaluated on a linear combination of the standard
basis vectors `Pi.single (e r) 1` is the double sum of `A (e r) (e s)` weighted
by the coefficients. -/
public lemma dotProduct_mulVec_sum_single {κ m R : Type*} [Fintype κ]
    [DecidableEq κ] [Fintype m] [CommRing R] (A : Matrix κ κ R) (e : m → κ)
    (c : m → R) :
    (∑ r, c r • (Pi.single (e r) (1 : R))) ⬝ᵥ
        (A *ᵥ (∑ r, c r • (Pi.single (e r) (1 : R)))) =
      ∑ r, ∑ s, c r * A (e r) (e s) * c s := by
  classical
  let x : κ → R := ∑ r, c r • (Pi.single (e r) (1 : R))
  have hx (k : κ) : x k = ∑ r, if e r = k then c r else 0 := by
    simp [x, Pi.single_apply, eq_comm]
  show x ⬝ᵥ (A *ᵥ x) = _
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [hx, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
  simp [mul_assoc]

/-- The parallelogram law for the quadratic form of a matrix. -/
public lemma dotProduct_mulVec_parallelogram {ι R : Type*} [Fintype ι]
    [CommRing R] (A : Matrix ι ι R) (u v : ι → R) :
    (u + v) ⬝ᵥ (A *ᵥ (u + v)) + (u - v) ⬝ᵥ (A *ᵥ (u - v)) =
      2 * (u ⬝ᵥ (A *ᵥ u)) + 2 * (v ⬝ᵥ (A *ᵥ v)) := by
  simp [Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct,
    sub_dotProduct, dotProduct_add, dotProduct_sub]
  ring

end Matrix

open Matrix

namespace AlgebraicGeometry.NumericalType

/-- The intersection matrix of a numerical type, over the rationals. -/
public def ratIntersection (T : NumericalType) :
    Matrix (Fin T.componentCount) (Fin T.componentCount) ℚ :=
  fun s t => (T.intersection s t : ℚ)

private lemma ratIntersection_isSymm (T : NumericalType) :
    (ratIntersection T).IsSymm := by
  ext i j
  show (T.intersection j i : ℚ) = (T.intersection i j : ℚ)
  exact_mod_cast T.intersection_symm j i

private lemma ratIntersection_offDiag_nonneg (T : NumericalType) :
    ∀ i j, i ≠ j → 0 ≤ ratIntersection T i j := fun i j hij => by
  simpa [ratIntersection] using T.intersection_nonneg i j hij

private lemma ratMultiplicity_pos (T : NumericalType) :
    ∀ i, 0 < ((T.multiplicity i : ℚ)) := fun i => mod_cast T.multiplicity_pos i

private lemma ratIntersection_mulVec_multiplicity (T : NumericalType) :
    ratIntersection T *ᵥ (fun i => (T.multiplicity i : ℚ)) = 0 := by
  ext i
  simpa [Matrix.mulVec, dotProduct, ratIntersection] using
    congrArg (Int.cast : ℤ → ℚ) (T.intersection_mul_multiplicity i)

private lemma ratIntersection_connected (T : NumericalType) :
    ∀ I : Set (Fin T.componentCount), I.Nonempty → I ≠ Set.univ →
      ¬ ∀ i ∈ I, ∀ j ∉ I, ratIntersection T i j = 0 := fun I hne hneq hcut =>
  T.connected ⟨I, hne, hneq, fun i hi j hj => by simpa [ratIntersection] using hcut i hi j hj⟩

/-- The quadratic form of the intersection matrix of a numerical type is
nonpositive: the matrix is symmetric with nonnegative off-diagonal entries and
annihilates the strictly positive multiplicity vector. -/
public lemma intersection_quadratic_nonpos (T : NumericalType)
    (x : Fin T.componentCount → ℚ) :
    x ⬝ᵥ (ratIntersection T *ᵥ x) ≤ 0 :=
  Matrix.dotProduct_mulVec_nonpos_of_positive_kernel
    (ratIntersection_isSymm T) (ratIntersection_offDiag_nonneg T)
    (ratMultiplicity_pos T) (ratIntersection_mulVec_multiplicity T) x

/-- The zero locus of the intersection form of a numerical type is the line
spanned by its multiplicity vector. -/
public lemma intersection_quadratic_eq_zero_iff (T : NumericalType)
    (x : Fin T.componentCount → ℚ) :
    x ⬝ᵥ (ratIntersection T *ᵥ x) = 0 ↔
      ∃ q : ℚ, x = q • fun i => (T.multiplicity i : ℚ) :=
  Matrix.dotProduct_mulVec_eq_zero_iff_of_positive_kernel
    (ratIntersection_isSymm T) (ratIntersection_offDiag_nonneg T)
    (ratMultiplicity_pos T) (ratIntersection_mulVec_multiplicity T)
    (ratIntersection_connected T)

/-- An embedding `Fin m ↪ Fin n` with `m < n` misses some element of `Fin n`. -/
private lemma exists_not_range_fin (m n : ℕ) (e : Fin m ↪ Fin n) (hm : m < n) :
    ∃ k : Fin n, ∀ j, e j ≠ k := by
  by_contra! h
  have hcard := Fintype.card_le_of_surjective e h
  simp only [Fintype.card_fin] at hcard
  omega

/-- No strictly positive combination of the standard basis vectors indexed by a
proper subset of the components of a numerical type annihilates the quadratic
form of the intersection matrix. -/
public lemma no_positive_supported_kernel (T : NumericalType) (m : ℕ)
    (e : Fin m ↪ Fin T.componentCount) (hm : m < T.componentCount)
    (hmpos : 0 < m)
    (c : Fin m → ℤ) (hc : ∀ j, 0 < c j)
    (hquad : ∑ r, ∑ s, c r * T.intersection (e r) (e s) * c s = 0) : False := by
  classical
  let cQ : Fin m → ℚ := fun i => (c i : ℚ)
  let x : Fin T.componentCount → ℚ := ∑ r, cQ r • Pi.single (e r) (1 : ℚ)
  have hxquad : x ⬝ᵥ (ratIntersection T *ᵥ x) = 0 := by
    show (∑ r, cQ r • Pi.single (e r) 1) ⬝ᵥ
      (ratIntersection T *ᵥ (∑ r, cQ r • Pi.single (e r) 1)) = 0
    rw [Matrix.dotProduct_mulVec_sum_single (ratIntersection T) (fun r => e r) cQ]
    simpa [ratIntersection, cQ] using congrArg (Int.cast : ℤ → ℚ) hquad
  obtain ⟨q, hq⟩ := (intersection_quadratic_eq_zero_iff T x).mp hxquad
  obtain ⟨k, hk⟩ := exists_not_range_fin m T.componentCount e hm
  have hxk : x k = 0 := by simp [x, hk]
  have hqzero : q = 0 := by
    simpa [hxk, (ratMultiplicity_pos T k).ne'] using congrFun hq k
  have hxe (j : Fin m) : x (e j) = cQ j := by simp [x, cQ, Pi.single_apply]
  have hzero := congrFun hq (e ⟨0, hmpos⟩)
  simp only [hxe, hqzero, zero_smul, Pi.zero_apply, cQ, Int.cast_eq_zero] at hzero
  exact (hc ⟨0, hmpos⟩).ne' hzero

end AlgebraicGeometry.NumericalType
