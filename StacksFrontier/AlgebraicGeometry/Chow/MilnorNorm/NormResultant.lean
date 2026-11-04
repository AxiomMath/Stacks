module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

/-!
# The norm of `g mod φ` is the resultant `Res(φ, g)`

Let `K` be a field and `φ, g ∈ K[X]` monic. This file proves

`N_{(K[X] ⧸ φ) / K}(g mod φ) = Res(φ, g)`

(`Stacks.Chow.norm_mk_eq_resultant`), and hence, by the antisymmetry of the resultant,
`N(g mod φ) = (-1)^{deg φ · deg g} N(φ mod g)` (`Stacks.Chow.norm_mk_eq_neg_one_pow_mul_norm_mk`).

## The argument

In the power basis `1, θ, …, θ^{n-1}` of `K[X] ⧸ φ`, multiplication by `g(θ)` has matrix
`g(M)`, where `M` is the matrix of multiplication by `θ`, whose characteristic polynomial is
`φ`. Over an algebraic closure `E`, `g = ∏_η (X - η)`, so
`det g(M) = ∏_η det(M - η) = ∏_η (-1)^n φ(η) = ∏_η ∏_θ (θ - η)`, which is `Res(φ, g)` by
`Polynomial.resultant_eq_prod_roots_sub`.

## Main results

* `Stacks.Chow.norm_mk_eq_resultant`: `N(g mod φ) = Res(φ, g)`.
* `Stacks.Chow.norm_mk_eq_neg_one_pow_mul_norm_mk`: `N(g mod φ) = (-1)^{deg φ · deg g} N(φ mod g)`.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
-/

@[expose] public noncomputable section

open Polynomial

universe u

namespace Stacks.Chow

variable {K : Type u} [Field K]

/-- Applying a ring homomorphism entrywise commutes with evaluating a polynomial at a matrix. -/
theorem mapMatrix_aeval {n : Type*} [Fintype n] [DecidableEq n] {E : Type*} [Field E]
    (f : K →+* E) (M : Matrix n n K) (g : K[X]) :
    f.mapMatrix (aeval M g) = aeval (f.mapMatrix M) (g.map f) := by
  rw [aeval_def, aeval_def, Polynomial.hom_eval₂, eval₂_map]
  congr 1
  refine RingHom.ext fun c ↦ ?_
  simp only [RingHom.comp_apply, Matrix.algebraMap_eq_diagonal, RingHom.mapMatrix_apply,
    Matrix.diagonal_map (map_zero f)]
  rfl

/-- **`N_{(K[X] ⧸ φ) / K}(g mod φ) = Res(φ, g)`** for `φ` and `g` monic. -/
theorem norm_mk_eq_resultant {φ g : K[X]} (hφ : φ.Monic) (hg : g.Monic) :
    Algebra.norm K (AdjoinRoot.mk φ g) = resultant φ g := by
  classical
  let E := AlgebraicClosure K
  let f : K →+* E := algebraMap K E
  refine f.injective ?_
  let pb := AdjoinRoot.powerBasis hφ.ne_zero
  have hgen : pb.gen = AdjoinRoot.root φ := rfl
  set M := Algebra.leftMulMatrix pb.basis pb.gen with hM
  have hchar : M.charpoly = φ := by
    rw [hM, charpoly_leftMulMatrix, AdjoinRoot.minpoly_powerBasis_gen_of_monic hφ]
  rw [Algebra.norm_eq_matrix_det pb.basis, ← AdjoinRoot.aeval_eq, ← hgen,
    ← Polynomial.aeval_algHom_apply, ← hM, RingHom.map_det, mapMatrix_aeval]
  set M' := f.mapMatrix M
  have hsg := IsAlgClosed.splits (g.map f)
  have hsφ := IsAlgClosed.splits (φ.map f)
  have hcard : Fintype.card (Fin pb.dim) = (φ.map f).roots.card := by
    rw [Fintype.card_fin, AdjoinRoot.powerBasis_dim, ← hsφ.natDegree_eq_card_roots,
      natDegree_map]
  have hleft : (aeval M' (g.map f)).det =
      ((g.map f).roots.map fun η ↦ ((φ.map f).roots.map fun θ ↦ θ - η).prod).prod := by
    conv_lhs => rw [hsg.eq_prod_roots_of_monic (hg.map f)]
    have hhom : ∀ q : E[X], (aeval M' q).det =
        (Matrix.detMonoidHom.comp (aeval M').toMonoidHom) q := fun q ↦ rfl
    rw [hhom, map_multiset_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun η _ ↦ ?_)
    show (aeval M' (X - C η)).det = _
    rw [map_sub, aeval_X, aeval_C]
    have hneg : M' - algebraMap E (Matrix (Fin pb.dim) (Fin pb.dim) E) η =
        -(Matrix.scalar (Fin pb.dim) η - M') := by
      rw [neg_sub, Matrix.algebraMap_eq_diagonal]
      rfl
    rw [hneg, Matrix.det_neg, ← Matrix.eval_charpoly, show M' = M.map f from rfl,
      Matrix.charpoly_map, hchar, hsφ.eval_eq_prod_roots_of_monic (hφ.map f), hcard,
      ← Multiset.card_map (fun x ↦ η - x), ← Multiset.prod_map_neg, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun θ _ ↦ ?_)
    simp
  rw [hleft, ← resultant_map_map, show φ.natDegree = (φ.map f).natDegree from
    (natDegree_map f).symm, show g.natDegree = (g.map f).natDegree from (natDegree_map f).symm,
    resultant_eq_prod_roots_sub _ _ (hφ.map f) (hg.map f) hsφ hsg,
    Multiset.prod_map_product_eq_prod_prod, Multiset.prod_map_prod_map]

/-- **Reciprocity of norms: `N(g mod φ) = (-1)^{deg φ · deg g} N(φ mod g)`** for `φ, g` monic. -/
theorem norm_mk_eq_neg_one_pow_mul_norm_mk {φ g : K[X]} (hφ : φ.Monic) (hg : g.Monic) :
    Algebra.norm K (AdjoinRoot.mk φ g) =
      (-1) ^ (φ.natDegree * g.natDegree) * Algebra.norm K (AdjoinRoot.mk g φ) := by
  rw [norm_mk_eq_resultant hφ hg, norm_mk_eq_resultant hg hφ, resultant_comm]

end Stacks.Chow

end
