module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DeligneConjectureConclusions
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RestrictScalarsRepresentation

/-!
# Continuity of restrictions of scalars of tensor products and contragredients

For a representation `ρ : G → GL_r(E)` with coefficients in a finite extension `E` of a
topological field `F`, continuity is expressed through the restriction of scalars
`Res_b ρ : G → GL_{r d}(F)` along a basis `b` of `E` over `F`. This file shows that the
restrictions of scalars of `ρ ⊗ ρ'` and of the contragredient `ρ^∨` are continuous when those of
`ρ` and `ρ'` are.

## Main results

* `Stacks.EtaleCohomology.restrictScalarsMatrix_kroneckerMonoidHom_apply`: the entries of
  `Res_b (A ⊗ B)` are sums of products of entries of `Res_b A` and `Res_b B`.
* `Stacks.EtaleCohomology.restrictScalarsMatrix_transpose_apply`: the entries of `Res_b (Aᵀ)` are
  entries of `Res_b A`.
* `Stacks.EtaleCohomology.continuous_restrictScalarsRep_kroneckerRepresentation`: `Res_b (ρ ⊗ ρ')`
  is continuous when `Res_b ρ` and `Res_b ρ'` are.
* `Stacks.EtaleCohomology.continuous_restrictScalarsRep_contragredient`: `Res_b ρ^∨` is
  continuous when `Res_b ρ` is.
-/

@[expose] public noncomputable section

open Matrix
open scoped Kronecker

namespace Stacks.EtaleCohomology

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

/-- The entries of `Res_b (A ⊗ B)` are sums of products of entries of `Res_b A` and `Res_b B`. -/
theorem restrictScalarsMatrix_kroneckerMonoidHom_apply {r s : ℕ} (M : Matrix (Fin r) (Fin r) E)
    (N : Matrix (Fin s) (Fin s) E) (p q : Fin (r * s * d)) :
    restrictScalarsMatrix b (kroneckerMonoidHom (M, N)) p q =
      ∑ t : Fin d,
        restrictScalarsMatrix b M
            (finProdFinEquiv ((finProdFinEquiv.symm (finProdFinEquiv.symm p).1).1,
              (finProdFinEquiv.symm p).2))
            (finProdFinEquiv ((finProdFinEquiv.symm (finProdFinEquiv.symm q).1).1, t)) *
          restrictScalarsMatrix b N
            (finProdFinEquiv ((finProdFinEquiv.symm (finProdFinEquiv.symm p).1).2, t))
            (finProdFinEquiv ((finProdFinEquiv.symm (finProdFinEquiv.symm q).1).2,
              (finProdFinEquiv.symm q).2)) := by
  simp only [restrictScalarsMatrix_apply]
  rw [restrictScalarsMatrix, Matrix.of_apply, kroneckerMonoidHom_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply, map_mul, Matrix.mul_apply]

/-- The entries of `Res_b (Mᵀ)` are entries of `Res_b M`. -/
theorem restrictScalarsMatrix_transpose_apply {r : ℕ} (M : Matrix (Fin r) (Fin r) E)
    (p q : Fin (r * d)) :
    restrictScalarsMatrix b Mᵀ p q =
      restrictScalarsMatrix b M (finProdFinEquiv ((finProdFinEquiv.symm q).1,
        (finProdFinEquiv.symm p).2)) (finProdFinEquiv ((finProdFinEquiv.symm p).1,
          (finProdFinEquiv.symm q).2)) := by
  rw [restrictScalarsMatrix_apply]
  rfl

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace F]
  [IsTopologicalRing F]

/-- **`Res_b (ρ ⊗ ρ')` is continuous** when `Res_b ρ` and `Res_b ρ'` are. -/
public theorem continuous_restrictScalarsRep_kroneckerRepresentation {r s : ℕ}
    {ρ : G →* GL (Fin r) E} {ρ' : G →* GL (Fin s) E} (hρ : Continuous (restrictScalarsRep b ρ))
    (hρ' : Continuous (restrictScalarsRep b ρ')) :
    Continuous (restrictScalarsRep b (kroneckerRepresentation ρ ρ')) := by
  refine continuous_restrictScalarsRep b _ (continuous_matrix fun p q => ?_)
  have hA := Units.continuous_val.comp hρ
  have hB := Units.continuous_val.comp hρ'
  simp only [kroneckerRepresentation_val]
  change Continuous fun g => restrictScalarsMatrix b
    (kroneckerMonoidHom ((ρ g : GL (Fin r) E).val, (ρ' g : GL (Fin s) E).val)) p q
  simp only [restrictScalarsMatrix_kroneckerMonoidHom_apply]
  refine continuous_finsetSum _ fun t _ => ?_
  exact ((hA.matrix_elem _ _).mul (hB.matrix_elem _ _))

omit [IsTopologicalRing F] in
/-- **`Res_b ρ^∨` is continuous** when `Res_b ρ` is. -/
public theorem continuous_restrictScalarsRep_contragredient {r : ℕ} {ρ : G →* GL (Fin r) E}
    (hρ : Continuous (restrictScalarsRep b ρ)) :
    Continuous (restrictScalarsRep b (contragredient ρ)) := by
  refine continuous_restrictScalarsRep b _ (continuous_matrix fun p q => ?_)
  have hA := (Units.continuous_val.comp hρ).comp continuous_inv
  simp only [contragredient_val, restrictScalarsMatrix_transpose_apply]
  have : ∀ g : G, (((ρ g)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) =
      ((ρ g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) := fun g => by rw [map_inv]
  simp only [this]
  exact hA.matrix_elem _ _

end Stacks.EtaleCohomology

end
