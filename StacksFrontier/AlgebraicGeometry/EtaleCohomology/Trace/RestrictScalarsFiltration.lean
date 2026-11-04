module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RestrictScalarsRepresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.BlockTriangularLattice
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GradedTriangularMatrices

/-!
# Sub and quotient representations along a coordinate splitting

For a representation `Y : G → GL_m(E)` and a coordinate splitting `J, K` of `E^m` such that the
coordinates of `J` are `Y`-stable (`Y J = J (J' Y J)`, `K Y = (K Y K') K`), the diagonal blocks
`J' Y J` and `K Y K'` are representations. If the off-diagonal block `K T J` vanishes, the
coordinates of `J` are `T`-stable. Restriction of scalars carries coordinate matrices to coordinate
matrices.

## Main definitions

* `Stacks.EtaleCohomology.IsSplitting.subRep`: the sub-representation `g ↦ J' Y(g) J` on stable
  coordinates.
* `Stacks.EtaleCohomology.IsSplitting.quotRep`: the quotient representation `g ↦ K Y(g) K'` along
  stable coordinates.
* `Stacks.EtaleCohomology.resIndex`: the coordinates `(e j, l)` of `F^{r d}`.

## Main results

* `Stacks.EtaleCohomology.IsSplitting.stable_of_comp_eq_zero`: if `K T J = 0`, the coordinates of
  `J` are `T`-stable.
* `Stacks.EtaleCohomology.restrictScalarsMatrix_coordMatrix`: restriction of scalars of a
  coordinate matrix is a coordinate matrix.
-/

@[expose] public noncomputable section

open Matrix

namespace Stacks.EtaleCohomology

section Rep

variable {R : Type*} [CommRing R] {r a c : ℕ} {J : Matrix (Fin r) (Fin a) R}
  {J' : Matrix (Fin a) (Fin r) R} {K : Matrix (Fin c) (Fin r) R} {K' : Matrix (Fin r) (Fin c) R}
  {G : Type*} [Group G]

/-- On `Y`-stable coordinates the diagonal block `g ↦ J' Y(g) J` is multiplicative. -/
public theorem IsSplitting.subRep_mul_aux (Y : G →* GL (Fin r) R)
    (hY : ∀ g, (Y g).val * J = J * (J' * (Y g).val * J)) (g g' : G) :
    J' * (Y (g * g')).val * J = (J' * (Y g).val * J) * (J' * (Y g').val * J) := by
  calc J' * (Y (g * g')).val * J = J' * (Y g).val * ((Y g').val * J) := by
        rw [map_mul, Units.val_mul]
        simp only [Matrix.mul_assoc]
    _ = J' * (Y g).val * (J * (J' * (Y g').val * J)) := by rw [hY g']
    _ = _ := by simp only [Matrix.mul_assoc]

/-- Along `Y`-stable coordinates the diagonal block `g ↦ K Y(g) K'` is multiplicative. -/
public theorem IsSplitting.quotRep_mul_aux (Y : G →* GL (Fin r) R)
    (hY : ∀ g, K * (Y g).val = (K * (Y g).val * K') * K) (g g' : G) :
    K * (Y (g * g')).val * K' = (K * (Y g).val * K') * (K * (Y g').val * K') := by
  calc K * (Y (g * g')).val * K' = (K * (Y g).val) * (Y g').val * K' := by
        rw [map_mul, Units.val_mul]
        simp only [Matrix.mul_assoc]
    _ = ((K * (Y g).val * K') * K) * (Y g').val * K' := by conv_lhs => rw [hY g]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- The sub-representation `g ↦ J' Y(g) J` on stable coordinates. -/
public def IsSplitting.subRep (h : IsSplitting J J' K K') (Y : G →* GL (Fin r) R)
    (hY : ∀ g, (Y g).val * J = J * (J' * (Y g).val * J)) : G →* GL (Fin a) R where
  toFun g := ⟨J' * (Y g).val * J, J' * (Y g⁻¹).val * J,
    by rw [← IsSplitting.subRep_mul_aux Y hY, mul_inv_cancel, map_one, Units.val_one,
      Matrix.mul_one, h.left_inv],
    by rw [← IsSplitting.subRep_mul_aux Y hY, inv_mul_cancel, map_one, Units.val_one,
      Matrix.mul_one, h.left_inv]⟩
  map_one' := Units.ext (by
    change J' * (Y 1).val * J = 1
    rw [map_one, Units.val_one, Matrix.mul_one, h.left_inv])
  map_mul' g g' := Units.ext (IsSplitting.subRep_mul_aux Y hY g g')

/-- The matrix of `h.subRep Y hY g` is `J' Y(g) J`. -/
@[simp]
public theorem IsSplitting.subRep_val (h : IsSplitting J J' K K') (Y : G →* GL (Fin r) R)
    (hY : ∀ g, (Y g).val * J = J * (J' * (Y g).val * J)) (g : G) :
    (h.subRep Y hY g).val = J' * (Y g).val * J :=
  rfl

/-- The quotient representation `g ↦ K Y(g) K'` along stable coordinates. -/
public def IsSplitting.quotRep (h : IsSplitting J J' K K') (Y : G →* GL (Fin r) R)
    (hY : ∀ g, K * (Y g).val = (K * (Y g).val * K') * K) : G →* GL (Fin c) R where
  toFun g := ⟨K * (Y g).val * K', K * (Y g⁻¹).val * K',
    by rw [← IsSplitting.quotRep_mul_aux Y hY, mul_inv_cancel, map_one, Units.val_one,
      Matrix.mul_one, h.right_inv],
    by rw [← IsSplitting.quotRep_mul_aux Y hY, inv_mul_cancel, map_one, Units.val_one,
      Matrix.mul_one, h.right_inv]⟩
  map_one' := Units.ext (by
    change K * (Y 1).val * K' = 1
    rw [map_one, Units.val_one, Matrix.mul_one, h.right_inv])
  map_mul' g g' := Units.ext (IsSplitting.quotRep_mul_aux Y hY g g')

/-- The matrix of `h.quotRep Y hY g` is `K Y(g) K'`. -/
@[simp]
public theorem IsSplitting.quotRep_val (h : IsSplitting J J' K K') (Y : G →* GL (Fin r) R)
    (hY : ∀ g, K * (Y g).val = (K * (Y g).val * K') * K) (g : G) :
    (h.quotRep Y hY g).val = K * (Y g).val * K' :=
  rfl

end Rep

section Stable

variable {R : Type*} [CommRing R] {r a c : ℕ} {J : Matrix (Fin r) (Fin a) R}
  {J' : Matrix (Fin a) (Fin r) R} {K : Matrix (Fin c) (Fin r) R} {K' : Matrix (Fin r) (Fin c) R}

/-- If the off-diagonal block `K T J` vanishes, the coordinates of `J` are `T`-stable. -/
public theorem IsSplitting.stable_of_comp_eq_zero (h : IsSplitting J J' K K')
    {T : Matrix (Fin r) (Fin r) R} (hT : K * T * J = 0) :
    T * J = J * (J' * T * J) ∧ K * T = (K * T * K') * K := by
  constructor
  · calc T * J = (J * J' + K' * K) * T * J := by rw [h.sum_eq_one, Matrix.one_mul]
      _ = J * (J' * T * J) + K' * (K * T * J) := by
          simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = _ := by rw [hT, Matrix.mul_zero, add_zero]
  · calc K * T = K * T * (J * J' + K' * K) := by rw [h.sum_eq_one, Matrix.mul_one]
      _ = (K * T * J) * J' + (K * T * K') * K := by
          simp only [Matrix.mul_add, Matrix.mul_assoc]
      _ = _ := by rw [hT, Matrix.zero_mul, zero_add]

/-- Multiplying by coordinate matrices takes a submatrix. -/
public theorem transpose_coordMatrix_mul_mul_coordMatrix {e₂ : Fin c → Fin r}
    {e₁ : Fin a → Fin r} (T : Matrix (Fin r) (Fin r) R) :
    (coordMatrix (R := R) e₂)ᵀ * T * coordMatrix (R := R) e₁ = T.submatrix e₂ e₁ := by
  ext j j'
  rw [Matrix.mul_apply, Finset.sum_eq_single (e₁ j')]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (e₂ j)]
    · simp [coordMatrix]
    · intro i _ hi
      simp [coordMatrix, hi]
    · simp
  · intro i _ hi
    simp [coordMatrix, hi]
  · simp

end Stable

section Res

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
  {r a : ℕ}

/-- The coordinates `(e j, l)` of `F^{r d}`. -/
public def resIndex (e : Fin a → Fin r) : Fin (a * d) → Fin (r * d) := fun p =>
  finProdFinEquiv (e (finProdFinEquiv.symm p).1, (finProdFinEquiv.symm p).2)

/-- `resIndex e` is injective when `e` is. -/
public theorem resIndex_injective {e : Fin a → Fin r} (he : Function.Injective e) :
    Function.Injective (resIndex (d := d) e) := fun p q hpq => by
  have h := finProdFinEquiv.injective hpq
  simp only [Prod.mk.injEq] at h
  exact finProdFinEquiv.symm.injective (Prod.ext (he h.1) h.2)

/-- `resIndex e` sends the coordinate `(j, l)` to `(e j, l)`. -/
public theorem resIndex_apply (e : Fin a → Fin r) (j : Fin a) (l : Fin d) :
    resIndex e (finProdFinEquiv (j, l)) = finProdFinEquiv (e j, l) := by
  simp [resIndex]

/-- Restriction of scalars of a coordinate matrix is a coordinate matrix. -/
public theorem restrictScalarsMatrix_coordMatrix (e : Fin a → Fin r) :
    restrictScalarsMatrix b (coordMatrix (R := E) e) = coordMatrix (resIndex e) := by
  ext p q
  obtain ⟨⟨i, l⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨j, l'⟩, rfl⟩ := finProdFinEquiv.surjective q
  rw [← coordMatrix_map (algebraMap F E), restrictScalarsMatrix_map_algebraMap]
  simp only [coordMatrix, Matrix.of_apply, resIndex_apply, finProdFinEquiv.injective.eq_iff,
    Prod.mk.injEq, Matrix.one_apply]
  by_cases h1 : i = e j <;> by_cases h2 : l = l' <;> simp [h1, h2]

/-- Restriction of scalars of a transposed coordinate matrix. -/
public theorem restrictScalarsMatrix_transpose_coordMatrix (e : Fin a → Fin r) :
    restrictScalarsMatrix b (coordMatrix (R := E) e)ᵀ = (coordMatrix (resIndex e))ᵀ := by
  ext p q
  obtain ⟨⟨j, l⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨i, l'⟩, rfl⟩ := finProdFinEquiv.surjective q
  rw [← coordMatrix_map (algebraMap F E), ← Matrix.transpose_map,
    restrictScalarsMatrix_map_algebraMap]
  simp only [coordMatrix, Matrix.transpose_apply, Matrix.of_apply, resIndex_apply,
    finProdFinEquiv.injective.eq_iff, Prod.mk.injEq, Matrix.one_apply]
  by_cases h1 : i = e j <;> by_cases h2 : l = l' <;> simp [h1, h2, eq_comm]

end Res

end Stacks.EtaleCohomology

end
