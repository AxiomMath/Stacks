module

public import Mathlib.LinearAlgebra.Determinant
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.ExteriorPower
public import StacksFrontier.RingTheory.Koszul.IteratedContraction

/-!
# Iterated contraction is the duality pairing of exterior powers

Let `R` be a commutative ring, `E` an `R`-module, `φ₁, …, φₙ : E →ₗ[R] R` linear forms and
`v₁, …, vₙ` vectors of `E`. Contracting the wedge `v₁ ∧ ⋯ ∧ vₙ` successively by `φ₁, …, φₙ`
lowers the exterior degree to zero, and the scalar that results is the determinant

`det (φᵢ(vⱼ))`

of the matrix of pairings. This file proves that formula and identifies the resulting linear
form on `⋀ⁿ E` with Mathlib's duality pairing `exteriorPower.pairingDual`, whose defining
property is the same determinant: `exteriorPower.pairingDual` sends `φ₁ ∧ ⋯ ∧ φₙ` to the form
taking `v₁ ∧ ⋯ ∧ vₙ` to `det (φᵢ(vⱼ))`.

Together with the bijectivity of the pairing for `E` finite free
(`exteriorPower.bijective_pairingDual`), the identification says that iterated contraction
exhibits the dual `(⋀ⁿ E)^∨` as the exterior power `⋀ⁿ(E^∨)` of the dual: every linear form on
`⋀ⁿ E` is a combination of iterated contractions, and the only relations among those are the
alternating ones of `Koszul.listContraction_swap_adjacent` and
`Koszul.listContraction_eq_zero_of_adjacent_eq`.

## Main definitions

* `Koszul.listContractionDual`: **the linear form on `⋀ⁿ E` given by iterated contraction** by
  the entries of a list of linear forms on `E`.

## Main results

* `Koszul.listContraction_append`: iterated contraction by a concatenation of lists is
  contraction by the first list followed by contraction by the second.
* `Koszul.listContraction_ofFn_ιMulti`: **the determinant formula** `det (φᵢ(vⱼ))` for the
  iterated contraction of a wedge of vectors.
* `Koszul.pairingDual_ιMulti`: **iterated contraction is the duality pairing.** The linear form
  `exteriorPower.pairingDual R E n (φ₁ ∧ ⋯ ∧ φₙ)` is contraction by `φ₁, …, φₙ` in that order.
* `Koszul.eq_pairingDual`: a linear map `⋀ⁿ(E^∨) ⟶ (⋀ⁿ E)^∨` sending each wedge of linear forms
  to the corresponding iterated contraction is the duality pairing.
* `Koszul.bijective_of_listContractionDual`: **for `E` finite free such a map is bijective**.
* `Koszul.listContractionDual_ofFn_append`: **multiplicativity.** Pairing against a wedge of
  linear forms split into two blocks is contraction by the first block followed by contraction
  by the second.
* `Koszul.listContractionDual_dualBasis_apply_ιMulti`: against the wedge of a dual basis the
  pairing is the determinant of the coordinate matrix of the family.

## Implementation notes

**The scalar is returned through the augmentation.** Contracting `n` times out of `⋀ⁿ E` lands
in `⋀⁰ E`, the image of `R` under `algebraMap`, and the scalar is read off by the augmentation
`ExteriorAlgebra.algebraMapInv`, which inverts `algebraMap`. So `Koszul.listContractionDual` is
literally "contract, then take the degree-zero coefficient", and no choice of an identification
of `⋀⁰ E` with `R` enters any statement.

**The pairing matrix is transposed.** `exteriorPower.pairingDual_ιMulti_ιMulti` records the
pairing as the determinant of `(i, j) ↦ φⱼ(vᵢ)`, whereas the Laplace expansion that computes an
iterated contraction expands along the row `j ↦ φ₁(vⱼ)` of `(i, j) ↦ φᵢ(vⱼ)`. The two matrices
are transposes of one another, so `Matrix.det_transpose` mediates between them.

**The head of the list is contracted first.** This is the convention of
`Koszul.listContraction`, and it is what makes `Koszul.listContraction_append` read as
"contract by the first block, then by the second": the first block of a product of linear forms
acts first.

## References

* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
* [Stacks Project, Tag 0622](https://stacks.math.columbia.edu/tag/0622)
-/

@[expose] public section

open scoped ExteriorAlgebra

namespace Koszul

universe u v

variable {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]

/-- **Iterated contraction by a concatenation of lists** is contraction by the first list
followed by contraction by the second. -/
theorem listContraction_append (l₁ l₂ : List (Module.Dual R E)) :
    listContraction (l₁ ++ l₂) = (listContraction l₂).comp (listContraction l₁) := by
  induction l₁ with
  | nil => rw [List.nil_append, listContraction_nil, LinearMap.comp_id]
  | cons φ l₁ ih =>
    refine LinearMap.ext fun x ↦ ?_
    rw [List.cons_append, listContraction_cons_apply, ih, LinearMap.comp_apply,
      LinearMap.comp_apply, listContraction_cons_apply]

/-- **The determinant formula for iterated contraction.** Contracting the wedge `v₁ ∧ ⋯ ∧ vₙ`
successively by `φ₁, …, φₙ` gives the scalar `det (φᵢ(vⱼ))`, placed in `⋀⁰ E` by `algebraMap`. -/
theorem listContraction_ofFn_ιMulti (n : ℕ) (f : Fin n → Module.Dual R E) (v : Fin n → E) :
    listContraction (List.ofFn f) (ExteriorAlgebra.ιMulti R n v) =
      algebraMap R (ExteriorAlgebra R E) (Matrix.of fun i j ↦ f i (v j)).det := by
  induction n with
  | zero =>
    rw [List.ofFn_zero, listContraction_nil, LinearMap.id_apply,
      ExteriorAlgebra.ιMulti_zero_apply, Matrix.det_isEmpty, map_one]
  | succ n ih =>
    rw [List.ofFn_succ, listContraction_cons_apply,
      exteriorPower.contractLeft_ιMulti (f 0) n v, Matrix.det_succ_row_zero]
    simp only [map_sum, map_smul, Matrix.of_apply]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hsub : (Matrix.of fun i j ↦ f i (v j)).submatrix Fin.succ k.succAbove =
        Matrix.of fun i j ↦ f i.succ ((v ∘ k.succAbove) j) := rfl
    rw [hsub, ih (fun i ↦ f i.succ) (v ∘ k.succAbove), Algebra.smul_def, ← map_mul]

/-- **The linear form on `⋀ⁿ E` given by iterated contraction** by the entries of a list `l` of
linear forms on `E`: contract by the entries of `l`, head first, then take the degree-zero
coefficient of the result through the augmentation of the exterior algebra. -/
noncomputable def listContractionDual (n : ℕ) (l : List (Module.Dual R E)) :
    Module.Dual R (⋀[R]^n E) :=
  (ExteriorAlgebra.algebraMapInv (R := R) (M := E)).toLinearMap.comp
    ((listContraction l).comp (⋀[R]^n E).subtype)

/-- The value of `listContractionDual n l` at `x` is the degree-zero coefficient, under
`ExteriorAlgebra.algebraMapInv`, of the iterated contraction of `x` by the entries of `l`. -/
@[simp]
theorem listContractionDual_apply (n : ℕ) (l : List (Module.Dual R E)) (x : ⋀[R]^n E) :
    listContractionDual n l x =
      ExteriorAlgebra.algebraMapInv (listContraction l (x : ExteriorAlgebra R E)) := rfl

/-- The determinant formula, read as a pairing of `⋀ⁿ E` against a list of linear forms. -/
theorem listContractionDual_ofFn_ιMulti (n : ℕ) (f : Fin n → Module.Dual R E) (v : Fin n → E) :
    listContractionDual n (List.ofFn f) (exteriorPower.ιMulti R n v) =
      (Matrix.of fun i j ↦ f i (v j)).det := by
  rw [listContractionDual_apply, exteriorPower.ιMulti_apply_coe, listContraction_ofFn_ιMulti]
  exact ExteriorAlgebra.algebraMap_leftInverse E _

/-- **Iterated contraction is the duality pairing of exterior powers.** The linear form that
`exteriorPower.pairingDual` attaches to the wedge `φ₁ ∧ ⋯ ∧ φₙ` of linear forms is contraction
by `φ₁, …, φₙ` in that order. -/
theorem pairingDual_ιMulti (n : ℕ) (f : Fin n → Module.Dual R E) :
    exteriorPower.pairingDual R E n (exteriorPower.ιMulti R n f) =
      listContractionDual n (List.ofFn f) := by
  refine exteriorPower.linearMap_ext (AlternatingMap.ext fun v ↦ ?_)
  have htr : Matrix.transpose (Matrix.of fun i j ↦ f i (v j) : Matrix (Fin n) (Fin n) R) =
      Matrix.of fun i j ↦ f j (v i) := rfl
  rw [LinearMap.compAlternatingMap_apply, LinearMap.compAlternatingMap_apply,
    exteriorPower.pairingDual_ιMulti_ιMulti, listContractionDual_ofFn_ιMulti, ← htr,
    Matrix.det_transpose]

/-- A linear map from `⋀ⁿ(E^∨)` to `(⋀ⁿ E)^∨` that sends every wedge `φ₁ ∧ ⋯ ∧ φₙ` of linear
forms to iterated contraction by `φ₁, …, φₙ` is the duality pairing. -/
theorem eq_pairingDual (n : ℕ)
    (Φ : ⋀[R]^n (Module.Dual R E) →ₗ[R] Module.Dual R (⋀[R]^n E))
    (hΦ : ∀ f : Fin n → Module.Dual R E,
      Φ (exteriorPower.ιMulti R n f) = listContractionDual n (List.ofFn f)) :
    Φ = exteriorPower.pairingDual R E n := by
  refine exteriorPower.linearMap_ext (AlternatingMap.ext fun f ↦ ?_)
  rw [LinearMap.compAlternatingMap_apply, LinearMap.compAlternatingMap_apply, hΦ,
    pairingDual_ιMulti]

/-- **Iterated contraction exhibits the dual of an exterior power as the exterior power of the
dual.** For `E` finite free, any linear map `⋀ⁿ(E^∨) ⟶ (⋀ⁿ E)^∨` which sends each wedge of
linear forms to the corresponding iterated contraction is bijective. -/
theorem bijective_of_listContractionDual [Module.Free R E] [Module.Finite R E] (n : ℕ)
    (Φ : ⋀[R]^n (Module.Dual R E) →ₗ[R] Module.Dual R (⋀[R]^n E))
    (hΦ : ∀ f : Fin n → Module.Dual R E,
      Φ (exteriorPower.ιMulti R n f) = listContractionDual n (List.ofFn f)) :
    Function.Bijective Φ := by
  rw [eq_pairingDual n Φ hΦ]
  exact exteriorPower.bijective_pairingDual R E n

/-- **Multiplicativity of the pairing.** Pairing against a wedge of linear forms split into two
blocks is contraction by the first block followed by contraction by the second. -/
theorem listContractionDual_ofFn_append (n m : ℕ) (f : Fin n → Module.Dual R E)
    (g : Fin m → Module.Dual R E) :
    listContractionDual (n + m) (List.ofFn f ++ List.ofFn g) =
      exteriorPower.pairingDual R E (n + m)
        (exteriorPower.ιMulti R (n + m) (Fin.append f g)) := by
  rw [pairingDual_ιMulti, List.ofFn_fin_append]

/-- Against the wedge of a dual basis the pairing is the determinant of the coordinate matrix
of the family. -/
theorem listContractionDual_dualBasis_apply_ιMulti {n : ℕ} (b : Module.Basis (Fin n) R E)
    (v : Fin n → E) :
    listContractionDual n (List.ofFn b.dualBasis) (exteriorPower.ιMulti R n v) = b.det v := by
  classical
  rw [listContractionDual_ofFn_ιMulti, Module.Basis.det_apply]
  congr 1 with i j
  rw [Matrix.of_apply, Module.Basis.toMatrix_apply, Module.Basis.coe_dualBasis,
    Module.Basis.coord_apply]

end Koszul

end
