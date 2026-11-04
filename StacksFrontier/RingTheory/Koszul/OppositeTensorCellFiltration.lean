module

public import StacksFrontier.RingTheory.Koszul.DerivedComparison
public import StacksFrontier.RingTheory.Koszul.TensorCellFiltration

/-!
# The tensor product of a differential graded algebra with a Koszul algebra, read on the graded
opposite algebra

Let `R` be a commutative ring, let `A` be a differential graded `R`-algebra and let `K` be the
Koszul algebra of a functional `φ : Rʳ → R`. The tensor product `A ⊗_R K` of Tag 065W is a
differential graded `A`-algebra through `a ↦ a ⊗ 1`, and `Koszul.tensorModule` records it as a
*right* differential graded `A`-module. The chapter's convention for a *left* differential graded
module is a right module over the graded opposite algebra, so the same tensor product also
presents an object
`(A ⊗_R K)^opp` of the category of right differential graded `A^opp`-modules, and the two are
genuinely different presentations: the graded opposite twists the multiplication by a Koszul
sign, so the action of `A^opp` on `(A ⊗_R K)^opp` is left multiplication by `a ⊗ 1` in `A ⊗_R K`
rather than right multiplication.

This file proves that the second presentation is also orthogonal on the left to the acyclic
modules. The cells are again the wedge monomials `1 ⊗ ξ_s`, with the same coordinates
`Koszul.tensorCellCoords` and the same `DifferentialGradedAlgebra.koszulSignPow` twist, read
through the identification `DifferentialGradedAlgebra.Opposite.equiv` of the underlying graded
modules; only the compatibility with the action has to be redone, and the two Koszul signs it
acquires cancel.

Taking `A` to be the Koszul algebra `K_N` of `f₁ᴺ, …, f_rᴺ` and `K` to be the Koszul algebra
`K_t` of `f₁ᵗ, …, f_rᵗ` gives `K_N ⊗_R K_t` as a left differential graded `K_N`-module, which is
`Koszul.powBaseTensorRestrictedModule`, the module the comparison of Tag 0GZ7 is built on.

## Main definitions

* `Koszul.oppTensorModule`: the tensor product `A ⊗_R K`, as a *left* differential graded
  `A`-module, that is, a right module over the graded opposite of `A`.
* `Koszul.oppTensorCellCoords`: its cell coordinates, the coordinates of
  `Koszul.tensorCellCoords` read on the graded opposite algebras.
* `Koszul.gradedCellDataOppTensorModule`: the triangular cell decomposition of `A ⊗_R K` over
  the graded opposite of `A`, by exterior degree.

## Main results

* `DifferentialGradedAlgebra.koszulSignPow_mul_left_of_mem`: moving the Koszul twist past a left
  multiplication by a homogeneous element costs the sign of that element's degree.
* `Koszul.tensorCellCoords_tensorOneMul_of_mem`: the cell coordinates of `A ⊗_R K` are
  compatible with *left* multiplication by `a ⊗ 1`, up to the sign of the exterior degree against
  the degree of `a`.
* `Koszul.oppTensorCellCoords_smul`: the cell coordinates are compatible with the right action of
  the graded opposite algebra. This is the statement in which the two Koszul signs cancel.
* `Koszul.leftOrthogonal_acyclic_oppTensorModule`: `A ⊗_R K`, as a right module over the graded
  opposite of `A`, is orthogonal on the left to the acyclic modules.
* `Koszul.leftOrthogonal_acyclic_powBaseTensorRestrictedModule`: the same for `K_N ⊗_R K_t` as a
  left differential graded `K_N`-module.

## Implementation notes

The graded opposite algebra is opaque: `DifferentialGradedAlgebra.opposite` is built by choice
from a nonemptiness statement, so its carrier is reachable only through the linear equivalence
`DifferentialGradedAlgebra.Opposite.equiv` and the four formulas recorded alongside it. Every
statement below is therefore proved by pushing it across that equivalence to the corresponding
statement about `A` and `A ⊗_R K` themselves, which is why the grading, the vanishing above
exterior degree `r` and both triangularity properties reduce verbatim to the facts already
proved for `Koszul.tensorModule`.

*Where the signs cancel.* For `a` of degree `α` and `x` of degree `n`, the right action of the
graded opposite algebra is `x ·ᵒᵖᵖ (a ⊗ 1) = (-1)^(n·α) (a ⊗ 1) · x`, and left multiplication by
`a ⊗ 1` moves past the twist at the cost of `(-1)^(m·α)` on the coordinate of exterior degree
`m`. That coordinate has degree `n + m`, so the right action of the graded opposite algebra on it
carries exactly `(-1)^((n+m)·α)`, and the two sides agree.

## References

* [Stacks Project, Tag 065W](https://stacks.math.columbia.edu/tag/065W), the tensor product of
  differential graded algebras.
* [Stacks Project, Tag 09JG](https://stacks.math.columbia.edu/tag/09JG), the graded opposite
  algebra.
* [Stacks Project, Tag 09KM](https://stacks.math.columbia.edu/tag/09KM), orthogonality to the
  acyclic modules.
* [Stacks Project, Tag 0GZ7](https://stacks.math.columbia.edu/tag/0GZ7), where `K_N ⊗_R K_t` as a
  left differential graded `K_N`-module is used.
-/

@[expose] public noncomputable section

open scoped DirectSum ExteriorAlgebra TensorProduct

universe u

open CategoryTheory DifferentialGradedModule DifferentialGraded.Bimodule

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra.{u, u} R)

/-- **Moving the Koszul twist past a left multiplication by a homogeneous element** costs the
sign of that element's degree. This is the mirror of
`DifferentialGradedAlgebra.koszulSignPow_mul_of_mem`. -/
theorem koszulSignPow_mul_left_of_mem (m : ℕ) {α : ℤ} {a : A.A} (ha : a ∈ A.grading α)
    (z : A.A) :
    A.koszulSignPow m (a * z)
      = (((m : ℤ) * α).negOnePow : ℤ) • (a * A.koszulSignPow m z) := by
  induction z using DirectSum.Decomposition.inductionOn A.grading with
  | zero => simp
  | add x y hx hy => rw [mul_add, map_add, hx, hy, map_add, mul_add, smul_add]
  | @homogeneous p x =>
      have haz : a * (x : A.A) ∈ A.grading (p + α) := by
        rw [add_comm]
        exact SetLike.mul_mem_graded ha x.property
      rw [A.koszulSignPow_apply_of_mem m haz, A.koszulSignPow_apply_coe m p x,
        Algebra.mul_smul_comm, smul_smul, negOnePow_natMul_add]

/-- The identification of the underlying graded module of the graded opposite algebra with that
of `A` commutes with multiplication by an integer. -/
theorem opposite_equiv_zsmul (t : ℤ) (y : (opposite R A).toDifferentialGradedAlgebra.A) :
    (opposite R A).equiv (t • y) = t • (opposite R A).equiv y := by
  simp only [← Int.cast_smul_eq_zsmul R, map_smul]

end DifferentialGradedAlgebra

namespace Koszul

open DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {r : ℕ}
variable (A : DifferentialGradedAlgebra.{u, u} R) (φ : Module.Dual R (Fin r → R))

local notation "𝒦" => Koszul.cohomologicalDifferentialGradedAlgebra R (Fin r → R) φ

/-! ### Left multiplication by `a ⊗ 1` in cell coordinates -/

/-- **Left multiplication by `a ⊗ 1`** on a pure tensor multiplies the first factor on the left;
there is no Koszul sign, because the second factor of `a ⊗ 1` has degree zero. -/
theorem tensorOne_mul_tmul (a b : A.A) (c : (𝒦).A) :
    ((a ᵍ⊗ₜ[R] (1 : (𝒦).A) : A.grading ᵍ⊗[R] (𝒦).grading) * (b ᵍ⊗ₜ[R] c))
      = ((a * b) ᵍ⊗ₜ[R] c) := by
  induction b using DirectSum.Decomposition.inductionOn A.grading with
  | zero => rw [mul_zero, tmul_zero_left' A (𝒦), mul_zero]
  | add x y hx hy =>
      rw [mul_add, tmul_add_left A (𝒦), tmul_add_left A (𝒦), mul_add, hx, hy]
  | @homogeneous p x =>
      exact GradedTensorProduct.tmul_one_mul_coe_tmul A.grading (𝒦).grading a x c

/-- **The cell coordinates are compatible with left multiplication by `a ⊗ 1`** for a
homogeneous `a`, up to the sign of the exterior degree against the degree of `a`. This is the
mirror of `Koszul.tensorCellCoords_mulTensorOne_of_mem`, and the sign it carries is the one
`DifferentialGradedAlgebra.koszulSignPow_mul_left_of_mem` produces. -/
theorem tensorCellCoords_tensorOneMul_of_mem (α : ℤ) {a : A.A} (ha : a ∈ A.grading α)
    (x : A.grading ᵍ⊗[R] (𝒦).grading) (m : ℕ) (j : exteriorCellIndex.{u} r m) :
    ((tensorCellCoords A φ
        ((a ᵍ⊗ₜ[R] (1 : (𝒦).A) : A.grading ᵍ⊗[R] (𝒦).grading) * x)) m) j
      = (((m : ℤ) * α).negOnePow : ℤ) • (a * ((tensorCellCoords A φ x) m) j) := by
  obtain ⟨X, rfl⟩ := (GradedTensorProduct.of R A.grading (𝒦).grading).surjective x
  induction X using TensorProduct.induction_on with
  | zero =>
      rw [map_zero (GradedTensorProduct.of R A.grading (𝒦).grading), mul_zero,
        map_zero (tensorCellCoords A φ)]
      simp only [DirectSum.zero_apply, mul_zero, smul_zero]
  | add X Y hX hY =>
      rw [map_add (GradedTensorProduct.of R A.grading (𝒦).grading), mul_add,
        map_add (tensorCellCoords A φ), DirectSum.add_apply, DirectSum.add_apply, hX, hY,
        map_add (tensorCellCoords A φ), DirectSum.add_apply, DirectSum.add_apply,
        mul_add, smul_add]
  | tmul b c =>
      have hof : (GradedTensorProduct.of R A.grading (𝒦).grading) (b ⊗ₜ[R] c)
          = (b ᵍ⊗ₜ[R] c) := rfl
      rw [hof, tensorOne_mul_tmul A φ a b c, tensorCellCoords_tmul, tensorCellCoords_tmul,
        ← Algebra.mul_smul_comm, A.koszulSignPow_mul_left_of_mem m ha]

/-! ### The module `A ⊗_R K` over the graded opposite of `A` -/

/-- **The tensor product of a differential graded algebra `A` with the Koszul algebra of a
functional on `Rʳ`, as a *left* differential graded `A`-module**, that is, as a right module over
the graded opposite of `A`. The action is restriction of the regular module of the graded
opposite of `A ⊗_R K` along the graded opposite of `a ↦ a ⊗ 1`. -/
def oppTensorModule : DifferentialGradedModule.{u, u, u} (oppAlgebra A) :=
  restrictScalars (oppHom (tensorInclLeft A (𝒦)))
    (regularModule (oppAlgebra (tensorProduct A (𝒦))))

/-- The underlying module of `oppTensorModule A φ` is the graded opposite of `A ⊗_R K`. -/
theorem oppTensorModule_M :
    (oppTensorModule A φ).M = (oppAlgebra (tensorProduct A (𝒦))).A := rfl

/-- The grading of `oppTensorModule A φ` is that of the graded opposite of `A ⊗_R K`. -/
theorem oppTensorModule_grading :
    (oppTensorModule A φ).grading = (oppAlgebra (tensorProduct A (𝒦))).grading := rfl

/-- The differential of `oppTensorModule A φ` is that of the graded opposite of `A ⊗_R K`. -/
theorem oppTensorModule_d :
    (oppTensorModule A φ).d = (oppAlgebra (tensorProduct A (𝒦))).d := rfl

/-- Under the identification of the underlying graded modules, the image of a scalar under the
graded opposite of `a ↦ a ⊗ 1` is the pure tensor `a ⊗ 1`. -/
theorem equiv_oppHom_tensorInclLeft (a : (oppAlgebra A).A) :
    (opposite R (tensorProduct A (𝒦))).equiv
        ((oppHom (tensorInclLeft A (𝒦))).toAlgebraHom a) =
      ((((opposite R A).equiv a) ᵍ⊗ₜ[R] (1 : (𝒦).A)) : A.grading ᵍ⊗[R] (𝒦).grading) := by
  rw [oppHom_apply, LinearEquiv.apply_symm_apply, tensorInclLeft_toAlgebraHom]
  rfl

/-- The cell coordinates of `A ⊗_R K`, read on the graded opposite algebras. -/
def oppCellEquiv :
    (⨁ (m : ℕ), ⨁ (_ : exteriorCellIndex.{u} r m), A.A) ≃ₗ[R]
      (⨁ (m : ℕ), ⨁ (_ : exteriorCellIndex.{u} r m), (oppAlgebra A).A) :=
  DirectSum.congrLinearEquiv fun _ =>
    DirectSum.congrLinearEquiv fun _ => (opposite R A).equiv.symm

/-- **The cell coordinates of `A ⊗_R K` over the graded opposite of `A`.** They are the
coordinates `Koszul.tensorCellCoords` of the same tensor product, transported along the
identifications of the underlying graded modules with those of the graded opposite algebras. -/
def oppTensorCellCoords :
    (oppTensorModule A φ).M ≃ₗ[R]
      (⨁ (m : ℕ), ⨁ (_ : exteriorCellIndex.{u} r m), (oppAlgebra A).A) :=
  ((opposite R (tensorProduct A (𝒦))).equiv.trans (tensorCellCoords A φ)).trans (oppCellEquiv A)

/-- Each coordinate of `Koszul.oppTensorCellCoords` is the corresponding coordinate of
`Koszul.tensorCellCoords`, read through the identification of the underlying graded modules. -/
theorem oppTensorCellCoords_apply (x : (oppTensorModule A φ).M) (m : ℕ)
    (j : exteriorCellIndex.{u} r m) :
    (opposite R A).equiv (((oppTensorCellCoords A φ x) m) j)
      = ((tensorCellCoords A φ
          ((opposite R (tensorProduct A (𝒦))).equiv x)) m) j := by
  have h : ((oppTensorCellCoords A φ x) m) j
      = (opposite R A).equiv.symm
          (((tensorCellCoords A φ
            ((opposite R (tensorProduct A (𝒦))).equiv x)) m) j) := rfl
  rw [h, LinearEquiv.apply_symm_apply]

/-- A block of the cell coordinates over the graded opposite of `A` vanishes exactly when the
corresponding block of `Koszul.tensorCellCoords` does. -/
theorem oppTensorCellCoords_eq_zero_iff (x : (oppTensorModule A φ).M) (m : ℕ) :
    (oppTensorCellCoords A φ x) m = 0 ↔
      (tensorCellCoords A φ ((opposite R (tensorProduct A (𝒦))).equiv x)) m = 0 := by
  rw [DirectSum.ext_iff, DirectSum.ext_iff]
  refine forall_congr' fun j => ?_
  rw [DirectSum.zero_apply, DirectSum.zero_apply, ← oppTensorCellCoords_apply A φ x m j,
    LinearEquiv.map_eq_zero_iff]

/-- The identification with `A ⊗_R K` commutes with the differential. -/
private theorem equiv_d_oppTensorModule (x : (oppTensorModule A φ).M) :
    (opposite R (tensorProduct A (𝒦))).equiv ((oppTensorModule A φ).d x)
      = (tensorProduct A (𝒦)).d ((opposite R (tensorProduct A (𝒦))).equiv x) :=
  (opposite R (tensorProduct A (𝒦))).map_d x

/-- An element of `oppTensorModule A φ` has degree `n` exactly when its image in `A ⊗_R K` does. -/
private theorem mem_grading_oppTensorModule_iff (n : ℤ) (x : (oppTensorModule A φ).M) :
    x ∈ (oppTensorModule A φ).grading n ↔
      (opposite R (tensorProduct A (𝒦))).equiv x ∈ tensorProductGrading A (𝒦) n :=
  (opposite R (tensorProduct A (𝒦))).mem_grading_iff n x

/-! ### Compatibility of the cell coordinates with the action of the graded opposite algebra -/

/-- **The cell coordinates are compatible with the right action of the graded opposite algebra**,
for a homogeneous scalar acting on a homogeneous element. The action of the graded opposite
algebra contributes the Koszul sign of the degree of the element against the degree of the
scalar, left multiplication by `a ⊗ 1` contributes the sign of the exterior degree against the
degree of the scalar, and on the coordinate of exterior degree `m` the two together are the
Koszul sign the graded opposite algebra acts by on a coordinate of degree `n + m`. -/
theorem oppTensorCellCoords_smul_of_mem {α n : ℤ} {a : (oppAlgebra A).A}
    (ha : a ∈ (oppAlgebra A).grading α) {x : (oppTensorModule A φ).M}
    (hx : x ∈ (oppTensorModule A φ).grading n) (m : ℕ) :
    (oppTensorCellCoords A φ (MulOpposite.op a • x)) m
      = MulOpposite.op a • (oppTensorCellCoords A φ x) m := by
  have ha' : (opposite R A).equiv a ∈ A.grading α := ((opposite R A).mem_grading_iff α a).1 ha
  obtain ⟨y, hy⟩ : ∃ y : A.grading ᵍ⊗[R] (𝒦).grading,
      (opposite R (tensorProduct A (𝒦))).equiv x = y := ⟨_, rfl⟩
  have hyg : y ∈ tensorProductGrading A (𝒦) n := by
    rw [← hy]
    exact (mem_grading_oppTensorModule_iff A φ n x).1 hx
  have hact : (opposite R (tensorProduct A (𝒦))).equiv (MulOpposite.op a • x)
      = (((n * α).negOnePow : ℤ) •
        (((((opposite R A).equiv a) ᵍ⊗ₜ[R] (1 : (𝒦).A)) : A.grading ᵍ⊗[R] (𝒦).grading)
          * y)) := by
    rw [← equiv_oppHom_tensorInclLeft A φ a, ← hy]
    exact (opposite R (tensorProduct A (𝒦))).map_mul_of_mem n α _ _ hx
      ((oppHom (tensorInclLeft A (𝒦))).map_grading α a ha)
  refine DirectSum.ext fun j => ?_
  refine (opposite R A).equiv.injective ?_
  have hz : ((oppTensorCellCoords A φ x) m) j ∈ (oppAlgebra A).grading (n + (m : ℤ)) := by
    refine ((opposite R A).mem_grading_iff (n + (m : ℤ)) _).2 ?_
    rw [oppTensorCellCoords_apply A φ x m j, hy]
    exact coords_mem_of_mem_tensorProductGrading A φ n y hyg m j
  have hRHS : (opposite R A).equiv ((MulOpposite.op a • (oppTensorCellCoords A φ x) m) j)
      = ((((n + (m : ℤ)) * α).negOnePow : ℤ) •
        ((opposite R A).equiv a *
          (opposite R A).equiv (((oppTensorCellCoords A φ x) m) j))) := by
    rw [DFinsupp.smul_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    exact (opposite R A).map_mul_of_mem (n + (m : ℤ)) α _ _ hz ha
  rw [hRHS, oppTensorCellCoords_apply A φ (MulOpposite.op a • x) m j,
    oppTensorCellCoords_apply A φ x m j, hact, hy, tensorCellCoords_zsmul,
    tensorCellCoords_tensorOneMul_of_mem A φ α ha' y m j, smul_smul]
  congr 1
  rw [← Units.val_mul, ← Int.negOnePow_add,
    show n * α + (m : ℤ) * α = (n + (m : ℤ)) * α by ring]

/-- **The cell coordinates are compatible with the right action of the graded opposite
algebra.** Both sides are additive in the scalar and in the element, so this follows from
`Koszul.oppTensorCellCoords_smul_of_mem` by decomposing both into homogeneous pieces. -/
theorem oppTensorCellCoords_smul (a : (oppAlgebra A).A) (x : (oppTensorModule A φ).M) (m : ℕ) :
    (oppTensorCellCoords A φ (MulOpposite.op a • x)) m
      = MulOpposite.op a • (oppTensorCellCoords A φ x) m := by
  induction a using DirectSum.Decomposition.inductionOn (oppAlgebra A).grading with
  | zero =>
      rw [MulOpposite.op_zero]
      simp only [zero_smul, map_zero, DirectSum.zero_apply]
  | add a b hA hB =>
      rw [MulOpposite.op_add, add_smul]
      simp only [map_add, DirectSum.add_apply]
      rw [hA, hB, add_smul]
  | @homogeneous α a =>
      induction x using DirectSum.Decomposition.inductionOn (oppTensorModule A φ).grading with
      | zero =>
          rw [smul_zero]
          simp only [map_zero, DirectSum.zero_apply, smul_zero]
      | add x y hX hY =>
          rw [smul_add]
          simp only [map_add, DirectSum.add_apply]
          rw [hX, hY, smul_add]
      | @homogeneous n x =>
          exact oppTensorCellCoords_smul_of_mem A φ a.property x.property m

/-! ### Compatibility of the cell coordinates with the grading and the differential -/

/-- **An element of `A ⊗_R K` is homogeneous of degree `n` exactly when all of its cell
coordinates over the graded opposite algebra are**: the coordinate on a cell of exterior degree
`m` must have degree `n + m`. -/
theorem oppTensorModule_mem_grading_iff (n : ℤ) (x : (oppTensorModule A φ).M) :
    x ∈ (oppTensorModule A φ).grading n ↔ ∀ (m : ℕ) (j : exteriorCellIndex.{u} r m),
      ((oppTensorCellCoords A φ x) m) j ∈ (oppAlgebra A).grading (n + (m : ℤ)) := by
  refine ⟨fun hx m j => ?_, fun h => ?_⟩
  · refine ((opposite R A).mem_grading_iff (n + (m : ℤ)) _).2 ?_
    rw [oppTensorCellCoords_apply A φ x m j]
    exact coords_mem_of_mem_tensorProductGrading A φ n _
      ((mem_grading_oppTensorModule_iff A φ n x).1 hx) m j
  · refine (mem_grading_oppTensorModule_iff A φ n x).2 ?_
    refine mem_tensorProductGrading_of_coords A φ n _ fun m j => ?_
    rw [← oppTensorCellCoords_apply A φ x m j]
    exact ((opposite R A).mem_grading_iff (n + (m : ℤ)) _).1 (h m j)

/-- There are no cells above exterior degree `r`. -/
theorem oppTensorModule_coords_eq_zero (x : (oppTensorModule A φ).M) (m : ℕ) (hm : r + 1 ≤ m) :
    (oppTensorCellCoords A φ x) m = 0 := by
  have : IsEmpty (exteriorCellIndex.{u} r m) := isEmpty_exteriorCellIndex r (by omega)
  exact DirectSum.ext fun j => isEmptyElim j

/-- **The differential preserves the vanishing of the cell coordinates in high exterior
degrees.** The differential of the graded opposite algebra is the differential of `A ⊗_R K`, so
this is `Koszul.tensorCellCoords_d_eq_zero`. -/
theorem oppTensorModule_coords_d_eq_zero (k : ℕ) (x : (oppTensorModule A φ).M)
    (hx : ∀ m : ℕ, k ≤ m → (oppTensorCellCoords A φ x) m = 0) (m : ℕ) (hm : k ≤ m) :
    (oppTensorCellCoords A φ ((oppTensorModule A φ).d x)) m = 0 := by
  obtain ⟨y, hy⟩ : ∃ y, (opposite R (tensorProduct A (𝒦))).equiv x = y := ⟨_, rfl⟩
  have hx' : ∀ p : ℕ, k ≤ p → (tensorCellCoords A φ y) p = 0 := by
    intro p hp
    rw [← hy]
    exact (oppTensorCellCoords_eq_zero_iff A φ x p).1 (hx p hp)
  rw [oppTensorCellCoords_eq_zero_iff, equiv_d_oppTensorModule, hy]
  obtain ⟨X, rfl⟩ := (GradedTensorProduct.of R A.grading (𝒦).grading).surjective y
  exact tensorCellCoords_d_eq_zero A φ X m (hx' m hm) (hx' (m + 1) (by omega))

/-- **On the top cell coordinate the differential is the differential of the graded opposite
algebra**, with the sign of the exterior degree. This is `Koszul.tensorCellCoords_d_apply` read
through the identification of the underlying graded modules. -/
theorem oppTensorModule_coords_d (k : ℕ) (x : (oppTensorModule A φ).M)
    (hx : ∀ m : ℕ, k + 1 ≤ m → (oppTensorCellCoords A φ x) m = 0)
    (j : exteriorCellIndex.{u} r k) :
    ((oppTensorCellCoords A φ ((oppTensorModule A φ).d x)) k) j
      = ((-1 : ℤ) ^ ((k : ℤ)).natAbs) •
        (oppAlgebra A).d (((oppTensorCellCoords A φ x) k) j) := by
  obtain ⟨y, hy⟩ : ∃ y, (opposite R (tensorProduct A (𝒦))).equiv x = y := ⟨_, rfl⟩
  have hx' : (tensorCellCoords A φ y) (k + 1) = 0 := by
    rw [← hy]
    exact (oppTensorCellCoords_eq_zero_iff A φ x (k + 1)).1 (hx (k + 1) (by omega))
  refine (opposite R A).equiv.injective ?_
  rw [oppTensorCellCoords_apply A φ ((oppTensorModule A φ).d x) k j,
    equiv_d_oppTensorModule, hy,
    opposite_equiv_zsmul, (opposite R A).map_d, oppTensorCellCoords_apply A φ x k j, hy,
    Int.natAbs_natCast]
  obtain ⟨X, rfl⟩ := (GradedTensorProduct.of R A.grading (𝒦).grading).surjective y
  exact tensorCellCoords_d_apply A φ X k j hx'

/-! ### The cell decomposition and orthogonality -/

/-- **The triangular cell decomposition of `A ⊗_R K` over the graded opposite of `A`, by
exterior degree.** The cells of exterior degree `m` are the wedge monomials `1 ⊗ ξ_s` with
`|s| = m`, each in degree `-m`; there are none above exterior degree `r`, and the tensor
differential lowers the exterior degree, so it is lower triangular for this decomposition. -/
def gradedCellDataOppTensorModule : GradedCellData (oppTensorModule A φ) :=
  gradedCellDataOfCellCoords (I := exteriorCellIndex.{u} r) (fun m _ => (m : ℤ)) (r + 1)
    (oppTensorCellCoords A φ) (oppTensorCellCoords_smul A φ)
    (oppTensorModule_mem_grading_iff A φ) (oppTensorModule_coords_eq_zero A φ)
    (oppTensorModule_coords_d_eq_zero A φ) (oppTensorModule_coords_d A φ)

/-- **The tensor product of a differential graded algebra `A` with the Koszul algebra of a
functional on `Rʳ`, viewed as a right differential graded module over the graded opposite of `A`,
is orthogonal on the left to the acyclic modules.** This is the companion of
`Koszul.leftOrthogonal_acyclic_tensorModule` for the chapter's presentation of a left
differential graded module as a right module over the graded opposite algebra. -/
theorem leftOrthogonal_acyclic_oppTensorModule :
    (acyclic' (oppAlgebra A)).leftOrthogonal
      ((toHomotopyCategory (oppAlgebra A)).obj (oppTensorModule A φ)) :=
  leftOrthogonal_acyclic_of_gradedCellData (gradedCellDataOppTensorModule A φ)

/-- **`K_n ⊗_R K_t`, viewed as a right differential graded module over the graded opposite of
`K_n`, is orthogonal on the left to the acyclic modules.** This is
`Koszul.leftOrthogonal_acyclic_oppTensorModule` for the functional cutting out `K_t` over the
algebra `K_n`, and it is the companion of `Koszul.leftOrthogonal_acyclic_powAlgebra_tensorModule`
for left modules. -/
theorem leftOrthogonal_acyclic_oppAlgebra_powAlgebra_tensorModule (f : Fin r → R) (n t : ℕ) :
    (acyclic' (oppAlgebra (powAlgebra f n))).leftOrthogonal
      ((toHomotopyCategory (oppAlgebra (powAlgebra f n))).obj
        (restrictScalars (oppHom (tensorInclLeft (powAlgebra f n) (powAlgebra f t)))
          (regularModule (oppAlgebra (tensorProduct (powAlgebra f n) (powAlgebra f t)))))) :=
  leftOrthogonal_acyclic_oppTensorModule (powAlgebra f n) (seqDual fun i => f i ^ t)

/-- **`{}_N(K_N ⊗_R K_t)`, the tensor product `K_N ⊗_R K_t` as a left differential graded
`K_N`-module, is orthogonal on the left to the acyclic modules.** This is
`Koszul.leftOrthogonal_acyclic_oppAlgebra_powAlgebra_tensorModule` read on the module
`Koszul.powBaseTensorRestrictedModule` of the comparison of Tag 0GZ7. -/
theorem leftOrthogonal_acyclic_powBaseTensorRestrictedModule (f : Fin r → R) (t N : ℕ) :
    (acyclic' (oppAlgebra (powAlgebra f N))).leftOrthogonal
      ((toHomotopyCategory (oppAlgebra (powAlgebra f N))).obj
        (powBaseTensorRestrictedModule f t N)) :=
  leftOrthogonal_acyclic_oppTensorModule (powAlgebra f N) (seqDual fun i => f i ^ t)

end Koszul

end
