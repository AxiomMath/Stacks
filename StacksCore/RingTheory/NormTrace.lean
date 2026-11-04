module

public import Mathlib.Algebra.Polynomial.Module.TensorProduct
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Mathlib.RingTheory.Trace.Defs
public import StacksCore.LinearAlgebra.Dimension.Natfreerank
import StacksCore.LinearAlgebra.Matrix.CommSemiring
import StacksCore.RingTheory.Ideal.Quotient.Operations
import StacksCore.RingTheory.Polynomial.FreeQuotient

/-! # Norm and trace -/

@[expose] public section

open LinearMap (mul)
open Polynomial TensorProduct Algebra Module Matrix Finset
open Algebra.TensorProduct hiding mul

section Lemmas

/-- The next-to-leading coefficient of the constant polynomial `1` is `0`. -/
@[simp] theorem Polynomial.nextCoeff_one (R : Type*) [Semiring R] : nextCoeff (1 : R[X]) = 0 :=
  nextCoeff_C_eq_zero 1

/-- The `n`-th coefficient of an integer scalar multiple `i • p` is `i` times the `n`-th
coefficient of `p`. -/
@[simp] theorem Polynomial.coeff_zsmul {R : Type*} [Ring R] (i : ℤ) (p : R[X]) (n : ℕ) :
    (i • p).coeff n = i • p.coeff n := rfl

/-- The characteristic polynomial of the zero endomorphism of a finite free `R`-module `M` is
`X ^ finrank R M`. -/
@[simp] theorem LinearMap.charpoly_zero' (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [Free R M] [Module.Finite R M] : (0 : End R M).charpoly = X ^ Module.finrank R M := by
  nontriviality R; simp

/-- The characteristic polynomial of the scalar endomorphism `r • 1` on a finite free `R`-module
is `(X - r) ^ finrank R M`. -/
@[simp] theorem LinearMap.charpoly_smul_one {R : Type*} (M : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] [Free R M] [Module.Finite R M] (r : R) :
    (r • 1 : End R M).charpoly = (X - C r) ^ finrank R M := by
  simpa [← sub_eq_add_neg] using charpoly_sub_smul (M := M) 0 (-r)

/-- The characteristic polynomial of the scalar endomorphism `r • id` on a finite free
`R`-module is `(X - r) ^ finrank R M`. -/
@[simp] theorem LinearMap.charpoly_smul_id {R : Type*} (M : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] [Free R M] [Module.Finite R M] (r : R) :
    (r • LinearMap.id : M →ₗ[R] M).charpoly = (X - C r) ^ finrank R M := charpoly_smul_one M r

end Lemmas

/-- Bundled-morphism version of `Matrix.det_det`: applying the ring-hom-class element `f` to the
determinant of `M : Matrix m m S` and then taking the determinant in `Matrix n n R` agrees with
the determinant of the block matrix obtained by entrywise application of `f`. -/
theorem Matrix.det_det' {R S n m : Type*} [CommRing R] [CommRing S] (M : Matrix m m S)
    [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
    {F : Type*} [FunLike F S (Matrix n n R)] [RingHomClass F S (Matrix n n R)] (f : F) :
    (f M.det).det = ((M.map f).comp m m n n R).det := M.det_det (RingHomClass.toRingHom f)

/-- The lifted ring hom `f.polyToMatrix : A[X] → Matrix n n R[X]` sends a constant polynomial
`C r` to the constant matrix-polynomial whose entries are `f r` mapped through `C`. -/
@[simp] theorem RingHom.polyToMatrix_C {R A : Type*} [CommSemiring R] [Semiring A]
    {n : Type*} [DecidableEq n] [Fintype n] (f : A →+* Matrix n n R) (r : A) :
    f.polyToMatrix (C r) = (f r).map C := by
  simp [RingHom.polyToMatrix]

/-- The lifted ring hom `f.polyToMatrix` sends the indeterminate `X` to the scalar matrix-
polynomial `X • 1`. -/
@[simp] theorem RingHom.polyToMatrix_X {R A : Type*} [CommSemiring R] [Semiring A]
    {n : Type*} [DecidableEq n] [Fintype n] (f : A →+* Matrix n n R) :
    f.polyToMatrix X = (X : R[X]) • 1 := by
  simp [RingHom.polyToMatrix, Matrix.smul_one_eq_diagonal]

/-- Lift an `R`-algebra hom `f : A →ₐ[R] Matrix n n R` to an `R`-algebra hom
`A[X] →ₐ[R] Matrix n n R[X]` by applying `f` to each coefficient. -/
noncomputable def AlgHom.polyToMatrix {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    {n : Type*} [DecidableEq n] [Fintype n] (f : A →ₐ[R] Matrix n n R) :
    A[X] →ₐ[R] Matrix n n R[X] where
  __ := f.toRingHom.polyToMatrix
  commutes' r := by simp

/-- The underlying function of `f.polyToMatrix` (as an `AlgHom`) coincides with the underlying
function of the lift of `f` as a ring hom. -/
@[simp] theorem AlgHom.coe_polyToMatrix {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    {n : Type*} [DecidableEq n] [Fintype n] (f : A →ₐ[R] Matrix n n R) :
    ⇑(f.polyToMatrix) = (f : _ →+* _).polyToMatrix := rfl

namespace Polynomial

/-- The `(i,j)`-entry of `f.polyToMatrix p` has `k`-th coefficient equal to the `(i,j)`-entry
of `f` applied to the `k`-th coefficient of `p`. -/
@[simp] theorem coeff_polyToMatrix {R A : Type*} [CommSemiring R] [Semiring A]
    {n : Type*} [DecidableEq n] [Fintype n] (f : A →+* Matrix n n R) (p : A[X]) (i j : n) (k : ℕ) :
    (f.polyToMatrix p i j).coeff k = f (p.coeff k) i j := by
  rw [p.as_sum_range]
  simp only [← C_mul_X_pow_eq_monomial, map_sum, map_mul, RingHom.polyToMatrix_C, map_pow,
    RingHom.polyToMatrix_X, smul_pow, one_pow, Algebra.mul_smul_comm, mul_one, Matrix.sum_apply,
    Matrix.smul_apply, map_apply, smul_eq_mul, X_pow_mul_C, finsetSum_coeff, coeff_C_mul,
    coeff_X_pow, mul_ite, mul_zero, sum_ite_eq, mem_range, Order.lt_add_one_iff]
  split_ifs <;> simp

/-- Each entry of `f.polyToMatrix p` has `natDegree` at most that of `p`. -/
@[simp] theorem natDegree_polyToMatrix_le {R A : Type*} [CommSemiring R] [Semiring A]
    {n : Type*} [DecidableEq n] [Fintype n] (f : A →+* Matrix n n R) (p : A[X]) (i j : n) :
    (f.polyToMatrix p i j).natDegree ≤ p.natDegree := by
  simp +contextual [natDegree_le_iff_coeff_eq_zero, p.coeff_eq_zero_of_natDegree_lt]

/-- If `p` is monic, every diagonal entry of `f.polyToMatrix p` is monic. -/
@[simp] theorem Monic.polyTomatrix {R A : Type*} [CommRing R] [Semiring A]
    {n : Type*} [DecidableEq n] [Fintype n] (f : A →+* Matrix n n R) {p : A[X]} (hp : p.Monic)
    (i : n) : (f.polyToMatrix p i i).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one _ (natDegree_polyToMatrix_le ..) (by simp [hp])

/-- If `p` is monic and the base ring is nontrivial, every diagonal entry of `f.polyToMatrix p`
has the same `natDegree` as `p`. -/
@[simp] theorem Monic.natDegree_polyTomatrix {R A : Type*} [CommRing R] [Nontrivial R] [Semiring A]
    {n : Type*} [DecidableEq n] [Fintype n] (f : A →+* Matrix n n R) {p : A[X]} (hp : p.Monic)
    (i : n) : (f.polyToMatrix p i i).natDegree = p.natDegree :=
  natDegree_eq_of_le_of_coeff_ne_zero (natDegree_polyToMatrix_le ..) (by simp [hp])

/-- If `p` is monic, the next-to-leading coefficient of any diagonal entry of `f.polyToMatrix p`
is the corresponding diagonal entry of `f` applied to the next-to-leading coefficient of `p`. -/
@[simp] theorem Monic.nextCoeff_polyTomatrix {R A : Type*} [CommRing R] [Semiring A]
    {n : Type*} [DecidableEq n] [Fintype n] (f : A →+* Matrix n n R) {p : A[X]} (hp : p.Monic)
    (i : n) : (f.polyToMatrix p i i).nextCoeff = f p.nextCoeff i i := by
  nontriviality R
  simp only [nextCoeff, hp, natDegree_polyTomatrix, natDegree_eq_zero, coeff_polyToMatrix,
    apply_ite, map_zero, Matrix.ite_apply, Matrix.zero_apply, ite_eq_left_iff, ite_eq_right_iff]
  grind [hp.natDegree_eq_zero]

/-- If `p` is monic of positive degree, every off-diagonal entry of `f.polyToMatrix p` has
strictly smaller `natDegree` than `p`. -/
@[simp] theorem Monic.natDegree_polyTomatrix_lt_of_ne {R A : Type*} [CommRing R] [Semiring A]
    {n : Type*} [DecidableEq n] [Fintype n] (f : A →+* Matrix n n R) {p : A[X]}
    (hp : p.Monic) (hp0 : p.natDegree ≠ 0) {i j : n} (h : i ≠ j) :
    (f.polyToMatrix p i j).natDegree < p.natDegree := by
  obtain _ | _ := subsingleton_or_nontrivial R
  · simpa [Subsingleton.elim (_ : R[X]) 0, pos_iff_ne_zero]
  refine (natDegree_polyToMatrix_le f p i j).lt_of_ne fun hfp ↦ ?_
  suffices f (p.coeff p.natDegree) i j = 0 by
    rw [← hfp, ← coeff_polyToMatrix, ← leadingCoeff.eq_1, leadingCoeff_eq_zero] at this
    simp [this, hp0.symm] at hfp
  simp [hp, h]

/-- Successor form of `Monic.natDegree_polyTomatrix_lt_of_ne`. -/
theorem Monic.natDegree_polyTomatrix_add_one_le_of_ne
    {R A : Type*} [CommRing R] [Semiring A]
    {n : Type*} [DecidableEq n] [Fintype n] (f : A →+* Matrix n n R) {p : A[X]}
    (hp : p.Monic) (hp0 : p.natDegree ≠ 0) {i j : n} (h : i ≠ j) :
    (f.polyToMatrix p i j).natDegree + 1 ≤ p.natDegree :=
  Nat.lt_iff_add_one_le.mp (hp.natDegree_polyTomatrix_lt_of_ne f hp0 h)

/-- The determinant of `f.polyToMatrix p` has `natDegree` at most `(card n) * p.natDegree`. -/
@[simp] theorem natDegree_det_polyToMatrix_le {R A : Type*} [CommRing R] [Semiring A]
    {n : Type*} [DecidableEq n] [Fintype n] (f : A →+* Matrix n n R) (p : A[X]) :
    (f.polyToMatrix p).det.natDegree ≤ Fintype.card n * p.natDegree := by
  grw [det_apply]
  refine natDegree_sum_le_of_forall_le _ _ fun _ _ ↦ (natDegree_smul_le _ _).trans ?_
  grw [natDegree_prod_le, sum_le_sum (fun _ _ ↦ natDegree_polyToMatrix_le ..), sum_const,
    card_univ, smul_eq_mul]

/-- The leading coefficient (in degree `(card n) * p.natDegree`) of the determinant of
`f.polyToMatrix p` is the determinant of the matrix `f p.leadingCoeff`. -/
@[simp] theorem coeff_det_polyTomatrix_natDegree_prod_card {R A : Type*} [CommRing R] [Semiring A]
    {n : Type*} [DecidableEq n] [Fintype n] (f : A →+* Matrix n n R) (p : A[X]) :
    (f.polyToMatrix p).det.coeff (Fintype.card n * p.natDegree) = (f p.leadingCoeff).det := by
  rw [det_apply, det_apply, finsetSum_coeff]
  convert sum_congr rfl fun _ _ ↦ coeff_smul ..
  simpa [← card_univ] using
    (coeff_prod_of_natDegree_le _ _ _ fun _ _  ↦ natDegree_polyToMatrix_le ..).symm

/-- For monic `p`, the coefficient of `det (f.polyToMatrix p)` in the expected top degree
`(card n) * p.natDegree` is `1`. -/
theorem Monic.coeff_det_polyTomatrix {R A : Type*} [CommRing R] [Semiring A]
    {n : Type*} [DecidableEq n] [Fintype n] (f : A →+* Matrix n n R) {p : A[X]} (hp : p.Monic) :
    (f.polyToMatrix p).det.coeff (Fintype.card n * p.natDegree) = 1 := by simp [hp]

/-- For monic `p`, the determinant of `f.polyToMatrix p` is monic. -/
@[simp] theorem Monic.det_polyTomatrix {R A : Type*} [CommRing R] [Semiring A]
    {n : Type*} [DecidableEq n] [Fintype n] (f : A →+* Matrix n n R) {p : A[X]} (hp : p.Monic) :
    (f.polyToMatrix p).det.Monic :=
  monic_of_natDegree_le_of_coeff_eq_one _ (natDegree_det_polyToMatrix_le ..) (by simp [hp])

/-- For monic `p` over a nontrivial ring, the determinant of `f.polyToMatrix p` has
`natDegree` exactly `(card n) * p.natDegree`. -/
@[simp] theorem Monic.natDegree_det_polyTomatrix
    {R A : Type*} [CommRing R] [Nontrivial R] [Semiring A]
    {n : Type*} [DecidableEq n] [Fintype n] (f : A →+* Matrix n n R) {p : A[X]} (hp : p.Monic) :
    (f.polyToMatrix p).det.natDegree = Fintype.card n * p.natDegree :=
  natDegree_eq_of_le_of_coeff_ne_zero (natDegree_det_polyToMatrix_le ..) (by simp [hp])

/-- For monic `p`, the next-to-leading coefficient of `det (f.polyToMatrix p)` equals the trace
of the matrix `f p.nextCoeff`. -/
@[simp] theorem Monic.nextCoeff_det_polyTomatrix {R A : Type*} [CommRing R] [Semiring A]
    {n : Type*} [DecidableEq n] [Fintype n] (f : A →+* Matrix n n R) {p : A[X]} (hp : p.Monic) :
    (f.polyToMatrix p).det.nextCoeff = (f p.nextCoeff).trace := by
  nontriviality R
  have := hp.natDegree_det_polyTomatrix f
  obtain hp0 | hp0 := eq_zero_or_pos (f.polyToMatrix p).det.natDegree
  · rw [this, mul_eq_zero, Fintype.card_eq_zero_iff, hp.natDegree_eq_zero] at hp0
    obtain hp0 | rfl := hp0 <;> simp
  have hnp := mul_pos_iff.mp (this ▸ hp0)
  nth_rw 1 [nextCoeff_of_natDegree_pos hp0, det_apply, finsetSum_coeff]
  simp_rw [Units.smul_def, coeff_zsmul]
  rw [sum_eq_single 1 (fun σ _ hσ ↦ ?_) (by simp)]
  · simp only [Equiv.Perm.sign_one, Units.val_one, Equiv.Perm.coe_one, id_eq, one_smul]
    have : (f.polyToMatrix p).det.natDegree = (∏ x, f.polyToMatrix p x x).natDegree := by
      simp [this, natDegree_prod_of_monic, hp]
    rw [this, ← nextCoeff_of_natDegree_pos (by grind), nextCoeff_prod _ _ (by simp [hp])]
    simp [hp.nextCoeff_polyTomatrix, Matrix.trace]
  · rw [← Units.smul_def, smul_eq_zero_iff_eq, this]
    refine coeff_eq_zero_of_natDegree_lt <| Nat.lt_sub_of_add_lt ?_
    obtain ⟨i, his, j, hjs, hij⟩ := one_lt_card.mp (σ.one_lt_card_support_of_ne_one hσ)
    rw [Equiv.Perm.mem_support] at his hjs
    have hn := (σ.two_le_card_support_of_ne_one hσ).trans (card_le_univ _)
    grw [natDegree_prod_le, Nat.lt_iff_add_one_le, ← sum_erase_add (a := i) (h := by simp),
      add_assoc (Finset.sum _ _), add_right_comm, ← sum_erase_add (a := j) (h := by grind),
      add_assoc (Finset.sum _ _), sum_le_sum fun _ _ ↦ natDegree_polyToMatrix_le ..,
      sum_const, card_erase_of_mem (by grind), card_erase_of_mem (by grind), card_univ,
      nsmul_eq_mul, hp.natDegree_polyTomatrix_add_one_le_of_ne f (by grind) his,
      hp.natDegree_polyTomatrix_add_one_le_of_ne f (by grind) hjs, ← add_one_mul, ← add_one_mul]
    grind

attribute [local instance] algebra

/-- Under the local `Algebra R[X] S[X]` instance, the algebra map sends `X` to `X`. -/
theorem algebraMap_X (R S : Type*) [CommSemiring R] [Semiring S] [Algebra R S] :
    algebraMap R[X] S[X] X = X := by simp

/-- Under the local `Algebra R[X] S[X]` instance, the algebra map sends `X ^ n` to `X ^ n`. -/
theorem algebraMap_X_pow (R S : Type*) [CommSemiring R] [Semiring S] [Algebra R S] (n : ℕ) :
    algebraMap R[X] S[X] (X ^ n) = X ^ n := by simp

/-- The `R[X]`-algebra isomorphism `R[X] ⊗[R] S ≃ S[X]` sending `X ⊗ 1 ↦ X` and `1 ⊗ s ↦ C s`,
witnessing that `S[X]` is the polynomial algebra over `S` realized as the base change of `R[X]`
along `R → S`. -/
noncomputable def tensorEquiv (R S : Type*) [CommSemiring R] [Semiring S] [Algebra R S] :
    R[X] ⊗[R] S ≃ₐ[R[X]] S[X] :=
  .ofAlgHom (lift (ofId _ _) CAlgHom (by simp [commute_iff_eq, Polynomial.ext_iff, commutes]))
    { __ := eval₂AlgHom includeRight (X ⊗ₜ 1) (by simp [commute_iff_eq])
      commutes' p := by
        rw [p.as_sum_support]
        simp [C_mul_X_pow_eq_monomial] }
    (AlgHom.restrictScalars_injective R <| algHom_ext' (by ext; simp) (by simp))
    (by ext; simp)

/-- Image of an elementary tensor `X ^ n ⊗ s` under `tensorEquiv`. -/
@[simp] theorem tensorEquiv_X_pow_tmul (R : Type*) {S : Type*} [CommSemiring R] [Semiring S]
    [Algebra R S] (n : ℕ) (s : S) : tensorEquiv R S ((X ^ n) ⊗ₜ s) = C s * X ^ n := by
  simp [tensorEquiv]

/-- Image of an elementary tensor `X ⊗ s` under `tensorEquiv`. -/
@[simp] theorem tensorEquiv_X_tmul (R : Type*) {S : Type*} [CommSemiring R] [Semiring S]
    [Algebra R S] (s : S) : tensorEquiv R S (X ⊗ₜ s) = C s * X := by
  simp [tensorEquiv]

/-- Image of a constant elementary tensor `C r ⊗ s` under `tensorEquiv`. -/
@[simp] theorem tensorEquiv_C_tmul {R S : Type*} [CommSemiring R] [Semiring S]
    [Algebra R S] (r : R) (s : S) : tensorEquiv R S (C r ⊗ₜ s) = C (r • s) := by
  simp [tensorEquiv, Algebra.smul_def]

/-- Image of a constant elementary tensor `1 ⊗ s` under `tensorEquiv`. -/
@[simp] theorem tensorEquiv_1_tmul (R : Type*) {S : Type*} [CommSemiring R] [Semiring S]
    [Algebra R S] (s : S) : tensorEquiv R S (1 ⊗ₜ s) = C s := by
  simp [tensorEquiv]

/-- Inverse image of a constant polynomial `C s` under `tensorEquiv`. -/
@[simp] theorem symm_tensorEquiv_C (R : Type*) {S : Type*} [CommSemiring R] [Semiring S]
    [Algebra R S] (s : S) : (tensorEquiv R S).symm (C s) = 1 ⊗ₜ s := by simp [tensorEquiv]

/-- Inverse image of the indeterminate `X` under `tensorEquiv`. -/
@[simp] theorem symm_tensorEquiv_X (R S : Type*) [CommSemiring R] [Semiring S]
    [Algebra R S] : (tensorEquiv R S).symm X = X ⊗ₜ 1 := by simp [tensorEquiv]

/-- The inclusion `S → S[X]` sending `s ↦ monomial 0 s = C s` is a base change of `R → R[X]`,
i.e. `S[X]` is the pushout of `R[X]` and `S` over `R`. -/
theorem isBaseChange (R S : Type*) [CommSemiring R] [Semiring S] [Algebra R S] :
    IsBaseChange R[X] ((monomial (R := S) 0).restrictScalars R) :=
  .of_equiv (tensorEquiv R S) (by simp)

/-- An `R`-basis `b` of `S` lifts to an `R[X]`-basis of `S[X]` with the same indexing set,
sending each basis vector to its image under `C : S → S[X]`. -/
noncomputable def basis {R S ι : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    (b : Basis ι R S) : Basis ι R[X] S[X] := IsBaseChange.basis b (isBaseChange R S)

/-- The lifted `R[X]`-basis of `S[X]`, as a function, is `C ∘ b : ι → S[X]`. -/
@[simp] theorem coe_basis {R S ι : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    (b : Basis ι R S) : ⇑(basis b) = C ∘ b := by ext; simp [basis, IsBaseChange.basis_apply]

/-- The `i`-th coordinate of `C s` in the lifted basis is `C` applied to the `i`-th coordinate
of `s` in the original basis. -/
@[simp] theorem basis_repr_C {R S ι : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    (b : Basis ι R S) (s : S) (i : ι) : (basis b).repr (C s) i = C (b.repr s i) :=
  IsBaseChange.basis_repr_comp_apply ..

/-- The `i`-th coordinate of `C s * X ^ n` in the lifted basis is `C (b.repr s i) * X ^ n`. -/
@[simp] theorem basis_repr_C_mul_X_pow {R S ι : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    (b : Basis ι R S) (s : S) (n : ℕ) (i : ι) :
    (basis b).repr (C s * X ^ n) i = C (b.repr s i) * X ^ n := by
  rw [← X_pow_mul_C, ← algebraMap_X_pow R, ← Algebra.smul_def, map_smul, Finsupp.smul_apply,
    basis_repr_C, smul_eq_mul, X_pow_mul_C]

/-- The `i`-th coordinate of `C s * X` in the lifted basis is `C (b.repr s i) * X`. -/
@[simp] theorem basis_repr_C_mul_X {R S ι : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    (b : Basis ι R S) (s : S) (i : ι) :
    (basis b).repr (C s * X) i = C (b.repr s i) * X := by
  simpa using basis_repr_C_mul_X_pow b s 1 i

/-- This is just `Algebra.norm`, but since the instance `Polynomial.algebra : Algebra R[X] S[X]`
is problematic, it is not a global instance, so this has to be a separate definition. -/
noncomputable def norm (R S : Type*) [CommRing R] [Ring S] [Algebra R S] : S[X] →* R[X] :=
  Algebra.norm R[X]

/-- The left-multiplication matrix of `S[X]` over `R[X]` in the lifted basis, restricted to `R`,
agrees with the lift along `polyToMatrix` of the left-multiplication matrix of `S` over `R`. -/
@[simp] theorem leftMulMatrix_basis {R S ι : Type*} [CommRing R] [Ring S] [Algebra R S]
    [Fintype ι] [DecidableEq ι] (b : Basis ι R S) :
    (leftMulMatrix (basis b)).restrictScalars R = (leftMulMatrix b).polyToMatrix := by
  ext : 2 <;>
  simp [← Matrix.ext_iff, leftMulMatrix_apply, LinearMap.toMatrix_apply, ← map_mul,
    Finsupp.single_apply, one_apply, eq_comm]

/-- Pointwise form of `leftMulMatrix_basis`. -/
@[simp] theorem leftMulMatrix_basis_apply {R S ι : Type*} [CommRing R] [Ring S] [Algebra R S]
    [Fintype ι] [DecidableEq ι] (b : Basis ι R S) (p : S[X]) :
    leftMulMatrix (basis b) p = (leftMulMatrix b).polyToMatrix p :=
  congr($(leftMulMatrix_basis b) p)

/-- The `Polynomial.norm R S` of a polynomial `p : S[X]` is the determinant of the lifted
left-multiplication matrix `(leftMulMatrix b).polyToMatrix p`. -/
theorem norm_of_basis {R S ι : Type*} [CommRing R] [Ring S] [Algebra R S]
    [Fintype ι] [DecidableEq ι] (b : Basis ι R S) (p : S[X]) :
    p.norm R S = ((leftMulMatrix b).polyToMatrix p).det := by
  simp [norm, norm_eq_matrix_det (basis b)]

end Polynomial

section trace_redo

namespace Algebra

/-- **Stacks 0BIF** (trace).
The trace of an `R`-algebra `S`, defined as the linear-map trace of left multiplication
`mul R S : S →ₗ[R] End R S`. This works for any `R`-algebra (no commutativity or finite-freeness
assumption on `S`); it agrees with `Algebra.trace R S` whenever the latter is defined. -/
@[stacks 0BIF "trace"]
noncomputable def trace' (R S : Type*) [CommSemiring R] [Semiring S] [Algebra R S] : S →ₗ[R] R :=
  (LinearMap.trace R S).comp (mul R S)

/-- For commutative `S`, the new `trace'` agrees definitionally with the old `Algebra.trace`. -/
@[simp] theorem trace_eq_trace' (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    trace R S = trace' R S := rfl

/-- Computation of `trace' R S s` via the matrix trace of `leftMulMatrix b s` in any basis `b`. -/
theorem trace_eq_matrix_trace' {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι R S) (s : S) :
    trace' R S s = (leftMulMatrix b s).trace := by
  simp [trace', LinearMap.trace_eq_matrix_trace _ b, leftMulMatrix_apply]

/-- The trace of `algebraMap R S x` is `finrank R S • x`. -/
@[simp] theorem trace_algebraMap' {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    [Free R S] (x : R) :
    trace' R S (algebraMap R S x) = finrank R S • x := by
  by_cases H : ∃ s : Finset S, Nonempty (Basis s R S)
  swap
  · simp [finrank_eq_zero_of_not_exists_basis_finset H, trace', LinearMap.trace, H]
  have := Module.Finite.of_basis H.choose_spec.some
  nontriviality R
  have b := Module.finBasis' R S
  rw [trace_eq_matrix_trace' b, AlgHom.commutes, Matrix.algebraMap_eq_diagonal, trace_diagonal]
  simp

/-- The trace of `R` over itself is the identity. -/
@[simp] theorem trace_self' (R : Type*) [CommSemiring R] : trace' R R = .id := by
  ext; simp [trace_eq_matrix_trace' (.singleton (Fin 1) R)]

end Algebra

end trace_redo

/-- Over any basis `b` of a finite free `R`-algebra `S`, the characteristic polynomial of the
left-multiplication matrix `leftMulMatrix b x` agrees with that of the linear map
`Algebra.lmul R S x`. -/
theorem charpoly_leftMulMatrix_eq_charpoly_mul
    {R S : Type*} [CommRing R] [Ring S] [Algebra R S] [Free R S] [Module.Finite R S]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι R S) (x : S) :
    (leftMulMatrix b x).charpoly = (mul R S x).charpoly := by
  rw [leftMulMatrix_apply, coe_lmul_eq_mul, LinearMap.charpoly_toMatrix]

/-- Reformulation of `charmatrix` as `X • 1 - M.map C`, useful for computations involving the
characteristic matrix. -/
theorem Matrix.charmatrix_def {R n : Type*} [CommRing R] [DecidableEq n] [Fintype n]
    (M : Matrix n n R) : M.charmatrix = (X : R[X]) • 1 - M.map C := by
  ext; simp [charmatrix_apply, diagonal_apply, one_apply]

/-- The polynomial norm of the linear factor `X - C s` over a finite free `R`-algebra `S`
agrees with the characteristic polynomial of left multiplication by `s`. -/
@[simp] theorem Polynomial.norm_X_sub_C (R : Type*) {S : Type*} [CommRing R] [Ring S]
    [Algebra R S] [Free R S] [Module.Finite R S] (s : S) :
    (X - C s).norm R S = (mul R S s).charpoly := by
  have b := Module.finBasis' R S
  rw [norm_of_basis b, ← charpoly_leftMulMatrix_eq_charpoly_mul b]
  simp [Matrix.charpoly, charmatrix_def]

/-- The polynomial norm of a constant polynomial `C s` is `C` applied to the algebra norm of `s`. -/
@[simp] theorem Polynomial.norm_C (R : Type*) {S : Type*} [CommRing R] [Ring S]
    [Algebra R S] (s : S) :
    (C s).norm R S = C (Algebra.norm R s) := by
  by_cases H : Module.Free R S ∧ Module.Finite R S
  · obtain ⟨_, _⟩ := H
    have b := Module.finBasis' R S
    rw [norm_of_basis b, norm_eq_matrix_det b, RingHom.map_det]
    simp
  have hS : ¬ ∃ t : Finset S, Nonempty (Basis t R S) :=
    fun ⟨_, ⟨b⟩⟩ ↦ H ⟨.of_basis b, .of_basis b⟩
  rw [Algebra.norm_eq_one_of_not_exists_basis R hS, map_one]
  let _ := Polynomial.algebra R S
  let _ : Algebra R[X] R := (evalRingHom 0).toAlgebra
  have : IsScalarTower R R[X] R :=
    .of_algebraMap_eq fun r ↦ by simp [RingHom.algebraMap_toAlgebra]
  change Algebra.norm R[X] (C s : S[X]) = 1
  refine Algebra.norm_eq_one_of_not_exists_basis R[X] (S := S[X]) ?_ _
  rintro ⟨t, ⟨b⟩⟩
  refine H ?_
  let e : R ⊗[R[X]] S[X] ≃ₗ[R] S :=
    AlgebraTensorModule.congr (.refl R R) (tensorEquiv R S).symm.toLinearEquiv ≪≫ₗ
      AlgebraTensorModule.cancelBaseChange R R[X] R R S ≪≫ₗ TensorProduct.lid R S
  let b' := (Algebra.TensorProduct.basis R b).map e
  exact ⟨.of_basis b', .of_basis b'⟩

/-- If `A` is nontrivial, free over `S` and finite over `R` in a tower, then `S` is finite
over `R`. -/
private theorem finite_of_free_tower_of_nontrivial (R S A : Type*) [CommSemiring R] [Semiring S]
    [Algebra R S] [AddCommMonoid A] [Module S A] [Module R A] [IsScalarTower R S A]
    [Module.Free S A] [Nontrivial A] [Module.Finite R A] : Module.Finite R S := by
  obtain ⟨i⟩ := (Free.chooseBasis S A).index_nonempty
  exact .of_surjective (((Free.chooseBasis S A).coord i).restrictScalars R)
    fun s ↦ ⟨s • Free.chooseBasis S A i, by simp⟩

/-- **Stacks 0BII** (trace).
In a tower `R ⊆ S ⊆ A` of free extensions, the `R`-trace of an `S`-linear endomorphism
`f : A →ₗ[S] A` factors through the `S`-trace: it equals `trace' R S` applied to `f.trace S A`.
This expresses the transitivity of trace at the level of endomorphisms. No finiteness is
assumed: if `S` is not finite over `R` or `A` is not finite over `S`, both sides are `0`. -/
@[stacks 0BII "trace"]
theorem trace_restrictScalars (R : Type*) {S A : Type*}
    [CommSemiring R] [CommSemiring S] [Semiring A]
    [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
    [Module.Free R S] [Module.Free S A]
    (f : A →ₗ[S] A) : (f.restrictScalars R).trace R A = trace' R S (f.trace S A) := by
  have hA : ¬ (∃ s : Finset A, Nonempty (Basis s R A)) → LinearMap.trace R A
      (f.restrictScalars R) = 0 := fun h ↦ by simp [LinearMap.trace, h]
  by_cases hSA : Module.Finite S A
  swap
  · have hS : ¬ ∃ s : Finset A, Nonempty (Basis s S A) := fun ⟨_, ⟨b⟩⟩ ↦ hSA (.of_basis b)
    rw [hA fun ⟨_, ⟨b⟩⟩ ↦ hSA (have := Module.Finite.of_basis b;
      .of_restrictScalars_finite R S A)]
    simp [LinearMap.trace, hS]
  by_cases hRS : Module.Finite R S
  swap
  · cases subsingleton_or_nontrivial A
    · simp [Subsingleton.elim f 0]
    have hS : ¬ ∃ s : Finset S, Nonempty (Basis s R S) := fun ⟨_, ⟨b⟩⟩ ↦ hRS (.of_basis b)
    rw [hA fun ⟨_, ⟨b⟩⟩ ↦ ?_]
    · simp [trace', LinearMap.trace, hS]
    have := Module.Finite.of_basis b
    exact hRS (finite_of_free_tower_of_nontrivial R S A)
  let b := Module.finBasis' R S
  let c := Module.finBasis' S A
  rw [LinearMap.trace_eq_matrix_trace _ (b.smulTower c), LinearMap.trace_eq_matrix_trace _ c,
    trace_eq_matrix_trace' b]
  simp [Matrix.trace, LinearMap.toMatrix_apply, leftMulMatrix_apply, Matrix.sum_apply, mul_comm,
    Fintype.sum_prod_type]

/-- **Stacks 0BII** (generalization).
In a tower `R ⊆ S ⊆ A` of free extensions, with `A` finite over `S` and over `R`, the
characteristic polynomial of the `R`-linear endomorphism `f.restrictScalars R` is the polynomial
norm of the characteristic polynomial of the `S`-linear endomorphism `f`. -/
@[stacks 0BII "generalization"]
theorem charpoly_restrictScalars_of_tower (R : Type*) {S A : Type*}
    [CommRing R] [CommRing S] [AddCommGroup A]
    [Algebra R S] [Module S A] [Module R A] [IsScalarTower R S A]
    [Module.Free R S] [Module.Free S A] [Module.Finite S A]
    [Module.Free R A] [Module.Finite R A]
    (f : A →ₗ[S] A) : (f.restrictScalars R).charpoly = f.charpoly.norm R S := by
  by_cases hRS : Module.Finite R S
  swap
  · have : Subsingleton A := by
      by_contra hA
      rw [not_subsingleton_iff_nontrivial] at hA
      exact hRS (finite_of_free_tower_of_nontrivial R S A)
    have : Nontrivial S := by
      by_contra hS
      rw [not_nontrivial_iff_subsingleton] at hS
      exact hRS inferInstance
    nontriviality R
    have : IsEmpty (Free.ChooseBasisIndex S A) :=
      ⟨fun i ↦ (Free.chooseBasis S A).ne_zero i (Subsingleton.elim _ _)⟩
    have : IsEmpty (Free.ChooseBasisIndex R A) :=
      ⟨fun i ↦ (Free.chooseBasis R A).ne_zero i (Subsingleton.elim _ _)⟩
    simp [LinearMap.charpoly, Matrix.charpoly_isEmpty]
  have b := Module.finBasis' R S; generalize natfreerank R S = m at b ⊢
  have c := Module.finBasis' S A; generalize natfreerank S A = n at c ⊢
  simp_rw [← LinearMap.charpoly_toMatrix _ (b.smulTower c), ← LinearMap.charpoly_toMatrix _ c,
    norm_of_basis b, charpoly, det_det']
  rw [← det_reindex_self (Equiv.prodComm (Fin n) (Fin m))]
  congr 1; ext ij kl : 1; obtain ⟨i, j⟩ := ij; obtain ⟨k, l⟩ := kl
  simp only [charmatrix, scalar_apply, RingHom.mapMatrix_apply, Matrix.sub_apply, diagonal_apply,
    Prod.mk.injEq, map_apply, LinearMap.toMatrix_apply, Basis.smulTower_apply,
    LinearMap.coe_restrictScalars, map_smul, Basis.smulTower_repr, Finsupp.coe_smul, Pi.smul_apply,
    smul_eq_mul, AlgHom.coe_polyToMatrix, reindex_apply, Equiv.prodComm_symm, Equiv.coe_prodComm,
    submatrix_apply, Prod.swap_prod_mk, comp_apply, map_sub, apply_ite, RingHom.polyToMatrix_X,
    map_zero, RingHom.polyToMatrix_C, RingHom.coe_coe, leftMulMatrix_apply, coe_lmul_eq_mul,
    Matrix.ite_apply, Matrix.smul_apply, one_apply, mul_comm, one_mul, zero_mul, Matrix.zero_apply,
    ← ite_and, LinearMap.mul_apply_apply, sub_left_inj, ite_eq_left_iff, not_and, ite_eq_right_iff,
    and_imp]
  grind

/-- **Stacks 0BIJ** (generalization).
Specialization of `charpoly_restrictScalars_of_tower` to left-multiplication: in a tower
`R ⊆ S ⊆ A`, the characteristic polynomial of `mul R A x` equals the polynomial norm over `R[X]`
of the characteristic polynomial of `mul S A x`. -/
@[stacks 0BIJ "generalization"]
theorem charpoly_mul_of_tower (R S : Type*) {A : Type*}
    [CommRing R] [CommRing S] [Ring A]
    [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
    [Module.Free R S] [Module.Free S A] [Module.Finite S A]
    [Module.Free R A] [Module.Finite R A]
    (x : A) : (mul R A x).charpoly = (mul S A x).charpoly.norm R S :=
  charpoly_restrictScalars_of_tower R (mul S A x)

/-- **Stacks 0BIJ** (trace).
Transitivity of trace in a tower of free extensions:
`trace' R S ∘ trace' S A = trace' R A`. -/
@[stacks 0BIJ "trace"]
theorem trace_trace (R S : Type*) {A : Type*}
    [CommSemiring R] [CommSemiring S] [Semiring A]
    [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
    [Module.Free R S] [Module.Free S A]
    (x : A) : trace' R S (trace' S A x) = trace' R A x := (trace_restrictScalars R (mul S A x)).symm

/-- In a tower `R ⊆ S ⊆ A` of finite free extensions, the characteristic polynomial of
left-multiplication by `algebraMap S A x` on `A` (as an `R`-module) is the characteristic
polynomial of left-multiplication by `x` on `S` raised to the `[A : S]`-th power. -/
theorem charPoly_mul_algebraMap_of_tower (R A : Type*) {S : Type*}
    [CommRing R] [CommRing S] [Ring A]
    [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
    [Module.Free R S] [Module.Finite R S] [Module.Free S A]
    [Module.Free R A] [Module.Finite R A] (x : S) :
    (mul R A (algebraMap S A x)).charpoly = (mul R S x).charpoly ^ Module.finrank S A := by
  have := Module.Finite.of_restrictScalars_finite R S A
  rw [charpoly_mul_of_tower R S, ← coe_lmul_eq_mul, AlgHom.commutes, algebraMap_end_eq_smul_id]
  simp

/-- Conjugation of `mul R A x` by an `R`-algebra equivalence `e : A ≃ₐ[R] B` gives
`mul R B (e x)`. -/
theorem Algebra.conj_mul
    {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) (x : A) :
    e.toLinearEquiv.conj (mul R A x) = mul R B (e x) := by
  ext; simp

/-- On the simple `R`-algebra `R[x] = R⟨{x}⟩`, the characteristic polynomial of multiplication
by `x` equals the minimal polynomial of `x`. -/
theorem charpoly_mul_adjoin_eq_minpoly
    (R : Type*) [CommRing R] {S : Type*} [Ring S] [Algebra R S] (x : S)
    [Free R R[x]] [Module.Finite R R[x]] :
    (mul R R[x] ⟨x, by simp⟩).charpoly = minpoly R x := by
  let y : R[x] := ⟨x, by simp⟩
  let e : (R[X] ⧸ RingHom.ker (aeval (R := R) x)) ≃ₐ[R] R[x] :=
    (Ideal.quotientKerEquivRange _).trans <| Subalgebra.equivOfEq _ _
      (adjoin_singleton_eq_range_aeval _ _).symm
  have := Free.of_equiv e.symm.toLinearEquiv
  have := Module.Finite.equiv e.symm.toLinearEquiv
  have hex : e (X : R[X]) = y := by simp [e, y]
  have hey : e.symm y = (X : R[X]) := by rw [e.symm_apply_eq, hex]
  rw [← e.symm.toLinearEquiv.charpoly_conj, Algebra.conj_mul, hey,
    ← minpoly_eq_of_free_quotient, ← minpoly.algEquiv_eq e, hex,
    ← minpoly.algHom_eq (Subalgebra.val _) Subtype.val_injective]
  rfl

/-- **Stacks 0BIG**.
For a finite free extension `R ⊆ S` and `x ∈ S` such that `R[x]` is free over `R` and `S` is
free over `R[x]`, the characteristic polynomial of `Algebra.lmul R S x` equals
`(minpoly R x) ^ [S : R[x]]`. -/
@[stacks 0BIG]
theorem charPoly_mul_eq_minpoly_pow (R : Type*) {S : Type*}
    [CommRing R] [Ring S] [Algebra R S] [Free R S] [Module.Finite R S]
    (x : S) [Free R R[x]] [Free R[x] S] :
    (mul R S x).charpoly = minpoly R x ^ Module.finrank R[x] S := by
  have := Finite.of_restrictScalars_finite R R[x] S
  have := finite_adjoin_simple_of_isIntegral (IsIntegral.isIntegral (R := R) x)
  let y : R[x] := ⟨x, by simp⟩
  have hx : mul R S x = (y • 1 : S →ₗ[R[x]] S).restrictScalars R := rfl
  rw [hx, charpoly_restrictScalars_of_tower, LinearMap.charpoly_smul_one, map_pow, norm_X_sub_C,
    charpoly_mul_adjoin_eq_minpoly]

/-- For a finite free `R`-algebra `S` and `x : S`, `norm R x` equals
`(-1) ^ [S : R]` times the constant coefficient of the characteristic polynomial of
left-multiplication by `x`. -/
theorem norm_eq_neg_one_pow_finrank_mul_constantCoeff_charpoly (R : Type*) {S : Type*}
    [CommRing R] [Ring S] [Algebra R S] [Free R S] [Module.Finite R S] (x : S) :
    norm R x = (-1) ^ finrank R S * (mul R S x).charpoly.constantCoeff := by
  nontriviality R
  let b := Module.finBasis R S
  rw [norm_eq_matrix_det b, det_eq_sign_charpoly_coeff,
    charpoly_leftMulMatrix_eq_charpoly_mul, constantCoeff_apply, Fintype.card_fin]

/-- **Stacks 0BIH**.
For a finite extension `R ⊆ S` and `x ∈ S` such that `R[x]` is free over `R` and `S` is
free over `R[x]` (so that `S` is free over `R`), `norm R x` equals `(-1) ^ [S : R]` times the
constant coefficient of `minpoly R x` raised to the `[S : R[x]]`-th power. -/
@[stacks 0BIH]
theorem norm_eq_neg_one_pow_finrank_mul_constantCoeff_minpoly_pow_finrank (R : Type*) {S : Type*}
    [CommRing R] [Ring S] [Algebra R S] [Module.Finite R S]
    (x : S) [Free R R[x]] [Free R[x] S] :
    norm R x = (-1) ^ finrank R S * (minpoly R x).constantCoeff ^ finrank R[x] S := by
  have := Module.Free.trans (R := R) (S := R[x]) (M := S)
  rw [norm_eq_neg_one_pow_finrank_mul_constantCoeff_charpoly, charPoly_mul_eq_minpoly_pow, map_pow]
