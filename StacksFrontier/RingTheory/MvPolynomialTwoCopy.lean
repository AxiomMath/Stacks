module

public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Two copies of the variables of a polynomial ring
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace MvPolynomial

/-- The ring map `A[E] → A[E][E']` sending the variable `X e` to `X e + C (X e)`, i.e. the
"diagonal" embedding of the first copy of the variables shifted by the second. -/
noncomputable def diagShift (A : Type u) [CommRing A] (E : Type v) :
    MvPolynomial E A →+* MvPolynomial E (MvPolynomial E A) :=
  MvPolynomial.eval₂Hom
    ((MvPolynomial.C : MvPolynomial E A →+* MvPolynomial E (MvPolynomial E A)).comp
      (MvPolynomial.C : A →+* MvPolynomial E A))
    (fun e => (MvPolynomial.X e : MvPolynomial E (MvPolynomial E A)) +
      MvPolynomial.C (MvPolynomial.X e))

namespace TwoCopy

variable (A : Type u) [CommRing A] (E : Type v)

/-- The `A[E]`-algebra automorphism of `A[E][E']` sending `X e` to `X e - C (X e)`; it undoes
`MvPolynomial.diagShift`. -/
noncomputable def unshift :
    MvPolynomial E (MvPolynomial E A) ≃ₐ[MvPolynomial E A]
      MvPolynomial E (MvPolynomial E A) :=
  AlgEquiv.ofAlgHom
    (aeval fun e => (X e : MvPolynomial E (MvPolynomial E A)) - C (X e : MvPolynomial E A))
    (aeval fun e => (X e : MvPolynomial E (MvPolynomial E A)) + C (X e : MvPolynomial E A))
    (by ext e; simp) (by ext e; simp)

/-- `unshift` undoes `diagShift`: the composite is the coefficient map `A[E] → A[E][E']`
sending `X e` to `X e`. -/
theorem unshift_comp_diagShift :
    (unshift A E).toAlgHom.toRingHom.comp (diagShift A E) =
      map (MvPolynomial.C : A →+* MvPolynomial E A) := by
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun e => ?_) <;> simp [diagShift, unshift]

/-- `A[E][E'] ≃ A[E] ⊗[A] A[E]`, the second factor carrying the variables, composed with
`unshift` so that `diagShift t` is carried to `1 ⊗ₜ t`. -/
noncomputable def twoCopy :
    MvPolynomial E (MvPolynomial E A) ≃ₐ[MvPolynomial E A]
      MvPolynomial E A ⊗[A] MvPolynomial E A :=
  (unshift A E).trans (algebraTensorAlgEquiv (σ := E) A (MvPolynomial E A)).symm

/-- `twoCopy` carries `diagShift t` to `1 ⊗ₜ t`. -/
theorem twoCopy_diagShift (t : MvPolynomial E A) :
    twoCopy A E (diagShift A E t) = 1 ⊗ₜ t := by
  have h := RingHom.congr_fun (unshift_comp_diagShift A E) t
  simp only [twoCopy, AlgEquiv.trans_apply]
  rw [show (unshift A E) (diagShift A E t) = map (MvPolynomial.C : A →+* MvPolynomial E A) t from h,
    show (MvPolynomial.C : A →+* MvPolynomial E A) =
      algebraMap A (MvPolynomial E A) from rfl,
    algebraTensorAlgEquiv_symm_map]

variable (V : Type w) [AddCommGroup V] [Module A V] [Module (MvPolynomial E A) V]
  [IsScalarTower A (MvPolynomial E A) V]

/-- Cancelling the base change: `(A[E] ⊗[A] A[E]) ⊗[A[E]] V ≃ V ⊗[A] A[E]`, where the first
factor of the left-hand tensor square acts on `V`. -/
noncomputable def cancel :
    (MvPolynomial E A ⊗[A] MvPolynomial E A) ⊗[MvPolynomial E A] V ≃ₗ[MvPolynomial E A]
      V ⊗[A] MvPolynomial E A :=
  (TensorProduct.comm (MvPolynomial E A) (MvPolynomial E A ⊗[A] MvPolynomial E A) V).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A (MvPolynomial E A)
      (MvPolynomial E A) V (MvPolynomial E A))

/-- The comparison map of the two copies. -/
noncomputable def fullEquiv :
    MvPolynomial E (MvPolynomial E A) ⊗[MvPolynomial E A] V ≃ₗ[A]
      MvPolynomial E A ⊗[A] V :=
  (((LinearEquiv.rTensor V (twoCopy A E).toLinearEquiv).trans
    (cancel A E V)).restrictScalars A).trans
      (TensorProduct.comm A V (MvPolynomial E A))

/-- After `cancel` and the swap of factors, multiplication by `1 ⊗ₜ t` on the left becomes the
action of `t` on the left-hand factor of `A[E] ⊗[A] V`. -/
theorem cancel_comm_smul (t : MvPolynomial E A)
    (y : MvPolynomial E A ⊗[A] MvPolynomial E A) (v : V) :
    TensorProduct.comm A V (MvPolynomial E A) (cancel A E V (((1 ⊗ₜ t) * y) ⊗ₜ v)) =
      t • TensorProduct.comm A V (MvPolynomial E A) (cancel A E V (y ⊗ₜ v)) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul t₁ t₂ =>
      simp [cancel, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul']
  | add y z hy hz =>
      simp only [mul_add, TensorProduct.add_tmul, map_add, hy, hz, smul_add]

/-- The comparison map on a pure tensor, in terms of `twoCopy`, `cancel` and the swap. -/
private theorem fullEquiv_tmul (s : MvPolynomial E (MvPolynomial E A)) (v : V) :
    fullEquiv A E V (s ⊗ₜ v) =
      TensorProduct.comm A V (MvPolynomial E A) (cancel A E V (twoCopy A E s ⊗ₜ v)) := by
  simp only [fullEquiv, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    LinearEquiv.rTensor, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    AlgEquiv.toLinearEquiv_apply]

/-- The comparison map sends `1 ⊗ₜ v` to `1 ⊗ₜ v`. -/
theorem fullEquiv_one_tmul (v : V) :
    fullEquiv A E V ((1 : MvPolynomial E (MvPolynomial E A)) ⊗ₜ v) = 1 ⊗ₜ v := by
  simp only [fullEquiv_tmul, map_one, cancel, Algebra.TensorProduct.one_def,
    LinearEquiv.trans_apply, TensorProduct.comm_tmul,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]

/-- The comparison map carries the action of `diagShift t` to the action of `t` on the
left-hand factor of `A[E] ⊗[A] V`. -/
theorem fullEquiv_smul (t : MvPolynomial E A)
    (x : MvPolynomial E (MvPolynomial E A) ⊗[MvPolynomial E A] V) :
    fullEquiv A E V (diagShift A E t • x) = t • fullEquiv A E V x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s v =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, fullEquiv_tmul, fullEquiv_tmul, map_mul,
        twoCopy_diagShift]
      exact cancel_comm_smul A E V t (twoCopy A E s) v
  | add x y hx hy =>
      simp only [smul_add, map_add, hx, hy]

end TwoCopy

/-- **The two-copy comparison.** Let `T = A[E]` and `S = T[E]`, regard `S` as a `T`-algebra
through the coefficient inclusion `C`, and let `V` be a `T`-module. Then `S ⊗[T] V` is
isomorphic to `T ⊗[A] V` by an `A`-linear isomorphism carrying the action of `T` on the left
through `diagShift` to the action of `T` on the left-hand factor on the right. -/
theorem exists_diagShift_tensorEquiv (A : Type u) [CommRing A] (E : Type v)
    (V : Type w) [AddCommGroup V] [Module A V] [Module (MvPolynomial E A) V]
    [IsScalarTower A (MvPolynomial E A) V] :
    ∃ e : (MvPolynomial E (MvPolynomial E A) ⊗[MvPolynomial E A] V) ≃ₗ[A]
        (MvPolynomial E A ⊗[A] V),
      ∀ (t : MvPolynomial E A) (x : MvPolynomial E (MvPolynomial E A) ⊗[MvPolynomial E A] V),
        e (diagShift A E t • x) = t • e x :=
  ⟨TwoCopy.fullEquiv A E V, TwoCopy.fullEquiv_smul A E V⟩

end MvPolynomial

end
