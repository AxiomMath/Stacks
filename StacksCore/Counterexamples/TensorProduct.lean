module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.GroupTheory.MonoidLocalization.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-! ## Tensor product does not preserve exactness -/

@[expose] public section

universe u v v' w

instance ULift.isDomain {R : Type u} [Ring R] [IsDomain R] : IsDomain (ULift.{v, u} R) :=
  ULift.ringEquiv.toMulEquiv.isDomain

instance :
    Nontrivial (TensorProduct (ULift.{u, 0} ℤ) (ULift.{v', 0} ℤ) (ULift.{w, 0} (ZMod 2))) :=
  (TensorProduct.congr (ULift.moduleEquiv.trans ULift.moduleEquiv.symm)
      (LinearEquiv.refl (ULift.{u, 0} ℤ) (ULift.{w, 0} (ZMod 2))) ≪≫ₗ
    TensorProduct.lid (ULift.{u, 0} ℤ) (ULift.{w, 0} (ZMod 2))).toEquiv.nontrivial

@[stacks 00DH]
theorem tensorRight_not_preserve_exactness :
    ¬ ∀ (R : Type u) (_ : CommRing R) (M₁ : Type v)
      (M₂ M₃ : Type v') (N : Type w)
      (_ : AddCommGroup M₁) (_ : Module R M₁)
      (_ : AddCommGroup M₂) (_ : Module R M₂)
      (_ : AddCommGroup M₃) (_ : Module R M₃)
      (_ : AddCommGroup N) (_ : Module R N)
      (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃),
      Function.Exact f g →
      Function.Exact (f.rTensor N) (g.rTensor N) := by
  simp_rw [not_forall]
  use ULift.{u, 0} ℤ, inferInstance, PUnit, ULift ℤ, ULift ℤ, ULift (ZMod 2), inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, (2 : ℤ) • LinearMap.id (R := ULift.{u, 0} ℤ), ?_, ?_
  · simp [← LinearMap.ker_eq_bot, SetLike.ext_iff, mul_eq_zero (M₀ := ULift.{v', 0} ℤ),
      (by grind : 2 ≠ (0 : ULift.{v', 0} ℤ))]
  · simp only [Function.Exact, zsmul_eq_mul, Int.cast_ofNat, LinearMap.rTensor_zero, Set.mem_range,
      LinearMap.zero_apply, exists_const, not_forall]
    use 1 ⊗ₜ 1
    simp only [LinearMap.rTensor_tmul, Module.End.mul_apply, LinearMap.id_coe, id_eq,
      Module.End.ofNat_apply, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
    rw [← Algebra.TensorProduct.one_def]
    simp only [zero_ne_one, iff_false, ne_eq, not_not]
    rw [← Int.cast_two, ← zsmul_one, TensorProduct.smul_tmul]
    simp [show (2 : ULift.{w} (ZMod 2)) = 0 by rfl]
