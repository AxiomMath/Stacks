module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Algebra.DirectSum.Module

/-!
# Tensor products along a ring isomorphism

Let `ψ : R ≃+* R'` be an isomorphism of commutative rings, `M`, `N` modules over `R'` and `M'`,
`N'` modules over `R`, and let `e : M ≃+ M'`, `f : N ≃+ N'` be additive bijections that are
semilinear along `ψ`, in the sense that `e (ψ r • m) = r • e m`. Then `m ⊗ n ↦ e m ⊗ f n` is a
well-defined bijection `M ⊗[R'] N ⟶ M' ⊗[R] N'`.

## Main definitions

* `Stacks.WeilDeRham.tensorMapOfSemilinear`: the map `m ⊗ n ↦ e m ⊗ f n`.

## Main results

* `Stacks.WeilDeRham.bijective_tensorMapOfSemilinear`: it is bijective.
* `Stacks.WeilDeRham.bijective_of_directSum_tensorMapOfSemilinear`: a map out of a direct sum of
  such tensor products that is compatible with a bijection out of the other one is bijective.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Stacks.WeilDeRham

section Single

variable {R R' : Type*} [CommRing R] [CommRing R'] (ψ : R ≃+* R')
  {M N M' N' : Type*} [AddCommGroup M] [Module R' M] [AddCommGroup N] [Module R' N]
  [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
  (e : M ≃+ M') (he : ∀ (r : R) (m : M), e (ψ r • m) = r • e m)
  (f : N ≃+ N') (hf : ∀ (r : R) (n : N), f (ψ r • n) = r • f n)

include he in
/-- The inverse of a semilinear bijection is semilinear. -/
theorem symm_smul_of_semilinear (r : R) (m' : M') : e.symm (r • m') = ψ r • e.symm m' := by
  apply e.injective
  rw [AddEquiv.apply_symm_apply, he, AddEquiv.apply_symm_apply]

/-- **The map `M ⊗[R'] N ⟶ M' ⊗[R] N'`, `m ⊗ n ↦ e m ⊗ f n`**, of semilinear bijections along a
ring isomorphism `ψ : R ≃+* R'`. -/
def tensorMapOfSemilinear : M ⊗[R'] N →+ M' ⊗[R] N' :=
  TensorProduct.liftAddHom
    { toFun := fun m =>
        { toFun := fun n => e m ⊗ₜ[R] f n
          map_zero' := by rw [map_zero, TensorProduct.tmul_zero]
          map_add' := fun n n' => by rw [map_add, TensorProduct.tmul_add] }
      map_zero' := by ext n; simp
      map_add' := fun m m' => by ext n; simp [TensorProduct.add_tmul] }
    (fun r' m n => by
      change e (r' • m) ⊗ₜ[R] f n = e m ⊗ₜ[R] f (r' • n)
      obtain ⟨r, rfl⟩ := ψ.surjective r'
      rw [he, hf, TensorProduct.smul_tmul])

/-- `Stacks.WeilDeRham.tensorMapOfSemilinear` sends `m ⊗ n` to `e m ⊗ f n`. -/
@[simp]
theorem tensorMapOfSemilinear_tmul (m : M) (n : N) :
    tensorMapOfSemilinear ψ e he f hf (m ⊗ₜ n) = e m ⊗ₜ f n :=
  TensorProduct.liftAddHom_tmul _ _ _ _

/-- The inverse map `M' ⊗[R] N' ⟶ M ⊗[R'] N`. -/
def tensorMapOfSemilinearInv : M' ⊗[R] N' →+ M ⊗[R'] N :=
  TensorProduct.liftAddHom
    { toFun := fun m' =>
        { toFun := fun n' => e.symm m' ⊗ₜ[R'] f.symm n'
          map_zero' := by rw [map_zero, TensorProduct.tmul_zero]
          map_add' := fun n n' => by rw [map_add, TensorProduct.tmul_add] }
      map_zero' := by ext n; simp
      map_add' := fun m m' => by ext n; simp [TensorProduct.add_tmul] }
    (fun r m' n' => by
      change e.symm (r • m') ⊗ₜ[R'] f.symm n' = e.symm m' ⊗ₜ[R'] f.symm (r • n')
      rw [symm_smul_of_semilinear ψ e he, symm_smul_of_semilinear ψ f hf,
        TensorProduct.smul_tmul])

/-- Two additive maps that are inverse on pure tensors are inverse on all tensors. -/
private theorem leftInverse_of_tmul {S : Type*} [CommSemiring S] {A B C : Type*} [AddCommMonoid A]
    [Module S A] [AddCommMonoid B] [Module S B] [AddCommMonoid C] (g : A ⊗[S] B →+ C)
    (h : C →+ A ⊗[S] B) (H : ∀ a b, h (g (a ⊗ₜ b)) = a ⊗ₜ b) : Function.LeftInverse h g := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => exact H m n
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- **The map `m ⊗ n ↦ e m ⊗ f n` along a ring isomorphism is bijective.** -/
theorem bijective_tensorMapOfSemilinear :
    Function.Bijective (tensorMapOfSemilinear ψ e he f hf) := by
  refine ⟨Function.LeftInverse.injective (g := tensorMapOfSemilinearInv ψ e he f hf)
    (leftInverse_of_tmul _ _ fun m n => ?_),
    Function.RightInverse.surjective (g := tensorMapOfSemilinearInv ψ e he f hf)
    (leftInverse_of_tmul _ _ fun m n => ?_)⟩
  · show e.symm (e m) ⊗ₜ[R'] f.symm (f n) = m ⊗ₜ n
    rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  · show tensorMapOfSemilinear ψ e he f hf (e.symm m ⊗ₜ[R'] f.symm n) = m ⊗ₜ n
    rw [tensorMapOfSemilinear_tmul, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

end Single

section DirectSum

variable {R R' : Type*} [CommRing R] [CommRing R'] (ψ : R ≃+* R') {ι : Type*} [DecidableEq ι]
  {M N : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R' (M i)] [∀ i, AddCommGroup (N i)]
  [∀ i, Module R' (N i)]
  {M' N' : ι → Type*} [∀ i, AddCommGroup (M' i)] [∀ i, Module R (M' i)]
  [∀ i, AddCommGroup (N' i)] [∀ i, Module R (N' i)]
  (e : ∀ i, M i ≃+ M' i) (he : ∀ i (r : R) (m : M i), e i (ψ r • m) = r • e i m)
  (f : ∀ i, N i ≃+ N' i) (hf : ∀ i (r : R) (n : N i), f i (ψ r • n) = r • f i n)

include ψ he hf in
/-- **A direct sum of tensor products, compared along a ring isomorphism.** If an additive map
`F : ⨁ᵢ M'ᵢ ⊗[R] N'ᵢ ⟶ T` carries `m ⊗ n` in the summand `i` to the image of `e⁻¹ m ⊗ f⁻¹ n`
under a bijection `Φ : ⨁ᵢ Mᵢ ⊗[R'] Nᵢ ⟶ T`, then `F` is bijective. -/
theorem bijective_of_directSum_tensorMapOfSemilinear {T : Type*} [AddCommGroup T]
    (Φ : (DirectSum ι fun i => M i ⊗[R'] N i) →+ T) (hΦ : Function.Bijective Φ)
    (F : (DirectSum ι fun i => M' i ⊗[R] N' i) →+ T)
    (hF : ∀ i (m : M' i) (n : N' i),
      F (DirectSum.of (fun i => M' i ⊗[R] N' i) i (m ⊗ₜ n)) =
        Φ (DirectSum.of (fun i => M i ⊗[R'] N i) i ((e i).symm m ⊗ₜ (f i).symm n))) :
    Function.Bijective F := by
  let τ := fun i => tensorMapOfSemilinear ψ (e i) (he i) (f i) (hf i)
  let G : (DirectSum ι fun i => M i ⊗[R'] N i) →+ DirectSum ι fun i => M' i ⊗[R] N' i :=
    DFinsupp.mapRange.addMonoidHom τ
  have hG : Function.Bijective G :=
    (DFinsupp.mapRange.addEquiv (fun i => AddEquiv.ofBijective (τ i)
      (bijective_tensorMapOfSemilinear ψ (e i) (he i) (f i) (hf i)))).bijective
  have key : F.comp G = Φ := by
    refine DirectSum.addHom_ext fun i t => ?_
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul m n =>
      have hG' : G (DirectSum.of _ i (m ⊗ₜ n)) = DirectSum.of _ i (e i m ⊗ₜ f i n) := by
        show DFinsupp.mapRange (fun i => τ i) (fun i => map_zero (τ i))
          (DFinsupp.single i (m ⊗ₜ[R'] n)) = _
        rw [DFinsupp.mapRange_single]
        exact congrArg (DFinsupp.single i) (tensorMapOfSemilinear_tmul _ _ _ _ _ m n)
      rw [AddMonoidHom.comp_apply, hG', hF, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
    | add t t' ht ht' => simp only [map_add, ht, ht']
  refine (Function.Bijective.of_comp_iff _ hG).1 ?_
  rwa [← AddMonoidHom.coe_comp, key]

end DirectSum

end Stacks.WeilDeRham

end
