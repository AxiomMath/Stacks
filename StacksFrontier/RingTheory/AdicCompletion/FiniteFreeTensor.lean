module

public import Mathlib

/-!
# Adic completion and tensor products with finite free modules

This file constructs the natural comparison from the tensor product of an adic
completion to the completion of a tensor product.  It is an isomorphism on the
underlying modules when the second tensor factor is finite free.

## Main definitions

* `adicCompletionTensorMap`: The natural `A`-linear map
  `AdicCompletion I M ⊗[A] N → AdicCompletion I (M ⊗[A] N)`.

## Main results

* `adicCompletionTensorMap_naturality`: The comparison map is natural in `M` and `N`.
* `adicCompletionTensorMap_bijective_of_finite_free`: The comparison map is bijective when `N`
  is finite free.
-/

noncomputable section

universe u v v' w w'

/-- The natural comparison from tensoring an adic completion to completing a
tensor product. -/
public def adicCompletionTensorMap
    {A : Type u} [CommRing A] (I : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N] :
    TensorProduct A (AdicCompletion I M) N →ₗ[A]
      AdicCompletion I (TensorProduct A M N) :=
  TensorProduct.lift
    (((LinearMap.restrictScalarsₗ A (AdicCompletion I A) _ _ A).comp
      ((AdicCompletion.map I).comp (TensorProduct.mk A M N).flip)).flip)

/-- `adicCompletionTensorMap` sends `x ⊗ₜ n` to the image of `x` under the map on adic
completions induced by `m ↦ m ⊗ₜ n`. -/
@[simp]
public theorem adicCompletionTensorMap_tmul
    {A : Type u} [CommRing A] (I : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N]
    (x : AdicCompletion I M) (n : N) :
    adicCompletionTensorMap I M N (TensorProduct.tmul A x n) =
      AdicCompletion.map I ((TensorProduct.mk A M N).flip n) x := by
  simp [adicCompletionTensorMap]

/-- Naturality of `adicCompletionTensorMap` in both module arguments. -/
public theorem adicCompletionTensorMap_naturality
    {A : Type u} [CommRing A] (I : Ideal A)
    {M : Type v} {M' : Type v'}
    [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    {N : Type w} {N' : Type w'}
    [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']
    (f : M →ₗ[A] M') (g : N →ₗ[A] N') :
    (AdicCompletion.map I (TensorProduct.map f g)).restrictScalars A ∘ₗ
        adicCompletionTensorMap I M N =
      adicCompletionTensorMap I M' N' ∘ₗ
        TensorProduct.map ((AdicCompletion.map I f).restrictScalars A) g := by
  apply TensorProduct.ext'
  intro x n
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul,
    adicCompletionTensorMap_tmul, LinearMap.restrictScalars_apply]
  rw [AdicCompletion.map_comp_apply, AdicCompletion.map_comp_apply]
  congr 2

private theorem adicCompletionTensorMap_bijective_of_pi
    {A : Type u} [CommRing A] (I : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M]
    (ι : Type w) [Finite ι] :
    Function.Bijective (adicCompletionTensorMap I M (ι → A)) := by
  classical
  have := Fintype.ofFinite ι
  let e := TensorProduct.piScalarRight A A M ι
  let e' := TensorProduct.piScalarRight A A (AdicCompletion I M) ι
  let c := (AdicCompletion.congr I e).restrictScalars A
  let p := (AdicCompletion.piEquivOfFintype I (fun _ : ι ↦ M)).restrictScalars A
  have heq : p.toLinearMap ∘ₗ c.toLinearMap ∘ₗ adicCompletionTensorMap I M (ι → A) =
      e'.toLinearMap := by
    apply TensorProduct.ext'
    intro x n
    funext j
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      adicCompletionTensorMap_tmul]
    simp only [p, c, LinearEquiv.restrictScalars_apply]
    rw [AdicCompletion.piEquivOfFintype_apply, AdicCompletion.congr_apply]
    show AdicCompletion.map I (LinearMap.proj j)
        (AdicCompletion.map I e.toLinearMap
          (AdicCompletion.map I ((TensorProduct.mk A M (ι → A)).flip n) x)) = _
    rw [AdicCompletion.map_comp_apply, AdicCompletion.map_comp_apply]
    have hm : (LinearMap.proj j).comp
        (e.toLinearMap.comp ((TensorProduct.mk A M (ι → A)).flip n)) =
        n j • (LinearMap.id : M →ₗ[A] M) := by
      ext m
      simp [e, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    rw [LinearMap.comp_assoc, hm, map_smul, AdicCompletion.map_id]
    simp [e', TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  have heq' : (p ∘ c) ∘ adicCompletionTensorMap I M (ι → A) = e' :=
    funext (DFunLike.congr_fun heq)
  apply ((p.bijective.comp c.bijective).of_comp_iff' _).mp
  rw [heq']
  exact e'.bijective

/-- The adic-completion tensor comparison is bijective when the second module
is finite free. -/
public theorem adicCompletionTensorMap_bijective_of_finite_free
    {A : Type u} [CommRing A] (I : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N]
    [Module.Finite A N] [Module.Free A N] :
    Function.Bijective (adicCompletionTensorMap I M N) := by
  classical
  let b := Module.Free.chooseBasis A N
  let e := b.equivFun
  let d := TensorProduct.congr (LinearEquiv.refl A (AdicCompletion I M)) e
  let c := (AdicCompletion.congr I
    (TensorProduct.congr (LinearEquiv.refl A M) e)).restrictScalars A
  have heq : c ∘ adicCompletionTensorMap I M N =
      adicCompletionTensorMap I M (Module.Free.ChooseBasisIndex A N → A) ∘ d := by
    funext x
    have h := DFunLike.congr_fun (adicCompletionTensorMap_naturality I
      (LinearMap.id : M →ₗ[A] M) e.toLinearMap) x
    simpa [c, d, AdicCompletion.congr_apply, TensorProduct.congr,
      LinearMap.restrictScalars_id] using h
  apply (c.bijective.of_comp_iff' _).mp
  rw [heq]
  exact (adicCompletionTensorMap_bijective_of_pi I M _).comp d.bijective
