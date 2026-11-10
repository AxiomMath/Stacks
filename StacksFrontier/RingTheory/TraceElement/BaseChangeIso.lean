module

public import StacksFrontier.AlgebraicGeometry.Different.DualizingModulesQuasi.FlatAlgebraBaseChange
public import StacksFrontier.RingTheory.TraceElement.Transport

/-!
# Transporting a trivialization of the dualizing module along a base change

Let `A₀ → B₀` be a flat quasi-finite map with `A₀` Noetherian and a finite-open factorization
`F₀`, and suppose `ω_{B₀/A₀}` is free on a generator carrying `d₀` to the canonical element.
For an arbitrary `A₀`-algebra `A`, the relative dualizing module commutes with the base change
to `B = A ⊗_{A₀} B₀` (Tag 0BVF) and the canonical element is carried to the canonical element,
so the same holds over `A` for every finite-open factorization of `B` that is isomorphic to the
base change of `F₀`.

## Main results

* `Stacks.Discriminant.dualizingModule.exists_linearEquiv_traceCandidate_of_baseChange`: the
  statement above.
-/

@[expose] public section

open scoped TensorProduct

universe u w

namespace Stacks.Discriminant

namespace dualizingModule

/-- Let `A₀ → B₀` be flat with `A₀` Noetherian, `F₀` a finite-open factorization of `B₀`, and
`ε₀ : B₀ ≅ ω_{F₀}` an isomorphism carrying `d₀` to the canonical element. Let `A` be any
`A₀`-algebra, `σ : A ⊗_{A₀} B₀ ≅ B` and `F` a finite-open factorization of `B` whose intermediate
algebra is identified with `A ⊗_{A₀} F₀.middle` compatibly with the maps to `B`. Then there is an
isomorphism `B ≅ ω_F` carrying `σ(1 ⊗ d₀)` to the canonical element of `ω_F`. -/
theorem exists_linearEquiv_traceCandidate_of_baseChange
    {A₀ : Type u} [CommRing A₀] [IsNoetherianRing A₀] {B₀ : Type u} [CommRing B₀]
    [Algebra A₀ B₀] [Module.Flat A₀ B₀]
    (F₀ : FiniteOpenFactorization.{u, u, u} A₀ B₀) [Module.FinitePresentation A₀ F₀.middle]
    (d₀ : B₀) (ε₀ : B₀ ≃ₗ[B₀] dualizingModule F₀) (hε₀ : ε₀ d₀ = traceCandidate F₀)
    {A : Type u} [CommRing A] [Algebra A₀ A] {B : Type u} [CommRing B] [Algebra A B]
    [Module.Flat A B] (σ : A ⊗[A₀] B₀ ≃ₐ[A] B)
    (F : FiniteOpenFactorization.{u, u, w} A B) [Module.FinitePresentation A F.middle]
    (r : A ⊗[A₀] F₀.middle ≃ₐ[A] F.middle)
    (hr : ∀ x, algebraMap F.middle B (r x) =
      σ (algebraMap (FiniteOpenFactorization.baseChange F₀ A).middle (A ⊗[A₀] B₀) x)) :
    ∃ ε : B ≃ₗ[B] dualizingModule F, ε (σ (1 ⊗ₜ d₀)) = traceCandidate F := by
  let B₁ := A ⊗[A₀] B₀
  let F₁ := FiniteOpenFactorization.baseChange F₀ A
  let : Algebra B₀ B₁ := Algebra.TensorProduct.rightAlgebra
  let : Module B₀ (dualizingModule F₁) := Module.compHom _ (algebraMap B₀ B₁)
  let : IsScalarTower B₀ B₁ (dualizingModule F₁) := IsScalarTower.of_compHom B₀ B₁ _
  -- the base change of `ε₀`
  let e3 : B₁ ⊗[B₀] dualizingModule F₀ ≃ₗ[B₁] dualizingModule F₁ :=
    LinearEquiv.ofBijective _ (baseChangeLinearMap_bijective F₀ A)
  let e2 : B₁ ⊗[B₀] B₀ ≃ₗ[B₁] B₁ ⊗[B₀] dualizingModule F₀ :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B₁ B₁) ε₀
  let e1 : B₁ ⊗[B₀] B₀ ≃ₗ[B₁] B₁ := TensorProduct.AlgebraTensorModule.rid B₀ B₁ B₁
  let ε₁ : B₁ ≃ₗ[B₁] dualizingModule F₁ := e1.symm ≪≫ₗ e2 ≪≫ₗ e3
  have hε₁ : ε₁ (1 ⊗ₜ d₀) = traceCandidate F₁ := by
    have h1 : e1.symm ((1 : A) ⊗ₜ[A₀] d₀) = (1 : B₁) ⊗ₜ[B₀] d₀ := by
      rw [LinearEquiv.symm_apply_eq]
      symm
      rw [TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_one]
      rfl
    change e3 (e2 (e1.symm ((1 : A) ⊗ₜ[A₀] d₀))) = _
    rw [h1]
    change baseChangeLinearMap F₀ A ((1 : B₁) ⊗ₜ[B₀] ε₀ d₀) = _
    rw [hε₀, baseChangeLinearMap_one_tmul]
    exact baseChange_traceCandidate F₀ A
  -- transport along `σ`
  let : Algebra B B₁ := σ.symm.toAlgHom.toRingHom.toAlgebra
  have he : ∀ b : B, σ (algebraMap B B₁ b) = b := fun b ↦ σ.apply_symm_apply b
  let Fr := retargetFactorization F₁ σ
  let : Module B (dualizingModule F₁) := Module.compHom _ (algebraMap B B₁)
  let eR : dualizingModule F₁ ≃ₗ[B] dualizingModule Fr := dualizingModule_retargetEquiv F₁ σ he
  have heR : eR (traceCandidate F₁) = traceCandidate Fr := retargetEquiv_traceCandidate F₁ σ he
  -- change of the intermediate algebra
  have hr' : ∀ c, algebraMap Fr.middle B (r.symm c) = algebraMap F.middle B c := by
    intro c
    conv_rhs => rw [← r.apply_symm_apply c]
    rw [hr]
    rfl
  let eM : dualizingModule Fr ≃ₗ[B] dualizingModule F := middleEquiv F Fr r.symm hr'
  have heM : eM (traceCandidate Fr) = traceCandidate F := middleEquiv_traceCandidate F Fr r.symm hr'
  -- the semilinear piece `B ≅ B₁ ≅ ω_{F₁}`
  let eB : B ≃ₗ[B] dualizingModule F₁ :=
    { toFun := fun b ↦ ε₁ (σ.symm b)
      invFun := fun z ↦ σ (ε₁.symm z)
      map_add' := fun x y ↦ by simp
      map_smul' := fun b x ↦ by
        change ε₁ (σ.symm (b * x)) = σ.symm b • ε₁ (σ.symm x)
        rw [map_mul, ← smul_eq_mul, map_smul]
      left_inv := fun b ↦ by simp
      right_inv := fun z ↦ by simp }
  refine ⟨eB ≪≫ₗ eR ≪≫ₗ eM, ?_⟩
  change eM (eR (ε₁ (σ.symm (σ (1 ⊗ₜ d₀))))) = _
  rw [AlgEquiv.symm_apply_apply, hε₁, heR, heM]

end dualizingModule

end Stacks.Discriminant
