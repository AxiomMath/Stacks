module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.BaseFieldExtension.Data

/-!
# The coproduct axiom descends along a field extension

Given a comparison `Φ` between first Chern class data `𝔇` over `k` with coefficients in `F` and
`𝔇'` over `k'` with coefficients in `F'`, identifying `F' ⊗_F H^*(X)` with `H'^*(X_{k'})`, if
`H'^*` is compatible with finite coproducts then so is `H^*`.

## Main results

* `Stacks.WeilCohomology.FieldExtensionComparison.coproductAxiom`: axiom (A1) for `𝔇'`
  implies axiom (A1) for `𝔇`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Function

universe u w w'

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

section LinearAlgebra

variable {F : Type*} [Field F] (F' : Type*) [Field F'] [Algebra F F']
  {V : Type*} [AddCommGroup V] [Module F V] {W : Type*} [AddCommGroup W] [Module F W]

/-- `v ↦ 1 ⊗ v`, `V → F' ⊗_F V`, is injective. -/
theorem injective_one_tmul : Injective fun v : V => (1 : F') ⊗ₜ[F] v := by
  have h : Injective ((Algebra.linearMap F F').rTensor V) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (algebraMap F F').injective
  intro v w hvw
  apply (TensorProduct.lid F V).symm.injective
  apply h
  simpa using hvw

/-- An `F`-linear map is bijective once its extension of scalars to `F'` is. -/
theorem bijective_of_bijective_baseChange (f : V →ₗ[F] W)
    (h : Bijective (f.baseChange F')) : Bijective f := by
  rw [LinearMap.baseChange_eq_ltensor] at h
  exact (Module.FaithfullyFlat.lTensor_bijective_iff_bijective F F' f).mp h

/-- An `F`-linear map is injective once its extension of scalars to `F'` is. -/
theorem injective_of_injective_baseChange (f : V →ₗ[F] W)
    (h : Injective (f.baseChange F')) : Injective f := by
  rw [LinearMap.baseChange_eq_ltensor] at h
  exact (Module.FaithfullyFlat.lTensor_injective_iff_injective F F' f).mp h

end LinearAlgebra

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
  {F : Type w} [Field F] {F' : Type w'} [Field F'] [Algebra F F']
  {𝔇 : FirstChernClassData k F} {𝔇' : FirstChernClassData k' F'}

namespace FieldExtensionComparison

variable (Φ : FieldExtensionComparison 𝔇 𝔇')

/-- The comparison isomorphism is `F'`-linear on pure tensors: it sends `a ⊗ v` to `a` times
the image of `1 ⊗ v`. -/
theorem iso_tmul (X : (SmoothProjectiveScheme k).FullSubcategory) (a : F') (v : 𝔇.H X) :
    Φ.iso X (a ⊗ₜ v) = a • Φ.iso X (1 ⊗ₜ v) := by
  rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The comparison isomorphisms intertwine `f^*` extended to `F'` with `(f_{k'})^*`. -/
theorem iso_comp_baseChange_pull {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) :
    (Φ.iso X).toLinearMap ∘ₗ (𝔇.pull f).toLinearMap.baseChange F' =
      (𝔇'.pull ((baseChange k k').map f)).toLinearMap ∘ₗ (Φ.iso Y).toLinearMap := by
  refine LinearMap.ext fun x => x.induction_on (by simp) (fun a v => ?_) (fun x y hx hy => ?_)
  · simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.baseChange_tmul,
      AlgHom.toLinearMap_apply, AlgEquiv.toLinearMap_apply]
    rw [iso_tmul Φ X a, iso_tmul Φ Y a, map_smul, Φ.iso_natural]
  · simp only [LinearMap.coe_comp, Function.comp_apply, map_add] at hx hy ⊢
    rw [hx, hy]

include Φ in
/-- **Axiom (A1) descends**: if `(H')^*` is compatible with finite coproducts, so is `H^*`. -/
theorem coproductAxiom (h : 𝔇'.CoproductAxiom) : 𝔇.CoproductAxiom := by
  refine ⟨fun X hX => ?_, fun X Y Z i j hc => ?_⟩
  · have := h.1 _ (isEmpty_baseChange (k' := k') hX)
    have : Subsingleton (F' ⊗[F] 𝔇.H X) := (Φ.iso X).toEquiv.subsingleton
    exact (injective_one_tmul (F := F) (V := 𝔇.H X) F').subsingleton
  · let g : 𝔇.H Z →ₗ[F] 𝔇.H X × 𝔇.H Y :=
      (𝔇.pull i).toLinearMap.prod (𝔇.pull j).toLinearMap
    let e : F' ⊗[F] (𝔇.H X × 𝔇.H Y) ≃ₗ[F']
        𝔇'.H ((baseChange k k').obj X) × 𝔇'.H ((baseChange k k').obj Y) :=
      (TensorProduct.prodRight F F' F' (𝔇.H X) (𝔇.H Y)).trans
        ((Φ.iso X).toLinearEquiv.prodCongr (Φ.iso Y).toLinearEquiv)
    have hpr : ∀ x : F' ⊗[F] 𝔇.H Z, TensorProduct.prodRight F F' F' (𝔇.H X) (𝔇.H Y)
        (g.baseChange F' x) = ((𝔇.pull i).toLinearMap.baseChange F' x,
          (𝔇.pull j).toLinearMap.baseChange F' x) := fun x =>
      x.induction_on (by simp only [map_zero]; rfl) (fun a v => by simp [g])
        (fun x y hx hy => by simp only [map_add, hx, hy]; rfl)
    have hg : e.toLinearMap ∘ₗ g.baseChange F' =
        ((𝔇'.pull ((baseChange k k').map i)).toLinearMap.prod
          (𝔇'.pull ((baseChange k k').map j)).toLinearMap) ∘ₗ (Φ.iso Z).toLinearMap := by
      refine LinearMap.ext fun x => ?_
      have h1 := LinearMap.congr_fun (Φ.iso_comp_baseChange_pull i) x
      have h2 := LinearMap.congr_fun (Φ.iso_comp_baseChange_pull j) x
      simp only [LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply] at h1 h2
      simp only [LinearMap.coe_comp, Function.comp_apply, e, LinearEquiv.coe_coe,
        LinearEquiv.trans_apply, hpr, LinearEquiv.prodCongr_apply, AlgEquiv.toLinearEquiv_apply,
        LinearMap.prod_apply, h1, h2]
      rfl
    have hb : Bijective (e.toLinearMap ∘ₗ g.baseChange F') := by
      rw [hg]
      exact (h.2 _ _ _ _ _ (nonempty_isColimit_baseChange i j hc)).comp (Φ.iso Z).bijective
    have : Bijective (g.baseChange F') := by
      have := e.symm.bijective.comp hb
      simpa [Function.comp_def] using this
    exact bijective_of_bijective_baseChange F' g this

end FieldExtensionComparison

end Stacks.WeilCohomology
