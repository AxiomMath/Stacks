module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LatticeReductionConstituents
public import Mathlib.Algebra.Module.ULift

/-!
# Constituents through a universe lift

`Stacks.EtaleCohomology.HasConstituentsIn A 𝓜 M` compares `M` with a family `𝓜` in the same
universe. Lifting both along `ULift` keeps the constituents
(`Stacks.EtaleCohomology.HasConstituentsIn.ulift`): a simple subquotient of `ULift M` is a simple
subquotient of `M`, up to a linear equivalence.

## Main results

* `Stacks.EtaleCohomology.HasConstituentsIn.ulift`.
-/

@[expose] public noncomputable section

universe v w

namespace Stacks.EtaleCohomology

variable {A : Type*} [Ring A] {ι : Type*} {𝓜 : ι → Type v} [∀ i, AddCommGroup (𝓜 i)]
  [∀ i, Module A (𝓜 i)] {M : Type v} [AddCommGroup M] [Module A M]

/-- **Constituents survive the universe lift.** If every simple subquotient of `M` is a retract of
some `𝓜 i`, then every simple subquotient of `ULift M` is a retract of some `ULift (𝓜 i)`. -/
theorem HasConstituentsIn.ulift (h : HasConstituentsIn A 𝓜 M) :
    HasConstituentsIn A (fun i => ULift.{w} (𝓜 i)) (ULift.{w} M) := by
  intro W S _ _ q hq hS
  let e : ULift.{w} M ≃ₗ[A] M := ULift.moduleEquiv
  let W' : Submodule A M := W.map (e : ULift.{w} M →ₗ[A] M)
  let eW : W ≃ₗ[A] W' := Submodule.equivMapOfInjective _ e.injective W
  let q' : W' →ₗ[A] S := q ∘ₗ eW.symm.toLinearMap
  have hq' : Function.Surjective q' := hq.comp eW.symm.surjective
  let eS : (W' ⧸ LinearMap.ker q') ≃ₗ[A] S := q'.quotKerEquivOfSurjective hq'
  have : IsSimpleModule A (W' ⧸ LinearMap.ker q') := IsSimpleModule.congr eS
  obtain ⟨i, f, g, hgf⟩ := h W' (W' ⧸ LinearMap.ker q') (LinearMap.ker q').mkQ
    (Submodule.mkQ_surjective _) inferInstance
  let ei : ULift.{w} (𝓜 i) ≃ₗ[A] 𝓜 i := ULift.moduleEquiv
  refine ⟨i, ei.symm.toLinearMap ∘ₗ f ∘ₗ eS.symm.toLinearMap,
    eS.toLinearMap ∘ₗ g ∘ₗ ei.toLinearMap, ?_⟩
  ext s
  have := LinearMap.congr_fun hgf (eS.symm s)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, LinearMap.id_coe, id_eq] at this ⊢
  rw [this, LinearEquiv.apply_symm_apply]

end Stacks.EtaleCohomology

end
