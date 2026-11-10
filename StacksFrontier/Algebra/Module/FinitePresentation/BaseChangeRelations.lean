module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Generators and relations of a finite presentation after base change

Let `A → B` be a map of commutative rings, let `f : Aⁿ → M` be a surjection with relations
`g : Aᵐ → Aⁿ` (so that `Aᵐ → Aⁿ → M → 0` is exact), and let `ρ : M → N` be an `A`-linear map
into a `B`-module which exhibits `N` as `B ⊗_A M`. Then the images of the generators generate
`N` over `B`, and every relation among them is a `B`-combination of the images of the relations
`g(eⱼ)`: tensor product is right exact.

## Main results

* `Module.exists_sum_eq_of_bijective_liftBaseChange`: the base-changed generators generate.
* `Module.exists_coeffs_of_bijective_liftBaseChange`: the base-changed relations generate the
  relations.
-/

@[expose] public noncomputable section

open TensorProduct

namespace Module

variable {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
  {n m : ℕ} (f : (Fin n → A) →ₗ[A] M) (g : (Fin m → A) →ₗ[A] (Fin n → A))
  (hf : Function.Surjective f) (hfg : Function.Exact g f)
  (ρ : M →ₗ[A] N) (hρ : Function.Bijective (ρ.liftBaseChange B))

/-- The base-changed map `B ⊗ Aⁿ → N` sends `w` to the combination of the images of the
generators with the coordinates of `w` as coefficients. -/
private theorem liftBaseChange_baseChange_eq_sum (w : B ⊗[A] (Fin n → A)) :
    ρ.liftBaseChange B (f.baseChange B w) =
      ∑ i, TensorProduct.piScalarRight A B B (Fin n) w i • ρ (f (Pi.single i 1)) := by
  induction w using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, Pi.add_apply, add_smul, Finset.sum_add_distrib, ha, hb]
  | tmul b a =>
    rw [LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul]
    change b • ρ (f a) = ∑ i, (TensorProduct.piScalarRightHom A B B (Fin n) (b ⊗ₜ a)) i • _
    rw [TensorProduct.piScalarRightHom_tmul]
    conv_lhs => rw [show a = ∑ i, a i • Pi.single i (1 : A) by ext j; simp [Pi.single_apply]]
    simp only [map_sum, map_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm, ← smul_assoc]

include hf hρ in
/-- **Generators of a module stay generators after a base change.** -/
theorem exists_sum_eq_of_bijective_liftBaseChange (x : N) :
    ∃ b : Fin n → B, ∑ i, b i • ρ (f (Pi.single i 1)) = x := by
  obtain ⟨w, rfl⟩ := hρ.2 x
  obtain ⟨w', rfl⟩ := LinearMap.lTensor_surjective B hf w
  exact ⟨_, (liftBaseChange_baseChange_eq_sum f ρ w').symm⟩

include hf hfg hρ in
/-- Relations among generators after a base change are combinations of the base-changed
relations. -/
theorem exists_coeffs_of_bijective_liftBaseChange (b : Fin n → B)
    (hb : ∑ i, b i • ρ (f (Pi.single i 1)) = 0) :
    ∃ c : Fin m → B, ∀ i, b i = ∑ j, c j * algebraMap A B (g (Pi.single j 1) i) := by
  let e := TensorProduct.piScalarRight A B B (Fin n)
  let e' := TensorProduct.piScalarRight A B B (Fin m)
  have hex : Function.Exact (g.baseChange B) (f.baseChange B) := lTensor_exact B hfg hf
  have hg : ∀ z, e (g.baseChange B z) =
      fun i => ∑ j, e' z j * algebraMap A B (g (Pi.single j 1) i) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add a b ha hb =>
      ext i
      simp only [map_add, Pi.add_apply, ha, hb, add_mul, Finset.sum_add_distrib]
    | tmul b c =>
      ext i
      rw [LinearMap.baseChange_tmul]
      change (TensorProduct.piScalarRightHom A B B (Fin n) (b ⊗ₜ g c)) i =
        ∑ j, (TensorProduct.piScalarRightHom A B B (Fin m) (b ⊗ₜ c)) j * _
      rw [TensorProduct.piScalarRightHom_tmul, TensorProduct.piScalarRightHom_tmul]
      conv_lhs => rw [show c = ∑ j, c j • Pi.single j (1 : A) by ext k; simp [Pi.single_apply]]
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      ring
  have h0 : f.baseChange B (e.symm b) = 0 := by
    apply hρ.1
    rw [map_zero, liftBaseChange_baseChange_eq_sum, LinearEquiv.apply_symm_apply, hb]
  obtain ⟨z, hz⟩ := (hex (e.symm b)).1 h0
  refine ⟨e' z, fun i => ?_⟩
  have := congrFun (hg z) i
  rwa [hz, LinearEquiv.apply_symm_apply] at this

end Module

end
