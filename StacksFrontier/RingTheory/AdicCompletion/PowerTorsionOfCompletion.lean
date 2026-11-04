module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import StacksFrontier.RingTheory.AdicCompletion.TorsionBaseChangeDescent
public import StacksFrontier.RingTheory.Localization.Glueing.IdealPowerTorsion

/-!
# Power torsion elements of an adic completion come from the ring

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `Â` the `I`-adic completion. An element of `Â`
killed by `Iᵐ` is the image of an element of `A` killed by `Iᵐ`: the annihilator `K` of `Iᵐ` in
`A` is the kernel of `a ↦ (g a)_g` for generators `g` of `Iᵐ`, flatness of `Â` gives the kernel of
the same map on `Â` as `K ⊗ Â`, and `K ⟶ K ⊗ Â` is bijective because `K` is `I`-power torsion
and `A/Iⁿ ⟶ Â/IⁿÂ` is an isomorphism.

This is used in the injectivity half of the proof of Stacks 0GI5, to read a formal function
vanishing on the punctured part of `Spec Â` back as an element of the ring of a stage.

## Main results

* `AdicCompletion.exists_algebraMap_eq_of_pow_smul_eq_zero`.
-/

@[expose] public section

open TensorProduct

universe u

namespace AdicCompletion

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)

/-- **An element of the `I`-adic completion killed by `Iᵐ` comes from an element of the ring
killed by `Iᵐ`**, for `A` Noetherian. -/
theorem exists_algebraMap_eq_of_pow_smul_eq_zero {m : ℕ} {x : AdicCompletion I A}
    (hx : ∀ a ∈ I ^ m, a • x = 0) :
    ∃ t : A, (∀ a ∈ I ^ m, a * t = 0) ∧ algebraMap A (AdicCompletion I A) t = x := by
  classical
  obtain ⟨s, hs⟩ := (I ^ m).fg_of_isNoetherianRing
  let φ : A →ₗ[A] (s → A) := LinearMap.pi fun g => LinearMap.mulLeft A (g : A)
  let K := LinearMap.ker φ
  have hex : Function.Exact K.subtype φ := LinearMap.exact_subtype_ker_map φ
  have hex' := Module.Flat.rTensor_exact (AdicCompletion I A) hex
  have hgx : ∀ g : s, (g : A) • x = 0 := fun g => hx g (hs ▸ Ideal.subset_span g.2)
  have hφ1 : φ 1 = ∑ g : s, (g : A) • Pi.single g (1 : A) := by
    ext g'
    simp [φ, Finset.sum_apply, Pi.single_apply]
  have hzero : φ.rTensor (AdicCompletion I A) ((1 : A) ⊗ₜ x) = 0 := by
    rw [LinearMap.rTensor_tmul, hφ1, sum_tmul]
    refine Finset.sum_eq_zero fun g _ => ?_
    rw [smul_tmul, hgx g, tmul_zero]
  obtain ⟨y, hy⟩ := (hex' ((1 : A) ⊗ₜ x)).mp hzero
  -- `K` is power torsion, so the unit `K ⟶ K ⊗ Â` is onto
  have hK : IsIPowerTorsion A K I := fun k => ⟨m + 1, Nat.succ_pos m, fun a ha => by
    have hk : ∀ g : s, (g : A) * k = 0 := fun g => congrFun (LinearMap.mem_ker.mp k.2) g
    have hIm : I ^ (m + 1) ≤ I ^ m := Ideal.pow_le_pow_right (Nat.le_succ m)
    have hmem : ∀ b ∈ I ^ m, b * (k : A) = 0 := by
      intro b hb
      rw [← hs] at hb
      refine Submodule.span_induction (fun g hg => hk ⟨g, hg⟩) (zero_mul _)
        (fun b c _ _ hb hc => by rw [add_mul, hb, hc, add_zero])
        (fun r b _ hb => by rw [smul_eq_mul, mul_assoc, hb, mul_zero]) hb
    exact Subtype.ext (hmem a (hIm ha))⟩
  have hbij := ((IPowerTorsion.baseChange_bijective_iff_quotientMap_bijective.{u, u, u} A
    (AdicCompletion I A) I inferInstance).mpr
      (AdicCompletion.quotientMap_bijective I I.fg_of_isNoetherianRing)) K hK
  obtain ⟨k, rfl⟩ := hbij.2 y
  refine ⟨k, fun a ha => ?_, ?_⟩
  · have hk : ∀ g : s, (g : A) * k = 0 := fun g => congrFun (LinearMap.mem_ker.mp k.2) g
    rw [← hs] at ha
    refine Submodule.span_induction (fun g hg => hk ⟨g, hg⟩) (zero_mul _)
      (fun b c _ _ hb hc => by rw [add_mul, hb, hc]; simp)
      (fun r b _ hb => by rw [smul_eq_mul, mul_assoc, hb, mul_zero]) ha
  · have h2 := congrArg (TensorProduct.lid A (AdicCompletion I A)) hy
    simp only [TensorProduct.mk_apply, LinearMap.flip_apply, LinearMap.rTensor_tmul,
      Submodule.subtype_apply, TensorProduct.lid_tmul, one_smul] at h2
    rw [← h2, Algebra.algebraMap_eq_smul_one]

end AdicCompletion

end
