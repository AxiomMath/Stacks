module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologyIdealPowerSystem
public import StacksFrontier.RingTheory.Filtration.IdealPowerSystemReesBound

/-!
# The cohomology of the `I`-adic filtration satisfies the laws of [Stacks, Tag 02OA] (1), (2)

`Stacks.Cohomology.FormalFunctions.cohomologyIdealPowerSystem` presents `n ↦ Hᵖ(X, Iⁿℱ)` as a
`Stacks.RingTheory.ReesSystem`. Parts (1) and (2) of [Stacks, Tag 02OA] at a general `n` need two
further laws, `Stacks.RingTheory.ReesSystem.IsTrMulCompatible`: the multiplication maps commute
with the transition maps, and multiplying by `a ∈ Iᵏ` and dropping back is the action of `a`.
Both hold for the cohomology system. The multiplication map
`Iᵏ ⊗_A Hᵖ(X, Iⁿℱ) → Hᵖ(X, Iᵏ⁺ⁿℱ)` of part (1) is a map out of the tensor product.

## Main results

* `Stacks.Cohomology.FormalFunctions.idealPowerMultipleMap_comp_idealPowerSmul`: the sheaf-level
  commutation of the inclusions along the filtration with the multiplication maps.
* `Stacks.Cohomology.FormalFunctions.cohomologyIdealPowerSystem_isTrMulCompatible`: the two laws
  for `n ↦ Hᵖ(X, Iⁿℱ)`.
* `Stacks.Cohomology.FormalFunctions.cohomologyMulTensor`: the multiplication map of part (1).

## References

* [Stacks Project, Tag 02OA](https://stacks.math.columbia.edu/tag/02OA)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower Stacks.Cohomology.AffineBase
open scoped ModuleCat.Algebra TensorProduct

universe u

namespace Stacks.Cohomology.FormalFunctions

attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra

variable {A : Type u} [CommRing A] (I : Ideal A) (X : Over (Spec (.of A)))
  (F : X.left.Modules)

/-- The inclusion along the filtration is multiplication by `1 ∈ I⁰`. -/
theorem idealPowerSmul_one {n m : ℕ} (h : m ≤ n) (hq : m ≤ 0 + n) (hone : (1 : A) ∈ I ^ 0) :
    idealPowerSmul I X F hq (1 : A) hone =
      idealPowerMultipleMap (baseIdealSheaf A I X.hom) F h :=
  cancel_sheafSubmodule_ι _ _ _
    (((idealPowerSmul_comp_ι I X F hq (1 : A) hone).trans
        ((congrArg (fun ψ : F ⟶ F ↦ (idealPowerSub I X F n).ι ≫ ψ)
            (one_smul A (𝟙 F))).trans (Category.comp_id _))).trans
      (idealPowerMultipleMap_comp_ι (baseIdealSheaf A I X.hom) F h).symm)

/-- Including along the filtration and then multiplying by `a ∈ Iᵏ` is multiplying by `a` out of
the larger member. -/
theorem idealPowerMultipleMap_comp_idealPowerSmul {k n m m' : ℕ} (h : m ≤ n) (hm : m' ≤ k + m)
    (hm' : m' ≤ k + n) (a : A) (ha : a ∈ I ^ k) :
    idealPowerMultipleMap (baseIdealSheaf A I X.hom) F h ≫ idealPowerSmul I X F hm a ha =
      idealPowerSmul I X F hm' a ha :=
  have hone : (1 : A) ∈ I ^ 0 := by simp
  have hq : m ≤ 0 + n := by omega
  have h2 : m' ≤ k + 0 + n := by omega
  (congrArg (fun ψ : idealPowerMod I X F n ⟶ idealPowerMod I X F m ↦
      ψ ≫ idealPowerSmul I X F hm a ha)
    (idealPowerSmul_one I X F h hq hone)).symm.trans
    ((idealPowerSmul_comp_idealPowerSmul I X F hq hm h2 a 1 ha hone).trans
      (idealPowerSmul_congr I X F h2 _ ha (mul_one a)))

variable (p : ℕ)

/-- Applying `Hᵖ(X, −)` successively to `f` and `g` is applying it to any `φ` equal to `f ≫ g`. -/
private theorem cohomologyFunctor_map_map_apply_of_comp_eq {M N P : X.left.Modules}
    {f : M ⟶ N} {g : N ⟶ P} {φ : M ⟶ P} (h : f ≫ g = φ) (x : (cohomologyFunctor X p).obj M) :
    ((cohomologyFunctor X p).map g).hom (((cohomologyFunctor X p).map f).hom x) =
      ((cohomologyFunctor X p).map φ).hom x :=
  (cohomologyFunctor_map_comp_apply X p f g x).trans
    (congrArg (fun ψ : M ⟶ P ↦ ((cohomologyFunctor X p).map ψ).hom x) h)

/-- The cohomology system `n ↦ Hᵖ(X, Iⁿℱ)` satisfies the two laws of
`Stacks.RingTheory.ReesSystem.IsTrMulCompatible`: the multiplication maps commute with the
transition maps, and multiplying by `a ∈ Iᵏ` and dropping back is the action of `a`. -/
theorem cohomologyIdealPowerSystem_isTrMulCompatible :
    (cohomologyIdealPowerSystem I X F p).IsTrMulCompatible where
  tr_mul k n m h a x :=
    (cohomologyFunctor_map_map_apply_of_comp_eq X p
        (idealPowerSmul_comp_idealPowerMultipleMap I X F (le_refl (k + n))
          (Nat.add_le_add_left h k) (Nat.add_le_add_left h k) (a : A) a.2) x).trans
      (cohomologyFunctor_map_map_apply_of_comp_eq X p
        (idealPowerMultipleMap_comp_idealPowerSmul I X F h (le_refl (k + m))
          (Nat.add_le_add_left h k) (a : A) a.2) x).symm
  tr_mul_self k n a x :=
    (cohomologyFunctor_map_map_apply_of_comp_eq X p
        ((idealPowerSmul_comp_idealPowerMultipleMap I X F (le_refl (k + n))
            (Nat.le_add_left n k) (Nat.le_add_left n k) (a : A) a.2).trans
          (idealPowerSmul_self I X F (Nat.le_add_left n k) (a : A) a.2)) x).trans
      (cohomologyFunctor_map_smul_id_apply X p (a : A) x)

/-- The multiplication map `Iᵏ ⊗_A Hᵖ(X, Iⁿℱ) → Hᵖ(X, I^(k+n)ℱ)` of [Stacks, Tag 02OA] part (1),
as a map out of the tensor product. -/
def cohomologyMulTensor (k n : ℕ) :
    (↥(I ^ k) ⊗[A] cohomologyIdealPower I X F p n) →ₗ[A]
      cohomologyIdealPower I X F p (k + n) :=
  TensorProduct.lift ((cohomologyMul I X F p k n).comp
    (Submodule.inclusion (le_of_eq (by rw [Ideal.map_id]) :
      I ^ k ≤ (I.map (RingHom.id A)) ^ k)))

/-- On a pure tensor `a ⊗ x`, `cohomologyMulTensor` is the multiplication `cohomologyMul` by `a`
applied to `x`. -/
@[simp]
theorem cohomologyMulTensor_tmul (k n : ℕ) (a : ↥(I ^ k))
    (x : cohomologyIdealPower I X F p n) :
    cohomologyMulTensor I X F p k n (a ⊗ₜ[A] x) =
      cohomologyMul I X F p k n ⟨(a : A), by rw [Ideal.map_id]; exact a.2⟩ x := rfl

end Stacks.Cohomology.FormalFunctions

end
