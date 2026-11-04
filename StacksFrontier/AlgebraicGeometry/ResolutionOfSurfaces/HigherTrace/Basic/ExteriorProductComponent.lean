module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Tactic.Abel
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.TraceMapPositive.Basic
public import StacksFrontier.RingTheory.Kaehler.Basic
public import StacksFrontier.RingTheory.Kaehler.JacobiZariski

/-!
# Bidegree components of the exterior algebra of a product

The component of the exterior algebra of a product `M × N` in bidegree `(i, j)`, as a map to the
tensor product of the exterior powers of `M` and `N`, together with its values on wedges.
-/

public noncomputable section

namespace KaehlerDifferential

open Polynomial
open scoped TensorProduct
open scoped KaehlerDifferential

variable {p t : ℕ} {Λ R S : Type*} [CommRing Λ] [CommRing R] [CommRing S]
  [Algebra Λ R] [Algebra Λ S] [Algebra R S] [IsScalarTower Λ R S]

universe u₁ u₂ u₃

/-- The component of the exterior algebra of a product in bidegree `(i, j)`, as a map from the `(i
+ j)`-st exterior power of the product to the tensor product of the two exterior powers. -/
noncomputable def exteriorProductComponent {K : Type u₁} {M : Type u₂}
    {N : Type u₃} [CommRing K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] (i j : ℕ) :
    (⋀[K]^(i + j) (M × N)) →ₗ[K] (⋀[K]^i M) ⊗[K] (⋀[K]^j N) := by
  let 𝒜 : ℕ → Submodule K (ExteriorAlgebra K M) :=
    fun k => ExteriorAlgebra.exteriorPower K k M
  let ℬ : ℕ → Submodule K (ExteriorAlgebra K N) :=
    fun k => ExteriorAlgebra.exteriorPower K k N
  let dM : DirectSum ℕ (fun k : ℕ => ↥(𝒜 k)) →ₗ[K] ↥(𝒜 i) :=
    DirectSum.component K ℕ (fun k : ℕ => ↥(𝒜 k)) i
  let dN : DirectSum ℕ (fun k : ℕ => ↥(ℬ k)) →ₗ[K] ↥(ℬ j) :=
    DirectSum.component K ℕ (fun k : ℕ => ↥(ℬ k)) j
  exact (TensorProduct.map dM dN).comp <|
    (GradedTensorProduct.auxEquiv K 𝒜 ℬ).toLinearMap.comp <|
        (ExteriorAlgebra.prodEquivTensor K M N).toLinearMap.comp
          (Submodule.subtype _)

/-- The bidegree component, unfolded to the maps it is built from. -/
private theorem exteriorProductComponent_apply_eq {K : Type u₁} {M : Type u₂}
    {N : Type u₃} [CommRing K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] (i j : ℕ)
    (x : ⋀[K]^(i + j) (M × N)) :
    exteriorProductComponent (K := K) (M := M) (N := N) i j x =
    (TensorProduct.map
      (DirectSum.component K ℕ (fun k : ℕ => ↥(⋀[K]^k M)) i)
      (DirectSum.component K ℕ (fun k : ℕ => ↥(⋀[K]^k N)) j))
      ((GradedTensorProduct.auxEquiv K (fun k : ℕ => ⋀[K]^k M)
        (fun k : ℕ => ⋀[K]^k N))
        ((ExteriorAlgebra.prodEquivTensor K M N) (x : ExteriorAlgebra K (M × N)))) := rfl

/-- The product equivalence sends a wedge of vectors of the two factors to the graded tensor of
the wedges. -/
private theorem prodEquivTensor_ιMulti_append {K : Type u₁} {M : Type u₂}
    {N : Type u₃} [CommRing K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] (i j : ℕ)
    (u : Fin i → M) (v : Fin j → N) :
    (ExteriorAlgebra.prodEquivTensor K M N)
      (ExteriorAlgebra.ιMulti K (i + j)
        (Fin.append (LinearMap.inl K M N ∘ u) (LinearMap.inr K M N ∘ v))) =
      (ExteriorAlgebra.ιMulti K i u) ᵍ⊗ₜ[K] (ExteriorAlgebra.ιMulti K j v) :=
  (ExteriorAlgebra.prodEquivTensor K M N).eq_symm_apply.mp
    (ExteriorAlgebra.prodEquivTensor_symm_apply_tmul_ιMulti K M N i j u v).symm

/-- The degree `i` component of the decomposition of a wedge of `i` vectors is that wedge. -/
private theorem component_decompose_ιMulti {K : Type u₁} {M : Type u₂} [CommRing K]
    [AddCommGroup M] [Module K M] (i : ℕ) (u : Fin i → M) :
    DirectSum.component K ℕ (fun k : ℕ => ↥(⋀[K]^k M)) i
      (DirectSum.decompose (fun k : ℕ => ⋀[K]^k M) (ExteriorAlgebra.ιMulti K i u)) =
    exteriorPower.ιMulti K i u :=
  (DirectSum.apply_eq_component K _ i).symm.trans <|
    Subtype.ext <| DirectSum.decompose_of_mem_same (fun k : ℕ => ⋀[K]^k M)
      (ExteriorAlgebra.ιMulti_range K i (Set.mem_range_self u))

/-- The bidegree component sends the wedge of `i` vectors from the first factor followed by `j`
vectors from the second to the corresponding tensor of wedges. -/
private theorem exteriorProductComponent_apply_append {K : Type u₁} {M : Type u₂}
    {N : Type u₃} [CommRing K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] (i j : ℕ)
    (u : Fin i → M) (v : Fin j → N) :
    exteriorProductComponent (K := K) (M := M) (N := N) i j
      (exteriorPower.ιMulti K (i + j)
        (Fin.append (LinearMap.inl K M N ∘ u) (LinearMap.inr K M N ∘ v))) =
    exteriorPower.ιMulti K i u ⊗ₜ[K] exteriorPower.ιMulti K j v := by
  rw [exteriorProductComponent_apply_eq]
  change (TensorProduct.map _ _) (GradedTensorProduct.auxEquiv K _ _
    ((ExteriorAlgebra.prodEquivTensor K M N) (ExteriorAlgebra.ιMulti K (i + j) _))) = _
  rw [prodEquivTensor_ιMulti_append, GradedTensorProduct.auxEquiv_tmul, TensorProduct.map_tmul,
    component_decompose_ιMulti, component_decompose_ιMulti]

/-- The value of the bidegree `(i, 1)` component on a wedge of vectors from the first factor with
one vector from the second appended. -/
theorem exteriorProductComponent_apply_snoc {K : Type u₁} {M : Type u₂}
    {N : Type u₃} [CommRing K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (i : ℕ) (u : Fin i → M) (v : N) :
    exteriorProductComponent (K := K) (M := M) (N := N) i 1
      (exteriorPower.ιMulti K (i + 1)
        (Fin.snoc (fun j => (u j, 0)) (0, v))) =
      exteriorPower.ιMulti K i u ⊗ₜ[K]
        exteriorPower.ιMulti K 1 (fun _ => v) := by
  have h : Fin.snoc (fun j : Fin i => (u j, (0 : N))) (0, v) =
      Fin.append (LinearMap.inl K M N ∘ u)
        (LinearMap.inr K M N ∘ fun _ : Fin 1 => v) := by
    rw [Fin.snoc_eq_append]
    congr 1
    funext j
    fin_cases j
    rfl
  rw [h]
  exact exteriorProductComponent_apply_append i 1 u (fun _ => v)

/-- The bidegree `(i, 1)` component annihilates a wedge of vectors all coming from the first
factor. -/
theorem exteriorProductComponent_apply_inl {K : Type u₁} {M : Type u₂}
    {N : Type u₃} [CommRing K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (i : ℕ) (u : Fin (i + 1) → M) :
    exteriorProductComponent (K := K) (M := M) (N := N) i 1
      (exteriorPower.ιMulti K (i + 1) (LinearMap.inl K M N ∘ u)) = 0 := by
  have hprod : (ExteriorAlgebra.prodEquivTensor K M N)
      (ExteriorAlgebra.ιMulti K (i + 1) (LinearMap.inl K M N ∘ u)) =
      (ExteriorAlgebra.ιMulti K (i + 1) u) ᵍ⊗ₜ[K]
        (ExteriorAlgebra.ιMulti K 0 (Fin.elim0 : Fin 0 → N)) := by
    have h := prodEquivTensor_ιMulti_append (K := K) (M := M) (N := N) (i + 1) 0 u Fin.elim0
    rwa [show LinearMap.inr K M N ∘ (Fin.elim0 : Fin 0 → N) = Fin.elim0 from funext fun j =>
      j.elim0, Fin.append_elim0] at h
  rw [exteriorProductComponent_apply_eq]
  change (TensorProduct.map _ _) (GradedTensorProduct.auxEquiv K _ _
    ((ExteriorAlgebra.prodEquivTensor K M N) (ExteriorAlgebra.ιMulti K (i + 1) _))) = 0
  rw [hprod, GradedTensorProduct.auxEquiv_tmul, TensorProduct.map_tmul]
  have hz : DirectSum.component K ℕ (fun k : ℕ => ↥(⋀[K]^k M)) i
      (DirectSum.decompose (fun k : ℕ => ⋀[K]^k M)
        (ExteriorAlgebra.ιMulti K (i + 1) u)) = 0 := by
    apply Subtype.ext
    change (DirectSum.decompose (fun k : ℕ => ⋀[K]^k M)
      (ExteriorAlgebra.ιMulti K (i + 1) u) i : ExteriorAlgebra K M) = 0
    exact DirectSum.decompose_of_mem_ne _
      (ExteriorAlgebra.ιMulti_range K (i + 1) (Set.mem_range_self u))
      (by omega)
  rw [hz]
  simp
end KaehlerDifferential

end
