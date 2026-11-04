module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# A finite Galois extension splits itself

Let `K/k` be a finite Galois extension with group `G = K ≃ₐ[k] K`.  Then the `K`-algebra
`K ⊗[k] K` is the algebra `G → K` of `K`-valued functions on `G`: the coordinate indexed by
`σ` sends `x ⊗ y` to `x * σ y`.

## Main definitions

* `IsGalois.tensorEvalAlgHom` is the `K`-algebra map `K ⊗[k] K →ₐ[K] K` which is the identity
  on the left factor and `σ` on the right factor.
* `IsGalois.tensorProductPi` is the `K`-algebra map `K ⊗[k] K →ₐ[K] (G → K)` assembled from
  those coordinates.

## Main results

* `IsGalois.bijective_tensorProductPi` and `IsGalois.tensorProductEquivPi`: for a finite Galois
  extension the coordinate maps identify `K ⊗[k] K` with `G → K`.
* `IsGalois.evalRingHom_comp_tensorProductEquivPi`: the `σ`-th coordinate of the resulting
  isomorphism is `IsGalois.tensorEvalAlgHom σ`, as a map of rings.

## References

* [Stacks Project, Tag 0CDR](https://stacks.math.columbia.edu/tag/0CDR)
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u

namespace IsGalois

/-- The `K`-algebra map `K ⊗[k] K →ₐ[K] K` which is the identity on the left factor and the
`k`-algebra automorphism `σ` on the right factor. -/
def tensorEvalAlgHom {k K : Type u} [Field k] [Field K] [Algebra k K] (σ : K ≃ₐ[k] K) :
    K ⊗[k] K →ₐ[K] K :=
  Algebra.TensorProduct.lift (AlgHom.id K K) σ fun _ _ ↦ Commute.all _ _

/-- `IsGalois.tensorEvalAlgHom σ` sends `x ⊗ y` to `x * σ y`. -/
@[simp]
lemma tensorEvalAlgHom_tmul {k K : Type u} [Field k] [Field K] [Algebra k K]
    (σ : K ≃ₐ[k] K) (x y : K) : tensorEvalAlgHom σ (x ⊗ₜ[k] y) = x * σ y := by
  simp [tensorEvalAlgHom, Algebra.TensorProduct.lift_tmul]

/-- The `K`-algebra map from `K ⊗[k] K` to the functions on the automorphism group, whose
coordinate at `σ` is `IsGalois.tensorEvalAlgHom σ`. -/
def tensorProductPi (k K : Type u) [Field k] [Field K] [Algebra k K] :
    K ⊗[k] K →ₐ[K] ((K ≃ₐ[k] K) → K) :=
  AlgHom.pi fun σ ↦ tensorEvalAlgHom σ

/-- The `σ`-th coordinate of `IsGalois.tensorProductPi k K x` is
`IsGalois.tensorEvalAlgHom σ x`. -/
@[simp]
lemma tensorProductPi_apply (k K : Type u) [Field k] [Field K] [Algebra k K]
    (x : K ⊗[k] K) (σ : K ≃ₐ[k] K) : tensorProductPi k K x σ = tensorEvalAlgHom σ x := rfl

/-- For a finite Galois extension `K/k` the coordinate maps identify `K ⊗[k] K` with the
functions on the Galois group: `IsGalois.tensorProductPi k K` is bijective. -/
theorem bijective_tensorProductPi (k K : Type u) [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] :
    Function.Bijective (tensorProductPi k K) := by
  classical
  let M := K ⊗[k] K
  let G := K ≃ₐ[k] K
  have hEval : Function.Injective (tensorEvalAlgHom (k := k) (K := K)) := by
    intro σ τ h
    refine AlgEquiv.ext fun x ↦ ?_
    simpa using DFunLike.congr_fun h (1 ⊗ₜ[k] x)
  let F : G → M →ₗ[K] K := fun σ ↦ (tensorEvalAlgHom σ).toLinearMap
  have hli : LinearIndependent K F :=
    (linearIndependent_algHom_toLinearMap K M K).comp (tensorEvalAlgHom (k := k) (K := K)) hEval
  have hcard : Fintype.card G = Module.finrank K M := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
    simp [M]
  have hspan : Submodule.span K (Set.range F) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hli, hcard, Module.finrank_linearMap_self]
  have hInjective : Function.Injective (tensorProductPi k K) := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply (Module.forall_dual_apply_eq_zero_iff K (x - y)).mp
    intro φ
    have hzero : tensorProductPi k K (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hle : Submodule.span K (Set.range F) ≤
        LinearMap.ker (LinearMap.applyₗ (R := K) (x - y)) :=
      Submodule.span_le.mpr (by rintro _ ⟨σ, rfl⟩; simpa [F] using congrFun hzero σ)
    exact hle (hspan ▸ Submodule.mem_top)
  have hRange : (tensorProductPi k K).toLinearMap.range = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [LinearMap.finrank_range_of_inj hInjective, ← hcard, Module.finrank_fintype_fun_eq_card]
  exact ⟨hInjective, LinearMap.range_eq_top.mp hRange⟩

/-- **A finite Galois extension splits itself**: the coordinates `x ⊗ y ↦ x * σ y` identify
`K ⊗[k] K`, as a `K`-algebra, with the algebra of `K`-valued functions on the Galois group. -/
def tensorProductEquivPi (k K : Type u) [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] : K ⊗[k] K ≃ₐ[K] ((K ≃ₐ[k] K) → K) :=
  AlgEquiv.ofBijective (tensorProductPi k K) (bijective_tensorProductPi k K)

/-- The `σ`-th coordinate of `IsGalois.tensorProductEquivPi k K x` is
`IsGalois.tensorEvalAlgHom σ x`. -/
@[simp]
lemma tensorProductEquivPi_apply (k K : Type u) [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] (x : K ⊗[k] K) (σ : K ≃ₐ[k] K) :
    tensorProductEquivPi k K x σ = tensorEvalAlgHom σ x := rfl

/-- The `σ`-th coordinate of the splitting isomorphism is `IsGalois.tensorEvalAlgHom σ`, read
as a map of rings. -/
lemma evalRingHom_comp_tensorProductEquivPi (k K : Type u) [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] (σ : K ≃ₐ[k] K) :
    (Pi.evalRingHom (fun _ : K ≃ₐ[k] K ↦ K) σ).comp
        (tensorProductEquivPi k K).toRingEquiv.toRingHom =
      (tensorEvalAlgHom σ).toRingHom := by
  ext x
  · simp [RingHom.comp_apply]
  · show (tensorProductEquivPi k K) (Algebra.TensorProduct.includeRight.toRingHom x) σ =
      tensorEvalAlgHom σ (Algebra.TensorProduct.includeRight.toRingHom x)
    exact tensorProductEquivPi_apply k K _ _

end IsGalois

end

end
