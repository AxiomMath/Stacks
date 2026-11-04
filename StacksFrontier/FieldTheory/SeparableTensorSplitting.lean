module

public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.FieldTheory.SeparableDegree
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# A normal extension splits every separable subextension

Let `k'/k` be a finite separable extension and let `K/k` be a normal extension into which `k'`
embeds. Then the `K`-algebra `K ⊗[k] k'` is the algebra `(k' →ₐ[k] K) → K` of `K`-valued
functions on the set of `k`-embeddings of `k'` into `K`: the coordinate indexed by `σ` sends
`x ⊗ y` to `x * σ y`. On spectra this is the decomposition

`Spec(k') × Spec(K) = ∐_{σ : k' →ₐ[k] K} Spec(K)`

whose `σ`-th coprojection is `(Spec(σ), id)`.

## Main definitions

* `Stacks.FieldTheory.tensorEvalAlgHom`: the `K`-algebra map `K ⊗[k] k' →ₐ[K] K` which is the
  identity on the left factor and `σ` on the right factor.
* `Stacks.FieldTheory.tensorPi`: the `K`-algebra map `K ⊗[k] k' →ₐ[K] ((k' →ₐ[k] K) → K)`
  assembled from those coordinates.
* `Stacks.FieldTheory.tensorPiEquiv`: the resulting isomorphism, and
  `Stacks.FieldTheory.tensorPiEquiv'` its `k`-linear form on `k' ⊗[k] K`.

## Main results

* `Stacks.FieldTheory.natCard_algHom_eq_finrank`: there are exactly `[k' : k]` embeddings of
  `k'` into `K` over `k`.
* `Stacks.FieldTheory.bijective_tensorPi`: the coordinate maps identify `K ⊗[k] k'` with
  `(k' →ₐ[k] K) → K`.

## Implementation notes

The hypothesis that `k'` embeds into `K` is carried as an `AlgHom` `ι : k' →ₐ[k] K`, not as an
algebra instance.

## References

* [Stacks Project, Tag 0FVS](https://stacks.math.columbia.edu/tag/0FVS)
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u

namespace Stacks.FieldTheory

variable (k k' K : Type u) [Field k] [Field k'] [Field K] [Algebra k k'] [Algebra k K]

/-- For `k'/k` finite separable and `K/k` normal with an embedding `ι : k' →ₐ[k] K`, there are
exactly `[k' : k]` embeddings of `k'` into `K` over `k`. -/
theorem natCard_algHom_eq_finrank [FiniteDimensional k k'] [Algebra.IsSeparable k k']
    [Normal k K] (ι : k' →ₐ[k] K) :
    Nat.card (k' →ₐ[k] K) = Module.finrank k k' := by
  have hsplits : ∀ s ∈ (Set.univ : Set k'),
      IsIntegral k s ∧ ((minpoly k s).map (algebraMap k K)).Splits := by
    intro s _
    exact ⟨Algebra.IsIntegral.isIntegral s,
      minpoly.algHom_eq ι ι.injective s ▸ Normal.splits ‹Normal k K› (ι s)⟩
  rw [← Field.finSepDegree_eq_of_adjoin_splits k k' K
      (IntermediateField.adjoin_univ k k') hsplits,
    Field.finSepDegree_eq_finrank_of_isSeparable]

/-- The `K`-algebra map `K ⊗[k] k' →ₐ[K] K` which is the identity on the left factor and the
`k`-embedding `σ` on the right factor. -/
def tensorEvalAlgHom {k k' K : Type u} [Field k] [Field k'] [Field K] [Algebra k k']
    [Algebra k K] (σ : k' →ₐ[k] K) : K ⊗[k] k' →ₐ[K] K :=
  Algebra.TensorProduct.lift (AlgHom.id K K) σ fun _ _ ↦ Commute.all _ _

/-- `Stacks.FieldTheory.tensorEvalAlgHom σ` sends `x ⊗ y` to `x * σ y`. -/
@[simp]
lemma tensorEvalAlgHom_tmul {k k' K : Type u} [Field k] [Field k'] [Field K] [Algebra k k']
    [Algebra k K] (σ : k' →ₐ[k] K) (x : K) (y : k') :
    tensorEvalAlgHom σ (x ⊗ₜ[k] y) = x * σ y := by
  simp [tensorEvalAlgHom, Algebra.TensorProduct.lift_tmul]

/-- The `K`-algebra map from `K ⊗[k] k'` to the functions on the set of `k`-embeddings of `k'`
into `K`, whose coordinate at `σ` is `Stacks.FieldTheory.tensorEvalAlgHom σ`. -/
def tensorPi : K ⊗[k] k' →ₐ[K] ((k' →ₐ[k] K) → K) :=
  AlgHom.pi fun σ ↦ tensorEvalAlgHom σ

/-- The coordinate of `Stacks.FieldTheory.tensorPi` at `σ` is
`Stacks.FieldTheory.tensorEvalAlgHom σ`. -/
@[simp]
lemma tensorPi_apply (x : K ⊗[k] k') (σ : k' →ₐ[k] K) :
    tensorPi k k' K x σ = tensorEvalAlgHom σ x := rfl

/-- **A normal extension splits a separable subextension.** The coordinates `x ⊗ y ↦ x * σ y`
identify `K ⊗[k] k'` with the `K`-valued functions on the set of `k`-embeddings `σ : k' → K`. -/
theorem bijective_tensorPi [FiniteDimensional k k'] [Algebra.IsSeparable k k'] [Normal k K]
    (ι : k' →ₐ[k] K) : Function.Bijective (tensorPi k k' K) := by
  classical
  have : Fintype (k' →ₐ[k] K) := minpoly.AlgHom.fintype k k' K
  let M := K ⊗[k] k'
  let G := k' →ₐ[k] K
  let f : G → (M →ₗ[K] K) := fun σ ↦ (tensorEvalAlgHom σ).toLinearMap
  have hEval : Function.Injective (tensorEvalAlgHom (k := k) (k' := k') (K := K)) :=
    fun σ τ h ↦ AlgHom.ext fun x ↦ by simpa using DFunLike.congr_fun h (1 ⊗ₜ[k] x)
  have hli : LinearIndependent K f :=
    (linearIndependent_algHom_toLinearMap K M K).comp _ hEval
  have hcard : Fintype.card G = Module.finrank K M := by
    calc Fintype.card G = Nat.card G := by simp
      _ = Module.finrank k k' := natCard_algHom_eq_finrank k k' K ι
      _ = Module.finrank K M := (Module.finrank_baseChange (R := K) (S := k) (M' := k')).symm
  have hspan : Submodule.span K (Set.range f) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    calc Module.finrank K (Submodule.span K (Set.range f)) = Fintype.card G :=
        finrank_span_eq_card hli
      _ = Module.finrank K M := hcard
      _ = Module.finrank K (M →ₗ[K] K) := (Module.finrank_linearMap_self K K M).symm
  have hInjective : Function.Injective (tensorPi k k' K) := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply (Module.forall_dual_apply_eq_zero_iff K (x - y)).mp
    intro φ
    refine Submodule.span_induction (s := Set.range f) (M := M →ₗ[K] K) ?_ ?_ ?_ ?_
      (hspan ▸ Submodule.mem_top : φ ∈ Submodule.span K (Set.range f))
    · rintro ψ ⟨σ, rfl⟩
      have hzero : tensorPi k k' K (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      simpa [f] using congrFun hzero σ
    · simp
    · intro f g _ _ hf0 hg0; simp [hf0, hg0]
    · intro a f _ hf0; simp [hf0]
  have hRange : (tensorPi k k' K).toLinearMap.range = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    calc Module.finrank K ((tensorPi k k' K).toLinearMap.range) = Module.finrank K M :=
        LinearMap.finrank_range_of_inj hInjective
      _ = Fintype.card G := hcard.symm
      _ = Module.finrank K (G → K) := by simp
  exact ⟨hInjective, LinearMap.range_eq_top.mp hRange⟩

/-- The splitting isomorphism `K ⊗[k] k' ≅ ∏_{σ : k' →ₐ[k] K} K` of
`Stacks.FieldTheory.bijective_tensorPi`, as a `K`-algebra isomorphism. -/
def tensorPiEquiv [FiniteDimensional k k'] [Algebra.IsSeparable k k'] [Normal k K]
    (ι : k' →ₐ[k] K) : K ⊗[k] k' ≃ₐ[K] ((k' →ₐ[k] K) → K) :=
  AlgEquiv.ofBijective (tensorPi k k' K) (bijective_tensorPi k k' K ι)

/-- `Spec(k') × Spec(K) = ∐_{σ : k' →ₐ[k] K} Spec(K)`: the `k`-algebra isomorphism
`k' ⊗[k] K ≅ ∏_{σ : k' →ₐ[k] K} K` sending `η ⊗ ζ` to `(σ(η) · ζ)_σ`. -/
def tensorPiEquiv' [FiniteDimensional k k'] [Algebra.IsSeparable k k'] [Normal k K]
    (ι : k' →ₐ[k] K) : k' ⊗[k] K ≃ₐ[k] ((k' →ₐ[k] K) → K) :=
  (Algebra.TensorProduct.comm k k' K).trans ((tensorPiEquiv k k' K ι).restrictScalars k)

/-- `Stacks.FieldTheory.tensorPiEquiv'` sends `η ⊗ ζ` to the function `σ ↦ σ η * ζ`. -/
@[simp]
lemma tensorPiEquiv'_tmul [FiniteDimensional k k'] [Algebra.IsSeparable k k'] [Normal k K]
    (ι : k' →ₐ[k] K) (η : k') (ζ : K) (σ : k' →ₐ[k] K) :
    tensorPiEquiv' k k' K ι (η ⊗ₜ[k] ζ) σ = σ η * ζ := by
  simp [tensorPiEquiv', tensorPiEquiv, tensorPi, mul_comm]

end Stacks.FieldTheory

end

end
