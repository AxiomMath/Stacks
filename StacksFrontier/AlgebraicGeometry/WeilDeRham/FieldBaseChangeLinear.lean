module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.FieldBaseChangeData

/-!
# Linear algebra along a field extension, for Lemma 0FVT

The proof of Lemma 0FVT of the Stacks Project transfers each axiom from the data over `k'`, `F'`
to the data over `k`, `F` by the linear algebra principle stated in its paragraph on (A1): if
`φ : V → W` is an `F`-linear map of `F`-vector spaces, then `φ` is an isomorphism if and only if
`φ_{F'} : V ⊗_F F' → W ⊗_F F'` is (and likewise for injectivity and surjectivity, as in its
paragraphs on (A2) and (A7)). The maps arising there are not literally `φ_{F'}`: they are maps
`ψ : V' → W'` which the comparison isomorphisms `F' ⊗_F V ≅ V'`, `F' ⊗_F W ≅ W'` identify with
`φ_{F'}`. This file records the principle in that form.

## Main results

* `Stacks.WeilDeRham.exists_contract_eq_of_baseChange`: the principle of the paragraph (A6): if
  `(1 ⊗ λ')ξ' = v'` for an `F'`-linear `λ'`, then `(1 ⊗ λ)ξ = v` for an `F`-linear `λ`.

## References

* [Stacks Project, Tag 0FVT](https://stacks.math.columbia.edu/tag/0FVT)
-/

@[expose] public noncomputable section

open TensorProduct

namespace Stacks.WeilDeRham

variable {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']
  {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
  {V' W' : Type*} [AddCommGroup V'] [Module F' V'] [AddCommGroup W'] [Module F' W']

/-- The contraction `(1 ⊗ λ')ξ'` of the image `ξ' ∈ (F' ⊗_F V) ⊗_{F'} (F' ⊗_F W)` of
`ξ ∈ V ⊗_F W` against an `F'`-linear form `λ'` on `F' ⊗_F W`, as a function of `ξ`:
`x ⊗ w ↦ λ'(1 ⊗ w) · (1 ⊗ x)`. -/
def baseChangeContract (l' : F' ⊗[F] W →ₗ[F'] F') : V ⊗[F] W →ₗ[F] F' ⊗[F] V :=
  TensorProduct.lift (LinearMap.mk₂ F (fun x w => l' (1 ⊗ₜ w) • ((1 : F') ⊗ₜ[F] x))
    (fun x x' w => by simp [TensorProduct.tmul_add, smul_add])
    (fun c x w => by
      rw [TensorProduct.tmul_smul, smul_comm])
    (fun x w w' => by simp [TensorProduct.tmul_add, add_smul])
    (fun c x w => by
      rw [TensorProduct.tmul_smul, LinearMap.map_smul_of_tower, smul_assoc]))

/-- The contraction `baseChangeContract l'` sends `x ⊗ w` to `l' (1 ⊗ w) • (1 ⊗ x)`. -/
@[simp]
theorem baseChangeContract_tmul (l' : F' ⊗[F] W →ₗ[F'] F') (x : V) (w : W) :
    baseChangeContract l' (x ⊗ₜ w) = l' (1 ⊗ₜ w) • ((1 : F') ⊗ₜ[F] x) :=
  rfl

/-- If `1 ⊗ v` lies in the image of the base change of `T`, then `v` lies in the image of `T`. -/
theorem mem_range_of_one_tmul_mem {U : Type*} [AddCommGroup U] [Module F U] (T : U →ₗ[F] V)
    (v : V) (h : (1 : F') ⊗ₜ[F] v ∈ LinearMap.range (T.lTensor F')) : v ∈ LinearMap.range T := by
  obtain ⟨x, hx⟩ := h
  have h0 : ((LinearMap.range T).mkQ.lTensor F') ((1 : F') ⊗ₜ[F] v) = 0 := by
    rw [← hx, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    have : (LinearMap.range T).mkQ ∘ₗ T = 0 := by
      ext u; simp
    rw [this, LinearMap.lTensor_zero, LinearMap.zero_apply]
  rw [LinearMap.lTensor_tmul] at h0
  have h1 : (LinearMap.range T).mkQ v = 0 :=
    injective_one_tmul (F := F) (F' := F') _ (h0.trans (TensorProduct.tmul_zero _ _).symm)
  simpa using h1

/-- **The linear algebra principle of the paragraph (A6) of the proof of Lemma 0FVT**: for
`ξ ∈ V ⊗_F W` and `v ∈ V`, if some `F'`-linear `λ' : W ⊗_F F' → F'` satisfies `(1 ⊗ λ')ξ' = v'`
(images in the base change), then some `F`-linear `λ : W → F` satisfies `(1 ⊗ λ)ξ = v`. -/
theorem exists_contract_eq_of_baseChange (ξ : V ⊗[F] W) (v : V) (l' : F' ⊗[F] W →ₗ[F'] F')
    (h : baseChangeContract l' ξ = (1 : F') ⊗ₜ[F] v) :
    ∃ μ : W →ₗ[F] F, TensorProduct.rid F V (μ.lTensor V ξ) = v := by
  classical
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset ξ
  set W₀ : Submodule F W := Submodule.span F ((S.image Prod.snd : Finset W) : Set W)
  have hmem : ∀ s ∈ S, s.2 ∈ W₀ := fun s hs =>
    Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hs))
  let b := Module.finBasis F W₀
  let r : V × W → Fin (Module.finrank F W₀) → F := fun s =>
    if hs : s.2 ∈ W₀ then b.repr ⟨s.2, hs⟩ else 0
  have hr : ∀ s ∈ S, s.2 = ∑ i, r s i • (b i : W) := by
    intro s hs
    have := congrArg Subtype.val (b.sum_repr ⟨s.2, hmem s hs⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    simpa [r, hmem s hs] using this.symm
  let y : Fin (Module.finrank F W₀) → V := fun i => ∑ s ∈ S, r s i • s.1
  have hcon : ∀ μ : W →ₗ[F] F, TensorProduct.rid F V (μ.lTensor V (∑ s ∈ S, s.1 ⊗ₜ s.2)) =
      ∑ i, μ (b i : W) • y i := by
    intro μ
    simp only [map_sum, LinearMap.lTensor_tmul, TensorProduct.rid_tmul, y, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s hs => ?_
    conv_lhs => rw [hr s hs]
    simp [map_sum, Finset.sum_smul, smul_smul, mul_comm]
  have hcon' : baseChangeContract l' (∑ s ∈ S, s.1 ⊗ₜ s.2) =
      ∑ i, l' (1 ⊗ₜ (b i : W)) • ((1 : F') ⊗ₜ[F] y i) := by
    simp only [map_sum, baseChangeContract_tmul, y, TensorProduct.tmul_sum, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s hs => ?_
    conv_lhs => rw [hr s hs]
    simp only [TensorProduct.tmul_sum, map_sum, Finset.sum_smul, TensorProduct.tmul_smul,
      LinearMap.map_smul_of_tower]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul F' (r s i), ← algebraMap_smul F' (r s i), smul_eq_mul, mul_comm,
      mul_smul]
  let T : (Fin (Module.finrank F W₀) → F) →ₗ[F] V := Fintype.linearCombination F y
  have hv : v ∈ LinearMap.range T := by
    refine mem_range_of_one_tmul_mem (F' := F') T v ⟨∑ i, l' (1 ⊗ₜ (b i : W)) ⊗ₜ Pi.single i 1, ?_⟩
    rw [← h, hcon', map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.lTensor_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    simp [T, Fintype.linearCombination_apply_single]
  obtain ⟨c, hc⟩ := hv
  obtain ⟨μ, hμ⟩ := LinearMap.exists_extend (b.constr F c)
  refine ⟨μ, ?_⟩
  rw [hcon μ, ← hc]
  simp only [T, Fintype.linearCombination_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := LinearMap.congr_fun hμ (b i)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
  rw [this, Module.Basis.constr_basis]

end Stacks.WeilDeRham

end
