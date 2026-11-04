module

public import StacksFrontier.Algebra.Module.FlatComplexNakayama

/-!
# Transfer of cohomological conditions along base change

Let `C₀ ⟶ C₁ ⟶ C₂` and `D₀ ⟶ D₁` be complexes of `R`-modules with a map `φ` between their first
two terms, and let `K` be an `R`-algebra. Suppose `C'ᵢ`, `D'ᵢ` are `K`-modules with maps
`θ : Cᵢ ⟶ C'ᵢ`, `θ : Dᵢ ⟶ D'ᵢ` exhibiting them as base changes to `K`, compatible with primed
differentials and maps. Then the conditions `SurjZero`, `InjOne` of
`StacksFrontier/Algebra/Module/FlatComplexNakayama.lean`, injectivity of the cone differential and of
`d₀` after base change to `K` follow from the corresponding conditions on the primed complexes.

This is how a computation on a fibre is turned into a statement about the base change of a
complex to a residue field.

## References

* [Stacks Project, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2)
-/

@[expose] public section

open TensorProduct

universe u

namespace Stacks.ConeTransfer

open Stacks.FlatComplexNakayama

variable {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]

/-- Naturality of the base-change equivalence. -/
theorem equiv_comp_baseChange {M N M' N' : Type u} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup M'] [AddCommGroup N'] [Module R M] [Module R N] [Module R M'] [Module R N']
    [Module K M'] [Module K N'] [IsScalarTower R K M'] [IsScalarTower R K N']
    {θ : M →ₗ[R] M'} {θ' : N →ₗ[R] N'} (hθ : IsBaseChange K θ) (hθ' : IsBaseChange K θ')
    (f : M →ₗ[R] N) (f' : M' →ₗ[K] N') (hf : (f'.restrictScalars R) ∘ₗ θ = θ' ∘ₗ f)
    (x : K ⊗[R] M) : hθ'.equiv (f.baseChange K x) = f' (hθ.equiv x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
    rw [LinearMap.baseChange_tmul, IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul, map_smul]
    congr 1
    exact (LinearMap.congr_fun hf m).symm
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- Applying `f'` to the base-change identification of `x` vanishes if `f.baseChange K x` does. -/
private theorem apply_equiv_eq_zero {M N M' N' : Type u} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup M'] [AddCommGroup N'] [Module R M] [Module R N] [Module R M'] [Module R N']
    [Module K M'] [Module K N'] [IsScalarTower R K M'] [IsScalarTower R K N']
    {θ : M →ₗ[R] M'} {θ' : N →ₗ[R] N'} (hθ : IsBaseChange K θ) (hθ' : IsBaseChange K θ')
    (f : M →ₗ[R] N) (f' : M' →ₗ[K] N') (hf : (f'.restrictScalars R) ∘ₗ θ = θ' ∘ₗ f)
    {x : K ⊗[R] M} (hx : f.baseChange K x = 0) : f' (hθ.equiv x) = 0 := by
  rw [← equiv_comp_baseChange hθ hθ' f f' hf, hx, map_zero]

variable {C₀ C₁ C₂ D₀ D₁ C₀' C₁' C₂' D₀' D₁' : Type u}
  [AddCommGroup C₀] [AddCommGroup C₁] [AddCommGroup C₂] [AddCommGroup D₀] [AddCommGroup D₁]
  [Module R C₀] [Module R C₁] [Module R C₂] [Module R D₀] [Module R D₁]
  [AddCommGroup C₀'] [AddCommGroup C₁'] [AddCommGroup C₂'] [AddCommGroup D₀'] [AddCommGroup D₁']
  [Module R C₀'] [Module R C₁'] [Module R C₂'] [Module R D₀'] [Module R D₁']
  [Module K C₀'] [Module K C₁'] [Module K C₂'] [Module K D₀'] [Module K D₁']
  [IsScalarTower R K C₀'] [IsScalarTower R K C₁'] [IsScalarTower R K C₂']
  [IsScalarTower R K D₀'] [IsScalarTower R K D₁']
  {d₀ : C₀ →ₗ[R] C₁} {d₁ : C₁ →ₗ[R] C₂} {δ₀ : D₀ →ₗ[R] D₁} {φ₀ : C₀ →ₗ[R] D₀}
  {φ₁ : C₁ →ₗ[R] D₁}
  {d₀' : C₀' →ₗ[K] C₁'} {d₁' : C₁' →ₗ[K] C₂'} {δ₀' : D₀' →ₗ[K] D₁'} {φ₀' : C₀' →ₗ[K] D₀'}
  {φ₁' : C₁' →ₗ[K] D₁'}
  {θC₀ : C₀ →ₗ[R] C₀'} {θC₁ : C₁ →ₗ[R] C₁'} {θC₂ : C₂ →ₗ[R] C₂'} {θD₀ : D₀ →ₗ[R] D₀'}
  {θD₁ : D₁ →ₗ[R] D₁'}
  (hC₀ : IsBaseChange K θC₀) (hC₁ : IsBaseChange K θC₁) (hC₂ : IsBaseChange K θC₂)
  (hD₀ : IsBaseChange K θD₀) (hD₁ : IsBaseChange K θD₁)
  (hd₀ : (d₀'.restrictScalars R) ∘ₗ θC₀ = θC₁ ∘ₗ d₀)
  (hd₁ : (d₁'.restrictScalars R) ∘ₗ θC₁ = θC₂ ∘ₗ d₁)
  (hδ₀ : (δ₀'.restrictScalars R) ∘ₗ θD₀ = θD₁ ∘ₗ δ₀)
  (hφ₀ : (φ₀'.restrictScalars R) ∘ₗ θC₀ = θD₀ ∘ₗ φ₀)
  (hφ₁ : (φ₁'.restrictScalars R) ∘ₗ θC₁ = θD₁ ∘ₗ φ₁)

include hC₀ hC₁ hD₀ hD₁ hd₀ hδ₀ hφ₀ in
/-- If every `y : D₀'` with `δ₀' y = 0` is `φ₀' c` for some `c : C₀'` with `d₀' c = 0`, then
`SurjZero d₀ δ₀ φ₀ K` holds. -/
theorem surjZero_of
    (h : ∀ y : D₀', δ₀' y = 0 → ∃ c : C₀', d₀' c = 0 ∧ φ₀' c = y) :
    SurjZero d₀ δ₀ φ₀ K := by
  intro y hy
  obtain ⟨c, hc0, hcy⟩ := h _ (apply_equiv_eq_zero hD₀ hD₁ δ₀ δ₀' hδ₀ hy)
  refine ⟨hC₀.equiv.symm c, hC₁.equiv.injective ?_, hD₀.equiv.injective ?_⟩
  · rw [equiv_comp_baseChange hC₀ hC₁ d₀ d₀' hd₀, LinearEquiv.apply_symm_apply, hc0, map_zero]
  · rw [equiv_comp_baseChange hC₀ hD₀ φ₀ φ₀' hφ₀, LinearEquiv.apply_symm_apply, hcy]

include hC₀ hC₁ hC₂ hD₀ hD₁ hd₀ hd₁ hδ₀ hφ₁ in
/-- If every `x : C₁'` with `d₁' x = 0` and `φ₁' x` in the range of `δ₀'` lies in the range of
`d₀'`, then `InjOne d₀ d₁ δ₀ φ₁ K` holds. -/
theorem injOne_of
    (h : ∀ x : C₁', d₁' x = 0 → (∃ y, φ₁' x = δ₀' y) → ∃ c, d₀' c = x) :
    InjOne d₀ d₁ δ₀ φ₁ K := by
  intro x hx ⟨y, hy⟩
  have hy' : φ₁' (hC₁.equiv x) = δ₀' (hD₀.equiv y) := by
    rw [← equiv_comp_baseChange hC₁ hD₁ φ₁ φ₁' hφ₁, ← equiv_comp_baseChange hD₀ hD₁ δ₀ δ₀' hδ₀,
      hy]
  obtain ⟨c, hc⟩ := h _ (apply_equiv_eq_zero hC₁ hC₂ d₁ d₁' hd₁ hx) ⟨_, hy'⟩
  refine ⟨hC₀.equiv.symm c, hC₁.equiv.injective ?_⟩
  rw [equiv_comp_baseChange hC₀ hC₁ d₀ d₀' hd₀, LinearEquiv.apply_symm_apply, hc]

include hC₀ hC₁ hD₀ hd₀ hφ₀ in
/-- If the only `c : C₀'` with `d₀' c = 0` and `φ₀' c = 0` is `c = 0`, then the base change
`(coneD₀ d₀ φ₀).baseChange K` of the cone differential is injective. -/
theorem ker_coneD₀_baseChange_eq_bot_of
    (h : ∀ c : C₀', d₀' c = 0 → φ₀' c = 0 → c = 0) :
    LinearMap.ker ((coneD₀ d₀ φ₀).baseChange K) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  have hx0 := congrArg (TensorProduct.prodRight R K K C₁ D₀) (LinearMap.mem_ker.mp hx)
  rw [prodRight_coneD₀, map_zero] at hx0
  have hx1 := Prod.ext_iff.mp hx0
  exact hC₀.equiv.map_eq_zero_iff.mp (h _ (apply_equiv_eq_zero hC₀ hC₁ d₀ d₀' hd₀ hx1.1)
    (apply_equiv_eq_zero hC₀ hD₀ φ₀ φ₀' hφ₀ hx1.2))

include hC₀ hC₁ hd₀ in
/-- If `d₀'` is injective, then the base change `d₀.baseChange K` is injective. -/
theorem ker_baseChange_eq_bot_of (h : ∀ c : C₀', d₀' c = 0 → c = 0) :
    LinearMap.ker (d₀.baseChange K) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  exact hC₀.equiv.map_eq_zero_iff.mp
    (h _ (apply_equiv_eq_zero hC₀ hC₁ d₀ d₀' hd₀ (LinearMap.mem_ker.mp hx)))

end Stacks.ConeTransfer

end
