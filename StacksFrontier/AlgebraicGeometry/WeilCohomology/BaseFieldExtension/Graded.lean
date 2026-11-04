module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.BaseFieldExtension.Coproduct

/-!
# The comparison isomorphisms of Tag 0FVT on graded pieces

For the comparison data `Φ` of Tag 0FVT, the isomorphisms `H^*(X) ⊗_F F' ≅ (H')^*(X_{k'})` are
graded. Both gradings being direct sum decompositions, they commute with the projections onto
the graded pieces, an element of `H^*(X)` is of degree `n` exactly when its image is, and they
restrict to isomorphisms `H^n(X) ⊗_F F' ≅ (H')^n(X_{k'})`.

## Main definitions

* `Stacks.WeilCohomology.FieldExtensionComparison.gradeEquiv`:
  `F' ⊗_F H^n(X) ≃ₗ[F'] (H')^n(X_{k'})`.

## Main results

* `Stacks.WeilCohomology.FieldExtensionComparison.iso_decompose`: the comparison commutes with
  the projections onto the graded pieces.
* `Stacks.WeilCohomology.FieldExtensionComparison.mem_grade_iff`: `a ∈ H^n(X)` if and only if its
  image lies in `(H')^n(X_{k'})`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Function DirectSum

universe u w w'

namespace Stacks.WeilCohomology

section LinearAlgebra

variable {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']
  {V : Type*} [AddCommGroup V] [Module F V] {W : Type*} [AddCommGroup W] [Module F' W]
  (𝒱 : ℤ → Submodule F V) [Decomposition 𝒱] (𝒲 : ℤ → Submodule F' W) [Decomposition 𝒲]

/-- The degree-`n` part of a finite sum of homogeneous elements, the `m`-th of degree `m`. -/
theorem coe_decompose_sum_of_mem (s : Finset ℤ) (y : ℤ → W) (hy : ∀ m, y m ∈ 𝒲 m) (n : ℤ) :
    (decompose 𝒲 (∑ m ∈ s, y m) n : W) = if n ∈ s then y n else 0 := by
  classical
  rw [decompose_sum, DFinsupp.finsetSum_apply, Submodule.coe_sum,
    Finset.sum_congr rfl (g := fun m => if m = n then y m else 0) fun m _ => by
      split_ifs with h
      · subst h; exact decompose_of_mem_same 𝒲 (hy m)
      · exact decompose_of_mem_ne 𝒲 (hy m) h,
    Finset.sum_ite_eq']

variable {𝒱 𝒲} (ψ : F' ⊗[F] V ≃ₗ[F'] W)
  (hψ : ∀ (n : ℤ) (v : V), v ∈ 𝒱 n → ψ (1 ⊗ₜ v) ∈ 𝒲 n)

include hψ

/-- A graded isomorphism `F' ⊗_F V ≅ W` commutes with the projections onto the graded pieces. -/
theorem baseChange_decompose (v : V) (n : ℤ) :
    ψ (1 ⊗ₜ (decompose 𝒱 v n : V)) = (decompose 𝒲 (ψ (1 ⊗ₜ v)) n : W) := by
  classical
  conv_rhs => rw [← sum_support_decompose 𝒱 v, tmul_sum, map_sum]
  rw [coe_decompose_sum_of_mem 𝒲 _ (fun m => ψ (1 ⊗ₜ (decompose 𝒱 v m : V)))
    (fun m => hψ m _ (decompose 𝒱 v m).2) n]
  split_ifs with h
  · rfl
  · rw [DFinsupp.notMem_support_iff.mp h, Submodule.coe_zero, tmul_zero, map_zero]

/-- Under a graded isomorphism `F' ⊗_F V ≅ W`, `v` is of degree `n` exactly when `1 ⊗ v` is. -/
theorem mem_iff_baseChange_mem (v : V) (n : ℤ) : v ∈ 𝒱 n ↔ ψ (1 ⊗ₜ v) ∈ 𝒲 n := by
  refine ⟨hψ n v, fun h => ?_⟩
  have key : ∀ m, m ≠ n → (decompose 𝒱 v m : V) = 0 := fun m hm => by
    refine injective_one_tmul (F := F) (V := V) F' (ψ.injective ?_)
    simp only [tmul_zero, map_zero]
    rw [baseChange_decompose ψ hψ, decompose_of_mem_ne 𝒲 h hm.symm]
  classical
  rw [← sum_support_decompose 𝒱 v]
  refine Submodule.sum_mem _ fun m _ => ?_
  by_cases hm : m = n
  · subst hm; exact (decompose 𝒱 v m).2
  · rw [key m hm]; exact zero_mem _

/-- The restriction `F' ⊗_F V_n → W_n` of a graded isomorphism `F' ⊗_F V ≅ W`. -/
def baseChangeGradeMap (n : ℤ) : F' ⊗[F] 𝒱 n →ₗ[F'] 𝒲 n :=
  LinearMap.codRestrict (𝒲 n) (ψ.toLinearMap ∘ₗ (𝒱 n).subtype.baseChange F') fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearMap.baseChange_tmul, Submodule.coe_subtype]
      rw [tmul_eq_smul_one_tmul, map_smul]
      exact Submodule.smul_mem _ _ (hψ n v v.2)
    | add x y hx hy =>
      simp only [map_add] at hx hy ⊢
      exact add_mem hx hy

omit [Decomposition 𝒱] [Decomposition 𝒲] in
/-- `baseChangeGradeMap` sends `a ⊗ v` to `ψ (a ⊗ v)`, viewed in `W`. -/
theorem coe_baseChangeGradeMap_tmul (n : ℤ) (a : F') (v : 𝒱 n) :
    (baseChangeGradeMap ψ hψ n (a ⊗ₜ v) : W) = ψ (a ⊗ₜ (v : V)) := rfl

/-- The restriction `F' ⊗_F V_n → W_n` of a graded isomorphism `F' ⊗_F V ≅ W` is bijective:
injective because `F'` is flat over `F`, surjective because `ψ` commutes with the projections
onto the graded pieces. -/
theorem bijective_baseChangeGradeMap (n : ℤ) : Bijective (baseChangeGradeMap ψ hψ n) := by
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · have h := congrArg Subtype.val hxy
    simp only [baseChangeGradeMap, LinearMap.codRestrict_apply, LinearMap.coe_comp,
      LinearEquiv.coe_coe, Function.comp_apply] at h
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := F') _ (𝒱 n).injective_subtype
      (ψ.injective h)
  · obtain ⟨x, hx⟩ := ψ.surjective y
    -- the degree-`n` projection, extended to `F'`
    let p : V →ₗ[F] 𝒱 n := (component F ℤ (fun i => 𝒱 i) n) ∘ₗ
      (decomposeLinearEquiv 𝒱).toLinearMap
    refine ⟨p.baseChange F' x, Subtype.ext ?_⟩
    have key : ∀ z : F' ⊗[F] V, ψ (((𝒱 n).subtype.baseChange F') (p.baseChange F' z)) =
        (decompose 𝒲 (ψ z) n : W) := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a v =>
        rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
          show a ⊗ₜ[F] (𝒱 n).subtype (p v) = a • ((1 : F') ⊗ₜ[F] (decompose 𝒱 v n : V)) by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]; rfl,
          tmul_eq_smul_one_tmul a v,
          map_smul, map_smul, decompose_smul, baseChange_decompose ψ hψ]
        rfl
      | add z z' hz hz' => rw [map_add, map_add, map_add, hz, hz', map_add, decompose_add]; rfl
    show ψ _ = _
    rw [key, hx, decompose_of_mem_same 𝒲 y.2]

/-- **A graded isomorphism `F' ⊗_F V ≅ W` restricts to `F' ⊗_F V_n ≅ W_n`.** -/
def baseChangeGradeEquiv (n : ℤ) : F' ⊗[F] 𝒱 n ≃ₗ[F'] 𝒲 n :=
  LinearEquiv.ofBijective (baseChangeGradeMap ψ hψ n) (bijective_baseChangeGradeMap ψ hψ n)

/-- `baseChangeGradeEquiv` sends `a ⊗ v` to `ψ (a ⊗ v)`, viewed in `W`. -/
theorem coe_baseChangeGradeEquiv_tmul (n : ℤ) (a : F') (v : 𝒱 n) :
    (baseChangeGradeEquiv ψ hψ n (a ⊗ₜ v) : W) = ψ (a ⊗ₜ (v : V)) := rfl

end LinearAlgebra

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
  {F : Type w} [Field F] {F' : Type w'} [Field F'] [Algebra F F']
  {𝔇 : FirstChernClassData k F} {𝔇' : FirstChernClassData k' F'}

namespace FieldExtensionComparison

open SmoothProjectiveScheme

variable (Φ : FieldExtensionComparison 𝔇 𝔇')

/-- **The comparison commutes with the projections onto the graded pieces.** -/
theorem iso_decompose (X : (SmoothProjectiveScheme k).FullSubcategory) (a : 𝔇.H X) (n : ℤ) :
    Φ.iso X (1 ⊗ₜ (decompose (𝔇.grade X) a n : 𝔇.H X)) =
      (decompose (𝔇'.grade ((baseChange k k').obj X)) (Φ.iso X (1 ⊗ₜ a)) n : _) :=
  baseChange_decompose (Φ.iso X).toLinearEquiv (Φ.iso_grade X) a n

/-- **`a ∈ H^n(X)` if and only if its image lies in `(H')^n(X_{k'})`.** -/
theorem mem_grade_iff (X : (SmoothProjectiveScheme k).FullSubcategory) (a : 𝔇.H X) (n : ℤ) :
    a ∈ 𝔇.grade X n ↔ Φ.iso X (1 ⊗ₜ a) ∈ 𝔇'.grade ((baseChange k k').obj X) n :=
  mem_iff_baseChange_mem (Φ.iso X).toLinearEquiv (Φ.iso_grade X) a n

/-- **The comparison on graded pieces**, `F' ⊗_F H^n(X) ≅ (H')^n(X_{k'})`. -/
def gradeEquiv (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ) :
    F' ⊗[F] 𝔇.grade X n ≃ₗ[F'] 𝔇'.grade ((baseChange k k').obj X) n :=
  baseChangeGradeEquiv (Φ.iso X).toLinearEquiv (Φ.iso_grade X) n

/-- The comparison on graded pieces sends `c ⊗ a` to the image of `c ⊗ a` under the comparison,
viewed in `(H')^*(X_{k'})`. -/
theorem coe_gradeEquiv_tmul (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ) (c : F')
    (a : 𝔇.grade X n) : (Φ.gradeEquiv X n (c ⊗ₜ a) : 𝔇'.H _) = Φ.iso X (c ⊗ₜ (a : 𝔇.H X)) :=
  rfl

end FieldExtensionComparison

end Stacks.WeilCohomology
