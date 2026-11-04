module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.ConcreteCover
public import StacksFrontier.RingTheory.Descent.AmitsurComplex

/-!
# Exactness of the kernels of the Čech diagram of a thickening

Let `A' → A` be a surjection with square-zero kernel and let `B'` be a faithfully flat
`A'`-algebra, with reduction `B = A ⊗[A'] B'`. Let `J₁ ⊆ B'` and `J₂ ⊆ B' ⊗[A'] B'` be the kernels
of the reductions of the concrete Čech diagram, `Stacks.ChartGlue.Concrete`. This file proves
that every element `c` of `J₂` satisfying the cocycle identity `q₁₂ c - q₁₃ c + q₂₃ c = 0` is
`p₂ s - p₁ s` for some `s ∈ J₁`.

The proof uses exactness of the Amitsur complex of `A' → B'` in degree one
(`Module.Descent.exact_amitsur_degree_one`) to write `c = p₂ s - p₁ s` for some `s ∈ B'`, and
exactness of the Amitsur complex of the faithfully flat `A → B` in degree zero to correct `s` by
an element of `A'` so that it lies in `J₁`.

## Main results

* `Stacks.ChartGlue.Concrete.exists_of_cocycle`: every Amitsur `1`-cocycle of `A' → B'` is a
  coboundary.
* `Stacks.ChartGlue.Concrete.exists_ker_of_cocycle`: the statement above.
-/

@[expose] public noncomputable section

open TensorProduct Module.Descent

universe u

namespace Stacks.ChartGlue

namespace Concrete

variable (A' A : Type u) [CommRing A'] [CommRing A] [Algebra A' A]
  (hA : Function.Surjective (algebraMap A' A))
  (B' : Type u) [CommRing B'] [Algebra A' B']

/-- `B' ⊗ A' ≅ B'`. -/
abbrev e₁ : B' ⊗[A'] A' ≃ₗ[A'] B' := TensorProduct.rid A' B'
/-- `B' ⊗ (B' ⊗ A') ≅ B' ⊗ B'`. -/
abbrev e₂ : B' ⊗[A'] (B' ⊗[A'] A') ≃ₗ[A'] B' ⊗[A'] B' :=
  TensorProduct.congr (LinearEquiv.refl A' B') (e₁ A' B')
/-- `B' ⊗ (B' ⊗ (B' ⊗ A')) ≅ B' ⊗ (B' ⊗ B')`. -/
abbrev e₃ : B' ⊗[A'] (B' ⊗[A'] (B' ⊗[A'] A')) ≃ₗ[A'] B' ⊗[A'] (B' ⊗[A'] B') :=
  TensorProduct.congr (LinearEquiv.refl A' B') (e₂ A' B')

/-- `m ⊗ algebraMap a = (a • m) ⊗ 1` in `N ⊗[A'] B'`. -/
lemma tmul_algebraMap {N : Type u} [AddCommGroup N] [Module A' N] (m : N) (a : A') :
    m ⊗ₜ[A'] (algebraMap A' B' a) = (a • m) ⊗ₜ[A'] (1 : B') := by
  rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_one]

/-- Under `e₁` and `e₂`, the degree-zero Amitsur differential of `A' → B'` with coefficients in
`A'` is `p₁ - p₂`. -/
lemma e₂_amitsurDiff₀ (x : B' ⊗[A'] A') :
    e₂ A' B' (amitsurDiff₀ A' B' A' x) = p₁ A' B' (e₁ A' B' x) - p₂ A' B' (e₁ A' B' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, map_add]; abel
  | tmul b a =>
    rw [amitsurDiff₀_tmul, map_sub]
    simp only [LinearEquiv.coe_coe, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
      TensorProduct.rid_tmul, AlgHom.coe_comp, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply]
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']

/-- Under `e₂` and `e₃`, the degree-one Amitsur differential of `A' → B'` with coefficients in
`A'` is `q₂₃ - q₁₃ + q₁₂`. -/
lemma e₃_amitsurDiff₁ (x : B' ⊗[A'] (B' ⊗[A'] A')) :
    e₃ A' B' (amitsurDiff₁ A' B' A' x) =
      q₂₃ A' B' (e₂ A' B' x) - q₁₃ A' B' (e₂ A' B' x) + q₁₂ A' B' (e₂ A' B' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add, map_add, map_add, map_add]; abel
  | tmul b y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz =>
      rw [tmul_add, map_add, map_add, hy, hz, map_add, map_add, map_add, map_add]; abel
    | tmul c a =>
      rw [amitsurDiff₁_tmul, map_add, map_sub]
      simp [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul', Algebra.smul_def,
        tmul_algebraMap A' B']

/-- **Every Amitsur `1`-cocycle of `A' → B'` with values in `B' ⊗ B'` is a coboundary.** -/
lemma exists_of_cocycle [Module.FaithfullyFlat A' B'] (c : B' ⊗[A'] B')
    (hc : q₁₂ A' B' c - q₁₃ A' B' c + q₂₃ A' B' c = 0) :
    ∃ s : B', p₂ A' B' s - p₁ A' B' s = c := by
  have hc' : amitsurDiff₁ A' B' A' ((e₂ A' B').symm c) = 0 := by
    apply (e₃ A' B').injective
    rw [e₃_amitsurDiff₁, LinearEquiv.apply_symm_apply, map_zero, ← hc]
    abel
  obtain ⟨y, hy⟩ := exists_amitsurDiff₀_eq A' B' A' hc'
  refine ⟨-(e₁ A' B' y), ?_⟩
  have := congrArg (e₂ A' B') hy
  rw [e₂_amitsurDiff₀, LinearEquiv.apply_symm_apply] at this
  rw [map_neg, map_neg, ← this]
  abel

/-- **Exactness in degree zero for `A → B`**: an element of `B` with `t ⊗ 1 = 1 ⊗ t` comes from
`A`. -/
lemma exists_algebraMap_of_tmul_eq [Module.FaithfullyFlat A' B'] (t : Bb A' A B')
    (ht : i₁ A' A B' t = i₂ A' A B' t) : ∃ a : A, algebraMap A (Bb A' A B') a = t := by
  let e : Bb A' A B' ⊗[A] (Bb A' A B' ⊗[A] A) ≃ₗ[A] Bb A' A B' ⊗[A] Bb A' A B' :=
    TensorProduct.congr (LinearEquiv.refl A _) (TensorProduct.rid A _)
  have h0 : amitsurDiff₀ A (Bb A' A B') A (t ⊗ₜ[A] (1 : A)) = 0 := by
    apply e.injective
    rw [amitsurDiff₀_tmul, map_sub, map_zero, sub_eq_zero]
    simpa [e] using ht
  obtain ⟨a, ha⟩ := (exact_amitsur_degree_zero A (Bb A' A B') A (t ⊗ₜ[A] (1 : A))).1 h0
  refine ⟨a, ?_⟩
  simpa [amitsurAug_apply, Algebra.algebraMap_eq_smul_one] using
    congrArg (TensorProduct.rid A (Bb A' A B')) ha

include hA in
/-- **A cocycle in the kernel `J₂` is the coboundary of an element of `J₁`.** -/
theorem exists_ker_of_cocycle [Module.FaithfullyFlat A' B'] (c : B' ⊗[A'] B')
    (hc0 : π₂ A' A B' c = 0)
    (hc : q₁₂ A' B' c - q₁₃ A' B' c + q₂₃ A' B' c = 0) :
    ∃ s : B', π₁ A' A B' s = 0 ∧ p₂ A' B' s - p₁ A' B' s = c := by
  obtain ⟨s₀, hs₀⟩ := exists_of_cocycle A' B' c hc
  have ht : i₁ A' A B' (π₁ A' A B' s₀) = i₂ A' A B' (π₁ A' A B' s₀) := by
    have h := congrArg (π₂ A' A B') hs₀
    rw [hc0, map_sub, sub_eq_zero] at h
    exact (DFunLike.congr_fun (p₁_π A' A B') s₀).symm.trans
      (h.symm.trans (DFunLike.congr_fun (p₂_π A' A B') s₀))
  obtain ⟨a, ha⟩ := exists_algebraMap_of_tmul_eq A' A B' _ ht
  obtain ⟨a', rfl⟩ := hA a
  refine ⟨s₀ - algebraMap A' B' a', ?_, ?_⟩
  · rw [map_sub, AlgHom.commutes, ← ha, IsScalarTower.algebraMap_apply A' A (Bb A' A B'),
      sub_self]
  · rw [map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, ← hs₀]
    abel

end Concrete

end Stacks.ChartGlue

end
