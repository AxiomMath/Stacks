module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TraceUniqueness

/-!
# The triangle identity of Lemma 0FIJ, and the algebra of Remark 0FIK

Lemma 0FIJ of the Stacks Project shows that `H^*(X)(d)[2d]` is a left dual of `H^*(X)` with unit
`η = γ([Δ])` and counit `ε = λ ∘ Δ^*`; the triangle identity it writes out reduces to

`(1 ⊗ λ)(γ([Δ]) ∪ p_2^*a) = a`, using `γ([Δ]) ∪ p_1^*a = γ([Δ]) ∪ p_2^*a`

(the closing paragraph of the proof, Lemma 0FII applied to the diagonal). The base proves Lemma
0FIJ (`…FirstChernClassData.IsCohomologicalChernCharacter.poincareDuality_toWeilData`), Remark 0FIK
(`…IsCohomologicalChernCharacter.trace_unique`,
`…IsCohomologicalChernCharacter.bijective_diagonalContract`) and the identity
`γ([Δ]) ∪ p_1^*a = γ([Δ]) ∪ p_2^*a` (`…IsCohomologicalChernCharacter.key_diagonalClass`), through
the linear algebra of `Stacks.WeilCohomology.DiagonalExpansion` on a Künneth expansion of `γ([Δ])`
as a list. This file keeps the same linear algebra in the form of a Künneth isomorphism
`κ : A ⊗ A ≅ P` and the contraction `Stacks.WeilCohomology.DiagonalExpansion.contractRight`,
which the computations of the product formula (Lemma 0FIL) use, and the triangle identity in
that form for the cycle class map of Tag 0FIF.

## Main results

* `Stacks.WeilDeRham.eq_zero_of_forall_mul`, `Stacks.WeilDeRham.eq_of_contractRight`: the pairing
  has no kernel, and Remark 0FIK in algebraic form.
* `Stacks.WeilDeRham.untwistTrace_decompose`, `Stacks.WeilDeRham.trace_eq_untwistTrace`: the
  untwisted trace `Stacks.WeilCohomology.FirstChernClassData.untwistTrace` only sees the degree
  `2d` part, and recovers `λ`.

## References

* [Stacks Project, Tag 0FIJ](https://stacks.math.columbia.edu/tag/0FIJ)
* [Stacks Project, Tag 0FIK](https://stacks.math.columbia.edu/tag/0FIK)
* [Stacks Project, Tag 0FII](https://stacks.math.columbia.edu/tag/0FII)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct DirectSum
open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme
open Stacks.WeilCohomology.DiagonalExpansion (contractRight contractRight_tmul)

universe u w

namespace Stacks.WeilDeRham

/-! ### The algebraic core -/

section Algebra

variable {F : Type*} [Field F] {A P : Type*} [Ring A] [Algebra F A] [Ring P] [Algebra F P]

variable (p q : A →ₐ[F] P) (κ : A ⊗[F] A ≃ₗ[F] P) (hκ : ∀ x y, κ (x ⊗ₜ y) = p x * q y)
include hκ

omit hκ

/-! ### Consequences of the triangle identity -/

variable {s : A ⊗[F] A} {μ : A →ₗ[F] F}

/-- The triangle identity written out on a representation `s = ∑_l x_l ⊗ y_l`. -/
theorem sum_smul_eq_of_contractRight {m : ℕ} {x y : Fin m → A}
    (hI : ∀ a, contractRight μ (LinearMap.lTensor A (LinearMap.mulRight F a)
      (∑ l, x l ⊗ₜ[F] y l)) = a) (a : A) :
    ∑ l, μ (y l * a) • x l = a := by
  simpa [map_sum] using hI a

variable (𝒜 : ℤ → Submodule F A) [_root_.GradedAlgebra 𝒜] {n : ℤ}

/-- **The pairing has no right kernel.** Let `μ` vanish off degree `n`. If
`a = (id ⊗ μ)(s ∪ (1 ⊗ a))` for all `a`, then a homogeneous `a` of degree `k` with
`μ(b ∪ a) = 0` for every `b` of degree `j = n - k` is zero. -/
theorem eq_zero_of_forall_mul_right
    (hI : ∀ a, contractRight μ (LinearMap.lTensor A (LinearMap.mulRight F a) s) = a)
    (hμ : ∀ x, μ x = μ (decompose 𝒜 x n : A)) {j k : ℤ} (hjk : j + k = n) {a : A}
    (ha : a ∈ 𝒜 k) (h : ∀ b ∈ 𝒜 j, μ (b * a) = 0) : a = 0 := by
  obtain ⟨m, x, y, rfl⟩ := exists_sum_tmul_eq s
  rw [← sum_smul_eq_of_contractRight hI a]
  refine Finset.sum_eq_zero fun l _ ↦ ?_
  rw [hμ, ← hjk, coe_decompose_mul_add_of_right_mem _ ha, h _ (SetLike.coe_mem _), zero_smul]

/-- A unit of `ℤ` acting on a group cancels: `u • v = 0` gives `v = 0`. -/
private theorem eq_zero_of_units_zsmul_eq_zero {M : Type*} [AddCommGroup M] (u : ℤˣ) {v : M}
    (h : (u : ℤ) • v = 0) : v = 0 := by
  have : ((u : ℤ) * u) • v = 0 := by rw [mul_smul, h, smul_zero]
  rwa [← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul] at this

/-- **The pairing has no left kernel**, by graded commutativity. -/
theorem eq_zero_of_forall_mul_left
    (hI : ∀ a, contractRight μ (LinearMap.lTensor A (LinearMap.mulRight F a) s) = a)
    (hμ : ∀ x, μ x = μ (decompose 𝒜 x n : A))
    (hc : ∀ (i j : ℤ) (a b : A), a ∈ 𝒜 i → b ∈ 𝒜 j → a * b = (Int.negOnePow (i * j) : ℤ) • (b * a))
    {j k : ℤ} (hjk : j + k = n) {a : A} (ha : a ∈ 𝒜 k) (h : ∀ b ∈ 𝒜 j, μ (a * b) = 0) :
    a = 0 :=
  eq_zero_of_forall_mul_right 𝒜 hI hμ hjk ha fun b hb ↦ by
    have hab := h b hb
    rw [hc k j a b ha hb, map_zsmul] at hab
    exact eq_zero_of_units_zsmul_eq_zero _ hab

/-- The pairing has no left kernel on all of `A`: `μ(z ∪ a) = 0` for all `a` gives `z = 0`. -/
theorem eq_zero_of_forall_mul
    (hI : ∀ a, contractRight μ (LinearMap.lTensor A (LinearMap.mulRight F a) s) = a)
    (hμ : ∀ x, μ x = μ (decompose 𝒜 x n : A))
    (hc : ∀ (i j : ℤ) (a b : A), a ∈ 𝒜 i → b ∈ 𝒜 j → a * b = (Int.negOnePow (i * j) : ℤ) • (b * a))
    {z : A} (h : ∀ a, μ (z * a) = 0) : z = 0 := by
  have hcomp : ∀ i, (decompose 𝒜 z i : A) = 0 := fun i ↦
    eq_zero_of_forall_mul_left 𝒜 hI hμ hc (j := n - i) (by ring) (SetLike.coe_mem _)
      fun b hb ↦ by
        rw [← coe_decompose_mul_add_of_right_mem _ hb, show i + (n - i) = n by ring, ← hμ, h]
  apply (decompose 𝒜).injective
  rw [decompose_zero]
  ext i
  simpa using hcomp i

/-- **Remark 0FIK, algebraic form.** Two maps `μ`, `μ'` vanishing off degree `n`, each satisfying
the triangle identity for the same `s`, are equal. -/
theorem eq_of_contractRight {μ' : A →ₗ[F] F}
    (hI : ∀ a, contractRight μ (LinearMap.lTensor A (LinearMap.mulRight F a) s) = a)
    (hI' : ∀ a, contractRight μ' (LinearMap.lTensor A (LinearMap.mulRight F a) s) = a)
    (_hμ : ∀ x, μ x = μ (decompose 𝒜 x n : A)) (hμ' : ∀ x, μ' x = μ' (decompose 𝒜 x n : A))
    (hc : ∀ (i j : ℤ) (a b : A), a ∈ 𝒜 i → b ∈ 𝒜 j → a * b = (Int.negOnePow (i * j) : ℤ) • (b * a))
    (z : A) : μ' z = μ z := by
  obtain ⟨m, x, y, rfl⟩ := exists_sum_tmul_eq s
  -- the second triangle identity `b = ∑_l μ'(b ∪ x_l) y_l`, at `b = 1`
  have hII : ∑ l, μ' (x l) • y l = 1 := by
    have h0 : (1 : A) - ∑ l, μ' (1 * x l) • y l = 0 := by
      refine eq_zero_of_forall_mul 𝒜 hI' hμ' hc fun a ↦ ?_
      have hμa : μ' a = ∑ l, μ' (y l * a) * μ' (x l) := by
        conv_lhs => rw [← sum_smul_eq_of_contractRight hI' a]
        simp [map_sum]
      simp only [one_mul, sub_mul, Finset.sum_mul, smul_mul_assoc, map_sub, map_sum, map_smul,
        smul_eq_mul, hμa]
      exact sub_eq_zero.mpr (Finset.sum_congr rfl fun l _ ↦ mul_comm _ _)
    have h1 := (sub_eq_zero.mp h0).symm
    simpa only [one_mul] using h1
  conv_lhs => rw [← sum_smul_eq_of_contractRight hI z]
  simp only [map_sum, map_smul, smul_eq_mul]
  conv_rhs => rw [← one_mul z, ← hII]
  simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, smul_eq_mul, mul_comm]

end Algebra

/-! ### The data (D0), (D1): the triangle identity of Lemma 0FIJ -/

section Weil

variable {k : Type u} [Field k] {F : Type w} [Field F] {𝔇 : FirstChernClassData k F}
  {X : (SmoothProjectiveScheme k).FullSubcategory}

/-- Reading a graded piece into `𝔇.H X` and projecting back is the identity. -/
private theorem projGrade_coe {n : ℤ} (w : 𝔇.grade X n) : 𝔇.projGrade X n (w : 𝔇.H X) = w :=
  Subtype.ext (by
    rw [FirstChernClassData.coe_projGrade, decompose_of_mem_same _ (SetLike.coe_mem _)])

/-- The untwisted trace `a ↦ λ(κ⁻¹(a_{2d}))` only sees the degree-`2d` part of `a`. -/
theorem untwistTrace_decompose (d : ℕ)
    (t : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) d →ₗ[F] F) (x : 𝔇.H X) :
    𝔇.untwistTrace X d t x =
      𝔇.untwistTrace X d t (decompose (𝔇.grade X) x (2 * (d : ℤ)) : 𝔇.H X) := by
  simp only [FirstChernClassData.untwistTrace, LinearMap.comp_apply]
  rw [← FirstChernClassData.coe_projGrade, projGrade_coe]

/-- `λ` is its untwisting read back through the coordinates. -/
theorem trace_eq_untwistTrace (d : ℕ)
    (t : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) d →ₗ[F] F)
    (v : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) d) :
    t v = 𝔇.untwistTrace X d t
      ((tateTwistCoordinates 𝔇.coord (d : ℤ) v : 𝔇.grade X (2 * (d : ℤ))) : 𝔇.H X) := by
  simp only [FirstChernClassData.untwistTrace, LinearMap.comp_apply, LinearEquiv.coe_coe,
    projGrade_coe, LinearEquiv.symm_apply_apply]

variable {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
    VectorBundleKZero ((toScheme k).obj X) → ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n}

end Weil

end Stacks.WeilDeRham

end
