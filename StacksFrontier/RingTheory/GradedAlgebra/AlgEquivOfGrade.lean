module

public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Isomorphisms of graded algebras from isomorphisms of their pieces

Let `A = ⨁ᵢ 𝒜ᵢ` and `B = ⨁ᵢ ℬᵢ` be graded `R`-algebras. A family of linear isomorphisms
`eᵢ : 𝒜ᵢ ≃ ℬᵢ` which is multiplicative on homogeneous elements and sends `1` to `1` assembles to
an isomorphism of algebras `A ≃ B` carrying `𝒜ᵢ` onto `ℬᵢ`
(`GradedAlgebra.algEquivOfGrade`).

## Main definitions

* `GradedAlgebra.algEquivOfGrade`: the assembled isomorphism.

## Main results

* `GradedAlgebra.algEquivOfGrade_apply_of_mem`: on `𝒜ᵢ` it is `eᵢ`.
* `GradedAlgebra.map_algEquivOfGrade`: it carries `𝒜ᵢ` onto `ℬᵢ`.
-/

@[expose] public noncomputable section

namespace GradedAlgebra

open DirectSum

variable {ι R A B : Type*} [DecidableEq ι] [AddMonoid ι] [CommSemiring R] [Semiring A]
  [Algebra R A] [Semiring B] [Algebra R B] {𝒜 : ι → Submodule R A} {ℬ : ι → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

/-- The linear isomorphism `A ≃ B` assembled from isomorphisms `𝒜ᵢ ≃ ℬᵢ` of the pieces. -/
def linearEquivOfGrade (e : ∀ i, 𝒜 i ≃ₗ[R] ℬ i) : A ≃ₗ[R] B :=
  (decomposeLinearEquiv 𝒜).trans
    ((DFinsupp.mapRange.linearEquiv e).trans (decomposeLinearEquiv ℬ).symm)

/-- On an element `a ∈ 𝒜ᵢ`, the assembled linear isomorphism `linearEquivOfGrade e` is `eᵢ`. -/
theorem linearEquivOfGrade_apply_of_mem (e : ∀ i, 𝒜 i ≃ₗ[R] ℬ i) {i : ι} {a : A}
    (ha : a ∈ 𝒜 i) : linearEquivOfGrade e a = e i ⟨a, ha⟩ := by
  simp only [linearEquivOfGrade, LinearEquiv.trans_apply, decomposeLinearEquiv_apply,
    decompose_of_mem 𝒜 ha]
  rw [show (DFinsupp.mapRange.linearEquiv e) (DirectSum.of (fun i ↦ 𝒜 i) i ⟨a, ha⟩) =
      DirectSum.of (fun i ↦ ℬ i) i (e i ⟨a, ha⟩) from DFinsupp.mapRange_single (hf := by simp)]
  exact decompose_symm_of (ℳ := ℬ) (e i ⟨a, ha⟩)

/-- **The isomorphism of graded algebras assembled from isomorphisms of the pieces**, when these
are multiplicative on homogeneous elements and send `1` to `1`. -/
def algEquivOfGrade (e : ∀ i, 𝒜 i ≃ₗ[R] ℬ i)
    (hmul : ∀ i j (a : 𝒜 i) (b : 𝒜 j),
      (e (i + j) ⟨a * b, SetLike.GradedMul.mul_mem a.2 b.2⟩ : B) = e i a * e j b)
    (hone : (e 0 ⟨1, SetLike.GradedOne.one_mem⟩ : B) = 1) : A ≃ₐ[R] B :=
  AlgEquiv.ofLinearEquiv (linearEquivOfGrade e)
    (by rw [linearEquivOfGrade_apply_of_mem e SetLike.GradedOne.one_mem, hone])
    (by
      intro x y
      induction x using DirectSum.Decomposition.inductionOn 𝒜 with
      | zero => simp
      | add x x' hx hx' => simp only [add_mul, map_add, hx, hx']
      | homogeneous hx =>
        induction y using DirectSum.Decomposition.inductionOn 𝒜 with
        | zero => simp
        | add y y' hy hy' => simp only [mul_add, map_add, hy, hy']
        | homogeneous hy =>
          rw [linearEquivOfGrade_apply_of_mem e (SetLike.GradedMul.mul_mem hx.2 hy.2),
            linearEquivOfGrade_apply_of_mem e hx.2, linearEquivOfGrade_apply_of_mem e hy.2]
          exact hmul _ _ ⟨_, hx.2⟩ ⟨_, hy.2⟩)

/-- On an element `a ∈ 𝒜ᵢ`, the assembled algebra isomorphism `algEquivOfGrade e hmul hone` is
`eᵢ`. -/
theorem algEquivOfGrade_apply_of_mem (e : ∀ i, 𝒜 i ≃ₗ[R] ℬ i) (hmul) (hone) {i : ι} {a : A}
    (ha : a ∈ 𝒜 i) : algEquivOfGrade e hmul hone a = e i ⟨a, ha⟩ :=
  linearEquivOfGrade_apply_of_mem e ha

/-- The assembled isomorphism carries `𝒜ᵢ` onto `ℬᵢ`. -/
theorem map_algEquivOfGrade (e : ∀ i, 𝒜 i ≃ₗ[R] ℬ i) (hmul) (hone) (i : ι) :
    (𝒜 i).map (algEquivOfGrade e hmul hone).toLinearMap = ℬ i := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [AlgEquiv.toLinearMap_apply, algEquivOfGrade_apply_of_mem e hmul hone ha]
    exact (e i ⟨a, ha⟩).2
  · intro hb
    obtain ⟨a, ha⟩ := (e i).surjective ⟨b, hb⟩
    refine ⟨a, a.2, ?_⟩
    rw [AlgEquiv.toLinearMap_apply, algEquivOfGrade_apply_of_mem e hmul hone a.2, ha]

end GradedAlgebra

end
