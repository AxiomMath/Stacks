module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.BoundedDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentKZeroDimensionFiltration
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs
public import StacksCore.Tactic.StacksAttribute

/-!
# Chow homology and the dimension-graded pieces of coherent K-theory

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X ⟶ Y` be a closed
immersion of schemes locally of finite type over `S` with `Y` regular and quasi-compact, and
write `A_k(X) = CH_k(X)`. Proposition 42.57.1 says that the composition

  `K'₀(X) ⟶ K₀(D_{X, perf}(𝒪_Y)) ⟶ A^*(X ⟶ Y) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐`

of the map `ℱ ↦ ℱ[0]`, the localized Chern character `ch(X ⟶ Y, -)` and the cap product
`c ↦ c ∩ [Y]` induces an isomorphism `K'₀(X) ⊗ 𝐐 ≅ CH_*(X) ⊗ 𝐐`, and that the canonical map
`CH_k(X) ⊗ 𝐐 ⟶ gr_k K'₀(X) ⊗ 𝐐` is an isomorphism for every `k`.

The composition is a hypothesis `ch`, the canonical maps `CH_k(X) ⟶ gr_k K'₀(X)` are a hypothesis
`cls`, and `ch` is assumed to satisfy the two conditions (1) and (2) of the proof of the
proposition; from these, the injectivity of the latter map and the surjectivity of the former are
proved. Here `CH_k(X) ⊗ 𝐐` is `TensorProduct ℤ ℚ (Stacks.Chow.chowGroup C f k)` and `gr_k K'₀(X)`
is `Stacks.Chow.gradedCoherentKZero`, the graded piece of the filtration by dimension of supports.

## Main results

* `Stacks.Chow.chowToGradedCoherentKZero_injective`: injectivity of
  `CH_k(X) ⊗ 𝐐 ⟶ gr_k K'₀(X) ⊗ 𝐐`.
* `Stacks.Chow.rationalCoherentKZeroToChowHomology_surjective`: surjectivity of
  `K'₀(X) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐`.
* `Stacks.Chow.surjective_of_exists_triangular_preimage`: a linear map into a `ℤ`-graded module is
  surjective as soon as the graded pieces vanish below some degree and every element of every
  graded piece has a preimage with no component in a higher degree.

## References

* [Stacks Project, Tag 0FEW](https://stacks.math.columbia.edu/tag/0FEW)
* [Stacks Project, Tag 0FEV](https://stacks.math.columbia.edu/tag/0FEV)
* [Stacks Project, Tag 0FEQ](https://stacks.math.columbia.edu/tag/0FEQ)
* [Stacks Project, Tag 0FDS](https://stacks.math.columbia.edu/tag/0FDS)
* [Stacks Project, Tag 02S9](https://stacks.math.columbia.edu/tag/02S9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- A linear map into a `ℤ`-graded module is surjective as soon as the graded pieces vanish in
every degree below some `lo`, and every element of every graded piece is the degree `k`
component of an element of the image all of whose components in degrees above `k` vanish. -/
theorem surjective_of_exists_triangular_preimage
    {R : Type*} [Semiring R] {V : Type*} [AddCommGroup V] [Module R V]
    {M : ℤ → Type*} [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)]
    (θ : V →ₗ[R] DirectSum ℤ M) (lo : ℤ)
    (hlo : ∀ j : ℤ, j < lo → ∀ m : M j, m = 0)
    (hsurj : ∀ (k : ℤ) (m : M k), ∃ v : V, θ v k = m ∧ ∀ j : ℤ, k < j → θ v j = 0) :
    Function.Surjective θ := by
  have key : ∀ n : ℕ, ∀ y : DirectSum ℤ M,
      (∀ j : ℤ, lo + (n : ℤ) ≤ j → y j = 0) → y ∈ LinearMap.range θ := by
    intro n
    induction n with
    | zero =>
      intro y hy
      have hy0 : y = 0 := by
        refine DFinsupp.ext fun j ↦ ?_
        rcases lt_or_ge j lo with h | h
        · exact hlo j h _
        · exact hy j (by simpa using h)
      exact ⟨0, by simp [hy0]⟩
    | succ n ih =>
      intro y hy
      obtain ⟨v, hv1, hv2⟩ := hsurj (lo + (n : ℤ)) (y (lo + (n : ℤ)))
      obtain ⟨w, hw⟩ := ih (y - θ v) fun j hj ↦ by
        obtain rfl | h := hj.eq_or_lt
        · simp [hv1]
        · simp [hy j (by lia), hv2 j h]
      exact ⟨w + v, by rw [map_add, hw]; abel⟩
  intro y
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ∀ j : ℤ, lo + (n : ℤ) ≤ j → y j = 0 := by
    induction y using DirectSum.induction_on with
    | zero => exact ⟨0, fun j _ ↦ rfl⟩
    | of i m => exact ⟨(i - lo + 1).toNat, fun j hj ↦ DirectSum.of_eq_of_ne _ _ _ (by lia)⟩
    | add x y hx hy =>
      obtain ⟨n₁, h₁⟩ := hx
      obtain ⟨n₂, h₂⟩ := hy
      exact ⟨max n₁ n₂, fun j hj ↦ by simp [h₁ j (by lia), h₂ j (by lia)]⟩
  exact key n y hn

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  [IsLocallyNoetherian X]

/-- The canonical map `CH_k(X) ⊗ 𝐐 ⟶ gr_k K'₀(X) ⊗ 𝐐` is injective, for a homomorphism
`ch : K'₀(X) → CH_*(X) ⊗ 𝐐` such that the class of a coherent module whose support has
delta-dimension at most `j` has vanishing components in degrees above `j` (`hch_triangular`), and
the degree `k` component of a lift to `F_k K'₀(X)` of `cls k α` is `1 ⊗ α` (`hch_diagonal`). -/
@[stacks 0FEW "injectivity of the canonical map `CH_k(X) ⊗ 𝐐 ⟶ gr_k K'₀(X) ⊗ 𝐐`; the \
  composition `K'₀(X) → K₀(D_{X, perf}(𝒪_Y)) → A^*(X ⟶ Y) ⊗ 𝐐 → CH_*(X) ⊗ 𝐐`, the canonical \
  maps of Lemma 42.23.4, and the two conditions (1) and (2) that the proof establishes for the \
  composition and reduces the proposition to, are hypotheses: none of the three legs of the \
  composition is constructed in this repository, `A^*` carrying no multiplication"]
theorem chowToGradedCoherentKZero_injective
    (ch : CoherentKZero X →+ DirectSum ℤ fun j => TensorProduct ℤ ℚ (chowGroup C f j))
    (hch_triangular : ∀ (j j' : ℤ) (F : CoherentModulesDimLE C f j), j < j' →
      ch (KZero.mk _ F.obj) j' = 0)
    (cls : ∀ j : ℤ, chowGroup C f j →+ gradedCoherentKZero C f j) (k : ℤ)
    (hch_diagonal : ∀ (α : chowGroup C f k) (x : coherentKZeroFiltration C f k),
      toGradedCoherentKZero C f k x = cls k α →
        ch (x : CoherentKZero X) k = (1 : ℚ) ⊗ₜ[ℤ] α) :
    Function.Injective
      (TensorProduct.map (LinearMap.id : ℚ →ₗ[ℤ] ℚ) (cls k).toIntLinearMap) := by
  let θ : CoherentKZero X →+ TensorProduct ℤ ℚ (chowGroup C f k) :=
    { toFun := fun x ↦ ch x k
      map_zero' := by simp
      map_add' := fun x y ↦ by simp }
  let ψ : gradedCoherentKZero C f k →+ TensorProduct ℤ ℚ (chowGroup C f k) :=
    gradedCoherentKZeroLift C f k (θ.comp (coherentKZeroFiltration C f k).subtype)
      fun _ hx ↦ coherentKZeroFiltration_le_ker C f θ (k - 1)
        (fun F ↦ hch_triangular (k - 1) k F (by lia)) hx
  have hψ : ∀ α : chowGroup C f k, ψ (cls k α) = (1 : ℚ) ⊗ₜ[ℤ] α := fun α ↦ by
    obtain ⟨x, hx⟩ := toGradedCoherentKZero_surjective C f k (cls k α)
    rw [← hx]
    exact hch_diagonal α x hx
  let B : ℚ →ₗ[ℤ] gradedCoherentKZero C f k →ₗ[ℤ] TensorProduct ℤ ℚ (chowGroup C f k) :=
    { toFun := fun q ↦ q • ψ.toIntLinearMap
      map_add' := fun q q' ↦ add_smul q q' _
      map_smul' := fun c q ↦ by rw [smul_assoc, RingHom.id_apply] }
  have key : ∀ z : TensorProduct ℤ ℚ (chowGroup C f k),
      TensorProduct.lift B (TensorProduct.map (LinearMap.id : ℚ →ₗ[ℤ] ℚ)
        (cls k).toIntLinearMap z) = z := by
    intro z
    induction z with
    | tmul q α =>
      rw [TensorProduct.map_tmul, TensorProduct.lift.tmul]
      show q • ψ (cls k α) = q ⊗ₜ[ℤ] α
      rw [hψ, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add z w hz hw => rw [map_add, map_add, hz, hw]
  exact Function.LeftInverse.injective key

/-- A homomorphism `ch : K'₀(X) → CH_*(X) ⊗ 𝐐` satisfying the conditions `hch_triangular` and
`hch_diagonal` of `Stacks.Chow.chowToGradedCoherentKZero_injective` (the latter in every degree)
becomes surjective after tensoring the source with `𝐐`, provided `δ_{X/S}` is bounded below. -/
@[stacks 0FEW "surjectivity of the composition `K'₀(X) ⊗ 𝐐 → CH_*(X) ⊗ 𝐐`; as for the \
  injectivity statement in this file the composition, the canonical maps of Lemma 42.23.4 and \
  the two conditions (1) and (2) that the proof establishes for the composition are \
  hypotheses, none of the three legs of the composition being constructed in this repository; \
  the injectivity of the composition is not proved, needing the surjectivity of the canonical \
  maps and hence the unformalized half of Tag 02S9"]
theorem rationalCoherentKZeroToChowHomology_surjective
    (ch : CoherentKZero X →+ DirectSum ℤ fun j => TensorProduct ℤ ℚ (chowGroup C f j))
    (hch_triangular : ∀ (j j' : ℤ) (F : CoherentModulesDimLE C f j), j < j' →
      ch (KZero.mk _ F.obj) j' = 0)
    (cls : ∀ j : ℤ, chowGroup C f j →+ gradedCoherentKZero C f j)
    (hch_diagonal : ∀ (k : ℤ) (α : chowGroup C f k) (x : coherentKZeroFiltration C f k),
      toGradedCoherentKZero C f k x = cls k α →
        ch (x : CoherentKZero X) k = (1 : ℚ) ⊗ₜ[ℤ] α)
    (lo : ℤ) (hlo : ∀ x : X, lo ≤ relativeDimension C.dimensionFunction f x) :
    Function.Surjective (ch.toIntLinearMap.liftBaseChange ℚ) := by
  have htri : ∀ (k j : ℤ), k < j → ∀ z ∈ coherentKZeroFiltration C f k, ch z j = 0 :=
    fun k j hkj z hz ↦ by
      simpa using coherentKZeroFiltration_le_ker C f
        ({ toFun := fun w ↦ ch w j, map_zero' := by simp, map_add' := fun _ _ ↦ by simp } :
          CoherentKZero X →+ TensorProduct ℤ ℚ (chowGroup C f j)) k
        (fun F ↦ hch_triangular k j F hkj) hz
  refine surjective_of_exists_triangular_preimage _ lo ?_ ?_
  · intro j hj m
    induction m with
    | tmul q α =>
      rw [chowGroup_eq_zero C f (fun x ↦ by have := hlo x; lia) α, TensorProduct.tmul_zero]
    | add a b ha hb => rw [ha, hb, add_zero]
  · intro k m
    induction m with
    | tmul q α =>
      obtain ⟨x, hx⟩ := toGradedCoherentKZero_surjective C f k (cls k α)
      refine ⟨q ⊗ₜ[ℤ] (x : CoherentKZero X), ?_, fun j hj ↦ ?_⟩
      · rw [LinearMap.liftBaseChange_tmul]
        show q • (ch (x : CoherentKZero X)) k = _
        rw [hch_diagonal k α x hx, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      · rw [LinearMap.liftBaseChange_tmul]
        show q • (ch (x : CoherentKZero X)) j = 0
        rw [htri k j hj _ x.2, smul_zero]
    | add a b ha hb =>
      obtain ⟨v, hv1, hv2⟩ := ha
      obtain ⟨w, hw1, hw2⟩ := hb
      exact ⟨v + w, by simp [hv1, hw1], fun j hj ↦ by simp [hv2 j hj, hw2 j hj]⟩

end Stacks.Chow

end
