module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.FirstChernClassSetup

/-!
# Axiom (A3) of a Weil cohomology theory from the projective bundle formula in each degree

Axiom (A3) of Weil Cohomology Theories, Section 0FID asks that for a smooth projective `X` over
`k`, a locally free `𝒪_X`-module `ℰ` of rank `r ≥ 1` and `p : P = 𝐏(ℰ) → X`, the map
`⨁_{i < r} H^*(X)(-i) → H^*(P)`, `(a_i) ↦ ∑ c₁^H(𝒪_P(1))^i ∪ p^*(a_i)`, is an isomorphism
(`Stacks.WeilCohomology.FirstChernClassData.ProjectiveBundleAxiom`). For de Rham cohomology the
projective bundle formula is proved one degree at a time ([Stacks, Tag 0FMT]): for every `n` the
map `⨁_{i < r} H^{n - 2i}(X) → H^n(P)` is bijective. This file shows that the degreewise statement
gives axiom (A3), for any data (D0), (D1), (D2').

For a map `φ : A → B` of `𝐙`-graded algebras and `ξ ∈ B^2`, the map `(a_i)_{i < r} ↦ ∑ ξ^i φ(a_i)`
from `A^r` to `B` sends the components `a_i^{n - 2i}` to the component of degree `n` of the image.
So it is bijective once its restrictions `∏_{i < r} A^{n - 2i} → B^n` are bijective for every `n`.
The Tate twists are removed using the coordinates `Stacks.WeilCohomology.FirstChernClassData.κ` on
the twists by the one-dimensional line `F(1)`.

## Main definitions

* `Stacks.WeilDeRham.sumPowMulMap`: the map `(a_i)_{i < r} ↦ ∑ ξ^i φ(a_i)`, `A^r → B`.
* `Stacks.WeilDeRham.degreewiseMap`: its restriction `∏_{i < r} A^{n - 2i} → B^n`.

## Main results

* `Stacks.WeilDeRham.bijective_sumPowMulMap_of_degreewise`: if every restriction
  `∏_{i < r} A^{n - 2i} → B^n` is bijective, so is `A^r → B`.
* `Stacks.WeilDeRham.projectiveBundleAxiom_of_bijective_bundleFormulaU`: axiom (A3) holds once its
  map, read in coordinates on the twists, is bijective. This is the converse of
  `Stacks.WeilCohomology.FirstChernClassData.bijective_bundleFormulaU`.
* `Stacks.WeilDeRham.projectiveBundleAxiom_of_degreewise`: axiom (A3) from the projective bundle
  formula in every degree.

## References

* [Stacks Project, Section 0FID](https://stacks.math.columbia.edu/tag/0FID)
* [Stacks Project, Tag 0FMT](https://stacks.math.columbia.edu/tag/0FMT)
-/

@[expose] public noncomputable section

open DirectSum

universe u w

namespace Stacks.WeilDeRham

/-! ### Graded linear algebra -/

section Graded

variable {F : Type*} [Field F] {A B : Type*} [Ring A] [Algebra F A] [Ring B] [Algebra F B]
  (𝒜 : ℤ → Submodule F A) [_root_.GradedAlgebra 𝒜] (ℬ : ℤ → Submodule F B) [_root_.GradedAlgebra ℬ]

/-- **The map `(a_i)_{i < r} ↦ ∑ ξ^i φ(a_i)`** from `A^r` to `B`. -/
def sumPowMulMap (φ : A →ₐ[F] B) (ξ : B) (r : ℕ) : (Fin r → A) →ₗ[F] B where
  toFun a := ∑ i : Fin r, ξ ^ (i : ℕ) * φ (a i)
  map_add' a b := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.smul_sum]

/-- The value of `Stacks.WeilDeRham.sumPowMulMap` at `(a_i)` is `∑ ξ^i φ(a_i)`. -/
theorem sumPowMulMap_apply (φ : A →ₐ[F] B) (ξ : B) (r : ℕ) (a : Fin r → A) :
    sumPowMulMap φ ξ r a = ∑ i : Fin r, ξ ^ (i : ℕ) * φ (a i) :=
  rfl

/-- The degrees `2i` and `n - 2i` add up to `n`. -/
private theorem nsmul_two_add_sub (n : ℤ) (i : ℕ) : i • (2 : ℤ) + (n - 2 * (i : ℤ)) = n := by
  rw [nsmul_eq_mul]; ring

variable {𝒜 ℬ}

/-- For `ξ ∈ B^2` and `a ∈ A^{n - 2i}`, the product `ξ^i φ(a)` lies in `B^n`. -/
theorem pow_mul_mem {φ : A →ₐ[F] B} (hφ : ∀ n, ∀ a ∈ 𝒜 n, φ a ∈ ℬ n) {ξ : B} (hξ : ξ ∈ ℬ 2)
    (n : ℤ) (i : ℕ) {a : A} (ha : a ∈ 𝒜 (n - 2 * (i : ℤ))) : ξ ^ i * φ a ∈ ℬ n := by
  have h := SetLike.mul_mem_graded (SetLike.pow_mem_graded i hξ) (hφ _ a ha)
  rwa [nsmul_two_add_sub] at h

variable (𝒜 ℬ)

/-- **The restriction `∏_{i < r} A^{n - 2i} → B^n` of `(a_i) ↦ ∑ ξ^i φ(a_i)`**, for `ξ ∈ B^2`. -/
def degreewiseMap {φ : A →ₐ[F] B} (hφ : ∀ n, ∀ a ∈ 𝒜 n, φ a ∈ ℬ n) {ξ : B} (hξ : ξ ∈ ℬ 2)
    (r : ℕ) (n : ℤ) (a : ∀ i : Fin r, 𝒜 (n - 2 * ((i : ℕ) : ℤ))) : ℬ n :=
  ⟨∑ i : Fin r, ξ ^ (i : ℕ) * φ (a i),
    Submodule.sum_mem _ fun i _ => pow_mul_mem hφ hξ n i (a i).2⟩

/-- The value of `Stacks.WeilDeRham.degreewiseMap` at `(a_i)`, read in `B`, is `∑ ξ^i φ(a_i)`. -/
theorem coe_degreewiseMap {φ : A →ₐ[F] B} (hφ : ∀ n, ∀ a ∈ 𝒜 n, φ a ∈ ℬ n) {ξ : B}
    (hξ : ξ ∈ ℬ 2) (r : ℕ) (n : ℤ) (a : ∀ i : Fin r, 𝒜 (n - 2 * ((i : ℕ) : ℤ))) :
    (degreewiseMap 𝒜 ℬ hφ hξ r n a : B) = ∑ i : Fin r, ξ ^ (i : ℕ) * φ (a i) :=
  rfl

/-- **The component of degree `n` of `∑ ξ^i φ(a_i)`** is `∑ ξ^i φ(a_i^{n - 2i})`. -/
theorem decompose_sumPowMulMap {φ : A →ₐ[F] B} (hφ : ∀ n, ∀ a ∈ 𝒜 n, φ a ∈ ℬ n) {ξ : B}
    (hξ : ξ ∈ ℬ 2) (r : ℕ) (a : Fin r → A) (n : ℤ) :
    (decompose ℬ (sumPowMulMap φ ξ r a) n : B) =
      ∑ i : Fin r, ξ ^ (i : ℕ) * φ (decompose 𝒜 (a i) (n - 2 * ((i : ℕ) : ℤ))) := by
  rw [sumPowMulMap_apply, decompose_sum, DFinsupp.finset_sum_apply, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := coe_decompose_mul_add_of_left_mem ℬ (b := φ (a i)) (j := n - 2 * ((i : ℕ) : ℤ))
    (SetLike.pow_mem_graded (i : ℕ) hξ)
  rw [nsmul_two_add_sub] at h
  rw [h, Stacks.WeilCohomology.decompose_map 𝒜 ℬ φ hφ]

/-- **Injectivity from injectivity in every degree.** -/
theorem injective_sumPowMulMap_of_degreewise {φ : A →ₐ[F] B}
    (hφ : ∀ n, ∀ a ∈ 𝒜 n, φ a ∈ ℬ n) {ξ : B} (hξ : ξ ∈ ℬ 2) (r : ℕ)
    (h : ∀ n, Function.Injective (degreewiseMap 𝒜 ℬ hφ hξ r n)) :
    Function.Injective (sumPowMulMap φ ξ r) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  have hc : ∀ (n : ℤ) (i : Fin r),
      (decompose 𝒜 (a i) (n - 2 * ((i : ℕ) : ℤ)) : A) = 0 := by
    intro n
    have h0 : degreewiseMap 𝒜 ℬ hφ hξ r n (fun i => decompose 𝒜 (a i) (n - 2 * ((i : ℕ) : ℤ))) =
        degreewiseMap 𝒜 ℬ hφ hξ r n 0 := by
      apply Subtype.ext
      rw [coe_degreewiseMap, coe_degreewiseMap, ← decompose_sumPowMulMap 𝒜 ℬ hφ hξ r a n, ha]
      simp
    intro i
    exact congrArg Subtype.val (congrFun (h n h0) i)
  funext i
  apply (decompose 𝒜).injective
  refine DFinsupp.ext fun m => Subtype.ext ?_
  have := hc (m + 2 * ((i : ℕ) : ℤ)) i
  rw [add_sub_cancel_right] at this
  simpa using this

/-- **Surjectivity from surjectivity in every degree.** -/
theorem surjective_sumPowMulMap_of_degreewise {φ : A →ₐ[F] B}
    (hφ : ∀ n, ∀ a ∈ 𝒜 n, φ a ∈ ℬ n) {ξ : B} (hξ : ξ ∈ ℬ 2) (r : ℕ)
    (h : ∀ n, Function.Surjective (degreewiseMap 𝒜 ℬ hφ hξ r n)) :
    Function.Surjective (sumPowMulMap φ ξ r) := by
  classical
  intro b
  choose c hc using fun n => h n (decompose ℬ b n)
  refine ⟨∑ n ∈ (decompose ℬ b).support, fun i => (c n i : A), ?_⟩
  conv_rhs => rw [← sum_support_decompose ℬ b]
  rw [map_sum]
  exact Finset.sum_congr rfl fun n _ => congrArg Subtype.val (hc n)

/-- **Bijectivity from bijectivity in every degree**: if for every `n` the map
`∏_{i < r} A^{n - 2i} → B^n`, `(a_i) ↦ ∑ ξ^i φ(a_i)`, is bijective, then so is
`A^r → B`, `(a_i) ↦ ∑ ξ^i φ(a_i)`. -/
theorem bijective_sumPowMulMap_of_degreewise {φ : A →ₐ[F] B}
    (hφ : ∀ n, ∀ a ∈ 𝒜 n, φ a ∈ ℬ n) {ξ : B} (hξ : ξ ∈ ℬ 2) (r : ℕ)
    (h : ∀ n, Function.Bijective (degreewiseMap 𝒜 ℬ hφ hξ r n)) :
    Function.Bijective (sumPowMulMap φ ξ r) :=
  ⟨injective_sumPowMulMap_of_degreewise 𝒜 ℬ hφ hξ r fun n => (h n).1,
    surjective_sumPowMulMap_of_degreewise 𝒜 ℬ hφ hξ r fun n => (h n).2⟩

end Graded

/-! ### Axiom (A3) -/

section Axiom

open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] (𝔇 : FirstChernClassData k F)

/-- **Axiom (A3) from its map in coordinates.** If for every `X`, `ℰ` locally free of rank
`r + 1` and `p : P = 𝐏(ℰ) → X` the map `H^*(X)^{r+1} → H^*(P)`, `(a_i) ↦ ∑ ξ^i ∪ p^*(a_i)`, is
bijective, `ξ` being `c₁^H(𝒪_P(1))` read in the coordinates on `H^*(P)(1)`, then axiom (A3)
holds. -/
theorem projectiveBundleAxiom_of_bijective_bundleFormulaU
    (h : ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (E : ((toScheme k).obj X).Modules)
      (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)],
      Function.Bijective fun a : Fin (r + 1) → 𝔇.H X =>
        ∑ i : Fin (r + 1), 𝔇.bundleClassU X E r ^ (i : ℕ) * 𝔇.pull (bundleProj X E r) (a i)) :
    𝔇.ProjectiveBundleAxiom := by
  intro X E r hE
  have key : 𝔇.bundleFormula X E r =
      (𝔇.κ _ 0).symm ∘ (fun a : Fin (r + 1) → 𝔇.H X =>
        ∑ i : Fin (r + 1), 𝔇.bundleClassU X E r ^ (i : ℕ) * 𝔇.pull (bundleProj X E r) (a i)) ∘
        fun a i => 𝔇.κ X (-(i : ℤ)) (a i) := by
    funext a
    rw [Function.comp_apply, Function.comp_apply, ← 𝔇.κ_bundleFormula, LinearEquiv.symm_apply_apply]
  rw [key]
  refine (𝔇.κ _ 0).symm.bijective.comp ((h X E r).comp ?_)
  exact ⟨fun a b hab => funext fun i => (𝔇.κ X _).injective (congrFun hab i),
    fun b => ⟨fun i => (𝔇.κ X _).symm (b i), funext fun i => by simp⟩⟩

/-- **Axiom (A3) from the projective bundle formula in every degree.** If for every `X`, `ℰ`
locally free of rank `r + 1`, `p : P = 𝐏(ℰ) → X` and every degree `n` the map
`∏_{i ≤ r} H^{n - 2i}(X) → H^n(P)`, `(a_i) ↦ ∑ ξ^i ∪ p^*(a_i)`, is bijective, `ξ` being
`c₁^H(𝒪_P(1))` read in coordinates, then axiom (A3) holds. -/
theorem projectiveBundleAxiom_of_degreewise
    (h : ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (E : ((toScheme k).obj X).Modules)
      (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)]
      (n : ℤ), Function.Bijective (degreewiseMap (𝔇.grade X) (𝔇.grade (bundle X E r))
        (𝔇.pull_grade (bundleProj X E r)) (𝔇.bundleClassU_mem X E r) (r + 1) n)) :
    𝔇.ProjectiveBundleAxiom :=
  projectiveBundleAxiom_of_bijective_bundleFormulaU 𝔇 fun X E r _ =>
    bijective_sumPowMulMap_of_degreewise _ _ _ _ (r + 1) (h X E r)

end Axiom

end Stacks.WeilDeRham

end
