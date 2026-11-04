module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.RingTheory.AugmentationIdealGraded

/-!
# Base change of the polynomials of large degree: `𝔪ⁿ ⊗_A B = 𝔪ⁿ_B`

Let `A → B` be a ring map, let `σ` be a type and let `𝔪 = (X_s; s ∈ σ)` be the ideal of the
variables of `MvPolynomial σ A`. Its `n`-th power, read as an `A`-module, is
`MvPolynomial.degreeGE σ A n`, the span of the monomials of total degree at least `n`
(`MvPolynomial.restrictScalars_span_range_X_pow`), and it is free on exactly those monomials
(`MvPolynomial.basisDegreeGE`).

This file proves that the comparison map

`B ⊗_A 𝔪ⁿ ⟶ 𝔪ⁿ_B`

induced by `MvPolynomial.map (algebraMap A B)` on coefficients is an isomorphism, and that the
isomorphisms are compatible with the inclusions `𝔪ᵐ ⊆ 𝔪ⁿ` for `n ≤ m`.

## Main definitions

* `MvPolynomial.degreeGEMap`: the `A`-linear map `𝔪ⁿ ⟶ 𝔪ⁿ_B` given by `map (algebraMap A B)`.
* `MvPolynomial.degreeGEBaseChange`: its base change `B ⊗_A 𝔪ⁿ ⟶ 𝔪ⁿ_B`.
* `MvPolynomial.degreeGEBaseChangeEquiv`: **the normal form** `B ⊗_A 𝔪ⁿ ≃ₗ[B] 𝔪ⁿ_B`.

## Main results

* `MvPolynomial.bijective_degreeGEBaseChange`: the comparison map is bijective.
* `MvPolynomial.degreeGEBaseChange_comp_baseChange_inclusion`: the comparison maps commute with
  the inclusions `𝔪ᵐ ⊆ 𝔪ⁿ`.

## References

* [Stacks Project, Tag 08RF](https://stacks.math.columbia.edu/tag/08RF)
* [Stacks Project, Tag 08RE](https://stacks.math.columbia.edu/tag/08RE)
-/

@[expose] public noncomputable section

open TensorProduct

namespace MvPolynomial

variable {A : Type*} [CommRing A] {B : Type*} [CommRing B] [Algebra A B] (σ : Type*)

/-! ### The monomial basis, by its values -/

variable (A) in
/-- The monomial basis of `degreeGE σ A n` takes the multidegree `d` to the monomial `X^d`. -/
@[simp]
theorem coe_basisDegreeGE (n : ℕ) (d : {d : σ →₀ ℕ // n ≤ d.degree}) :
    ((basisDegreeGE σ A n d : degreeGE σ A n) : MvPolynomial σ A) =
      monomial (d : σ →₀ ℕ) 1 := by
  simp [basisDegreeGE, Module.Basis.span_apply]

/-! ### `degreeGE` is antitone -/

variable (A) in
/-- The polynomials all of whose monomials have degree at least `m` are among those all of whose
monomials have degree at least `n`, for `n ≤ m`. -/
theorem degreeGE_antitone {n m : ℕ} (h : n ≤ m) : degreeGE σ A m ≤ degreeGE σ A n :=
  fun _ hp d hd => h.trans (hp d hd)

/-! ### The comparison map -/

/-- `map (algebraMap A B)` carries a polynomial all of whose monomials have degree at least `n`
to one with the same property. -/
theorem map_mem_degreeGE {n : ℕ} {p : MvPolynomial σ A} (hp : p ∈ degreeGE σ A n) :
    map (algebraMap A B) p ∈ degreeGE σ B n :=
  fun d hd => hp d (support_map_subset _ _ hd)

variable (A B) in
/-- **The comparison map `𝔪ⁿ ⟶ 𝔪ⁿ_B`**, `A`-linear, given by `map (algebraMap A B)` on
coefficients. -/
def degreeGEMap (n : ℕ) : degreeGE σ A n →ₗ[A] degreeGE σ B n where
  toFun p := ⟨map (algebraMap A B) (p : MvPolynomial σ A), map_mem_degreeGE σ p.2⟩
  map_add' _ _ := Subtype.ext (map_add (MvPolynomial.map (algebraMap A B)) _ _)
  map_smul' a p := Subtype.ext
    ((mapAlgHom (R := A) (σ := σ) (Algebra.ofId A B)).toLinearMap.map_smul a
      (p : MvPolynomial σ A))

/-- The comparison map `𝔪ⁿ ⟶ 𝔪ⁿ_B` sends `p` to `map (algebraMap A B) p`. -/
@[simp]
theorem coe_degreeGEMap_apply (n : ℕ) (p : degreeGE σ A n) :
    ((degreeGEMap A B σ n p : degreeGE σ B n) : MvPolynomial σ B) =
      map (algebraMap A B) (p : MvPolynomial σ A) :=
  rfl

variable (A B) in
/-- **The base change of the comparison map**, `B ⊗_A 𝔪ⁿ ⟶ 𝔪ⁿ_B`. -/
def degreeGEBaseChange (n : ℕ) : B ⊗[A] (degreeGE σ A n) →ₗ[B] degreeGE σ B n :=
  (degreeGEMap A B σ n).liftBaseChange B

/-- The base-changed comparison map sends `b ⊗ₜ p` to `b` times the image of `p` under
`MvPolynomial.degreeGEMap`. -/
@[simp]
theorem degreeGEBaseChange_tmul (n : ℕ) (b : B) (p : degreeGE σ A n) :
    degreeGEBaseChange A B σ n (b ⊗ₜ p) = b • degreeGEMap A B σ n p :=
  rfl

/-- The comparison map carries the monomial basis of `B ⊗_A 𝔪ⁿ` to that of `𝔪ⁿ_B`. -/
theorem degreeGEBaseChange_basisDegreeGE_baseChange (n : ℕ)
    (d : {d : σ →₀ ℕ // n ≤ d.degree}) :
    degreeGEBaseChange A B σ n ((basisDegreeGE σ A n).baseChange B d) = basisDegreeGE σ B n d := by
  rw [Module.Basis.baseChange_apply, degreeGEBaseChange_tmul, one_smul]
  exact Subtype.ext (by simp)

/-- **The comparison map `B ⊗_A 𝔪ⁿ ⟶ 𝔪ⁿ_B` is bijective.** -/
theorem bijective_degreeGEBaseChange (n : ℕ) :
    Function.Bijective (degreeGEBaseChange A B σ n) := by
  let e := ((basisDegreeGE σ A n).baseChange B).equiv (basisDegreeGE σ B n) (Equiv.refl _)
  have h : degreeGEBaseChange A B σ n = e.toLinearMap := by
    refine ((basisDegreeGE σ A n).baseChange B).ext fun d => ?_
    rw [degreeGEBaseChange_basisDegreeGE_baseChange, LinearEquiv.coe_coe,
      Module.Basis.equiv_apply, Equiv.refl_apply]
  rw [h]
  exact e.bijective

variable (A B) in
/-- **The normal form `B ⊗_A 𝔪ⁿ ≃ₗ[B] 𝔪ⁿ_B`**: the `n`-th power of the ideal of the variables of
`MvPolynomial σ B` is the base change along `A → B` of the `n`-th power of the ideal of the
variables of `MvPolynomial σ A`. -/
def degreeGEBaseChangeEquiv (n : ℕ) : B ⊗[A] (degreeGE σ A n) ≃ₗ[B] degreeGE σ B n :=
  LinearEquiv.ofBijective (degreeGEBaseChange A B σ n) (bijective_degreeGEBaseChange σ n)

/-! ### Compatibility with the inclusions `𝔪ᵐ ⊆ 𝔪ⁿ` -/

/-- **The normal form is compatible with the filtration**: for `n ≤ m` the square relating the
comparison maps at `m` and at `n` with the inclusions `𝔪ᵐ ⊆ 𝔪ⁿ` commutes. -/
theorem degreeGEBaseChange_comp_baseChange_inclusion {n m : ℕ} (h : n ≤ m) :
    (degreeGEBaseChange A B σ n).comp
        (LinearMap.baseChange B (Submodule.inclusion (degreeGE_antitone A σ h))) =
      (Submodule.inclusion (degreeGE_antitone B σ h)).comp (degreeGEBaseChange A B σ m) := by
  refine TensorProduct.AlgebraTensorModule.curry_injective ?_
  refine LinearMap.ext fun b => LinearMap.ext fun p => ?_
  exact Subtype.ext (by simp)

end MvPolynomial

end
