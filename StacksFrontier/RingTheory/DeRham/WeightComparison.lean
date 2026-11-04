module

public import StacksFrontier.RingTheory.DeRham.LaurentResidue
public import StacksFrontier.RingTheory.Kaehler.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# The three weight comparisons for the total space of a line bundle

Let `R` be a commutative ring and `A` an `R`-algebra.  Over a trivializing affine the total space
of a line bundle on `Spec A` is `Spec A[X]` and the complement of its zero section is
`Spec A[T;T⁻¹]`, both graded by the degree of the fibre coordinate.  This file proves the three
affine local statements behind Stacks 0FUH, each a comparison of weight components of de Rham
complexes:

1. multiplication by `Tⁿ` is an isomorphism from the weight-zero part of `Ω^p_{A[T;T⁻¹]/R}` onto
   its weight-`n` part, for every integer `n`;
2. the weight-zero part of the de Rham complex of `A[X]` over `R` is the de Rham complex of `A`
   over `R`;
3. for `n > 0` the restriction of forms along `A[X] → A[T;T⁻¹]` carries the weight-`n` part of
   `Ω^p_{A[X]/R}` isomorphically onto the weight-`n` part of `Ω^p_{A[T;T⁻¹]/R}`.

The first is immediate from the explicit description of the weight components of
`Ω^p_{A[T;T⁻¹]/R}`, which is available at every weight.  The other two need its polynomial
counterpart, which is proved here: a form of weight `n` on `A[X]` is `Xⁿ ω'` for `n = 0`, and
`Xⁿ ω' + X^{n-1} dX ∧ ω` for `n > 0`, with `ω'` and `ω` pulled back from `A`.  Clause (2) is the
case `n = 0`, where the `dX`-summand is absent because `dX` has weight one; clause (3) compares
the two descriptions, `X^{n-1} dX` and `Tⁿ dlog T` being the same form.

## Main definitions

* `PolynomialDeRham.weightGrading`: the grading of `A[X]` by the degree of `X`.
* `PolynomialDeRham.weightComponent`: the weight-`n` component of `Ω^p_{A[X]/R}`, namely the
  graded component of differential forms of Stacks 0FU9 for that grading.
* `PolynomialDeRham.weightForms`: the explicit description `Xⁿ ω' + X^{n-1} dX ∧ ω` of the
  weight-`n` forms, built from `PolynomialDeRham.weightPullback` and
  `PolynomialDeRham.weightDX`.
* `PolynomialDeRham.deRhamComplexWeightZero`: the weight-zero de Rham complex `Ω^•_{A[X]/R,0}`,
  as a `CochainComplex (ModuleCat R) ℕ`, and `PolynomialDeRham.inclWeightZero` the pullback of
  forms into it.
* `LaurentDeRham.smulTEquiv`: multiplication by `Tⁿ` on `Ω^p_{A[T;T⁻¹]/R}`, an automorphism.

## Main results

* `LaurentDeRham.weightComponentSmulEquiv`: **clause (1)**, multiplication by `Tⁿ` is an
  isomorphism `Ω^p_{A[T;T⁻¹]/R,0} ≅ Ω^p_{A[T;T⁻¹]/R,n}` for every `n : ℤ`, with
  `LaurentDeRham.map_smulTEquiv_weightComponent` the underlying statement about submodules.
* `PolynomialDeRham.weightComponent_eq_weightForms`: the weight components of `Ω^p_{A[X]/R}`,
  explicitly.
* `PolynomialDeRham.deRhamComplexWeightZeroIso`: **clause (2)**, `Ω^•_{A/R} ≅ Ω^•_{A[X]/R,0}` as
  complexes of `R`-modules, through the pullback of forms.
* `PolynomialDeRham.laurentWeightEquiv`: **clause (3)**, for `n > 0` the restriction of forms
  along `A[X] → A[T;T⁻¹]` is an isomorphism `Ω^p_{A[X]/R,n} ≅ Ω^p_{A[T;T⁻¹]/R,n}`, with
  `PolynomialDeRham.map_weightComponent_eq_laurentWeightComponent` the underlying statement about
  submodules.

## Implementation notes

Both gradings are the one notion of weight of Stacks 0FU9,
`KaehlerDifferential.gradedDifferentialFormComponent`, taken for the grading of the algebra by
the degree of the fibre coordinate.  For `A[T;T⁻¹]` that grading is
`LaurentDeRham.weightGrading`, built from Mathlib's `AddMonoidAlgebra.grade`.  Mathlib has no
graded-algebra structure on `Polynomial`: the `AddMonoidAlgebra` one does not transport, since
`Polynomial` wraps `AddMonoidAlgebra` in a one-field structure and its submodules are therefore
submodules of a different type.  So `PolynomialDeRham.weightGrading` is defined directly as the
range of `Polynomial.monomial n`, which is the exact analogue of Mathlib's
`AddMonoidAlgebra.grade_eq_lsingle_range`, and the two graded components are then two instances
of one definition.

The explicit description of the polynomial weight components is proved in both directions by
reduction to the homogeneous generators `a₀ ⋅ da₁ ∧ ⋯ ∧ da_p`, exactly as for `A[T;T⁻¹]` in
`StacksFrontier.RingTheory.DeRham.LaurentResidue`.  The one asymmetry is that the free generator of
the complementary summand is `dX`, of weight one, rather than `dlog T`, of weight zero: the
weight-`n` forms are `Xⁿ ω' + X^{n-1} dX ∧ ω`, so the second summand is absent at `n = 0`, and
that is exactly what makes clauses (2) and (3) differ from clause (1).

Clause (3) needs `A[T;T⁻¹]` as an `A[X]`-algebra over `R`.  Mathlib has the algebra structure,
`LaurentPolynomial.algebraPolynomial`, but not the scalar tower over `R`, which is supplied here
as `PolynomialDeRham.isScalarTowerLaurent`.

The source statement of clause (2) is printed as `Ω^•_{X/S} = Ω^•_{L/X, 0}`, and that of clause
(3) as `Ω^p_{L/X, n} = Ω^p_{L^⋆/S, n}`; in both the subscript `L/X` is a typo for `L/S`.
Relative to `X` the module `Ω^1_{L/X}` is generated over `O_L` by `dT`, which has weight one, so
`Ω^1_{L/X, 0}` vanishes while `Ω^1_{X/S}` does not, and `Ω^p_{L/X, n}` is zero for `p ≥ 2` while
`Ω^p_{L^⋆/S, n}` is not.  What is formalized here is the intended relative-to-`S` statement,
which is also what the paragraph preceding the lemma in the source supports.

## References

* [Stacks Project, Tag 0FUH](https://stacks.math.columbia.edu/tag/0FUH), the three comparisons of
  weight components for the total space of a line bundle; what is proved here are its omitted
  local calculations
* [Stacks Project, Tag 0FU9](https://stacks.math.columbia.edu/tag/0FU9), the grading of the de
  Rham complex of a graded algebra
-/

open CategoryTheory Function KaehlerDifferential Polynomial

open scoped LaurentPolynomial TensorProduct

@[expose] public section

noncomputable section

universe u

namespace LaurentDeRham

open LaurentPolynomial

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-! ### Multiplication by a power of the variable -/

/-- Multiplication by `Tⁿ` on the relative `p`-forms of `A[T;T⁻¹]` over `R`.  It is an
`R`-linear automorphism because `T` is a unit, the inverse being multiplication by `T⁻ⁿ`. -/
def smulTEquiv (n : ℤ) (p : ℕ) :
    ⋀[A[T;T⁻¹]]^p (Ω[A[T;T⁻¹]⁄R]) ≃ₗ[R] ⋀[A[T;T⁻¹]]^p (Ω[A[T;T⁻¹]⁄R]) :=
  LinearEquiv.ofLinearMap
    (DistribSMul.toLinearMap R (↥(⋀[A[T;T⁻¹]]^p (Ω[A[T;T⁻¹]⁄R]))) (T n : A[T;T⁻¹]))
    (DistribSMul.toLinearMap R (↥(⋀[A[T;T⁻¹]]^p (Ω[A[T;T⁻¹]⁄R]))) (T (-n) : A[T;T⁻¹]))
    (LinearMap.ext fun x ↦ by
      change (T n : A[T;T⁻¹]) • (T (-n) : A[T;T⁻¹]) • x = x
      rw [T_smul_T_smul_pow, add_neg_cancel, T_zero, one_smul])
    (LinearMap.ext fun x ↦ by
      change (T (-n) : A[T;T⁻¹]) • (T n : A[T;T⁻¹]) • x = x
      rw [T_smul_T_smul_pow, neg_add_cancel, T_zero, one_smul])

/-- Multiplication by `Tⁿ` is the scaling of a relative form by `Tⁿ`. -/
@[simp]
theorem smulTEquiv_apply (n : ℤ) (p : ℕ) (x : ↥(⋀[A[T;T⁻¹]]^p (Ω[A[T;T⁻¹]⁄R]))) :
    smulTEquiv R A n p x = (T n : A[T;T⁻¹]) • x := rfl

/-- Scaling a weight-`g` pullback by `Tⁿ` gives a weight-`n + g` pullback. -/
theorem T_smul_weightPullback (g n : ℤ) (p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    (T n : A[T;T⁻¹]) • weightPullback R A g p ω = weightPullback R A (n + g) p ω := by
  rw [weightPullback_apply, weightPullback_apply, T_smul_T_smul_pow]

/-- Scaling a weight-`g` `dlog T`-form by `Tⁿ` gives a weight-`n + g` `dlog T`-form. -/
theorem T_smul_weightDlog (g n : ℤ) (p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    (T n : A[T;T⁻¹]) • weightDlog R A g p ω = weightDlog R A (n + g) p ω := by
  rw [weightDlog_apply, weightDlog_apply, T_smul_T_smul_pow]

/-- Multiplication by `Tⁿ` shifts the pullbacks by `n`. -/
theorem smulTEquiv_comp_weightPullback (g n : ℤ) (p : ℕ) :
    (smulTEquiv R A n p).toLinearMap ∘ₗ weightPullback R A g p = weightPullback R A (n + g) p :=
  LinearMap.ext fun ω ↦ T_smul_weightPullback R A g n p ω

/-- Multiplication by `Tⁿ` shifts the `dlog T`-forms by `n`. -/
theorem smulTEquiv_comp_weightDlog (g n : ℤ) (p : ℕ) :
    (smulTEquiv R A n (p + 1)).toLinearMap ∘ₗ weightDlog R A g p = weightDlog R A (n + g) p :=
  LinearMap.ext fun ω ↦ T_smul_weightDlog R A g n p ω

/-- **Multiplication by `Tⁿ` carries the weight-`g` forms onto the weight-`n + g` forms.** -/
theorem map_smulTEquiv_weightComponent (g n : ℤ) (p : ℕ) :
    Submodule.map (smulTEquiv R A n p).toLinearMap (weightComponent R A g p) =
      weightComponent R A (n + g) p := by
  rw [weightComponent_eq_weightForms, weightComponent_eq_weightForms]
  cases p with
  | zero =>
      rw [weightForms_zero, weightForms_zero, ← LinearMap.range_comp,
        smulTEquiv_comp_weightPullback]
  | succ q =>
      rw [weightForms_succ, weightForms_succ, Submodule.map_sup, ← LinearMap.range_comp,
        ← LinearMap.range_comp, smulTEquiv_comp_weightPullback, smulTEquiv_comp_weightDlog]

/-- **Clause (1) of Stacks 0FUH, affine locally**: multiplication by `Tⁿ` is an isomorphism from
the weight-zero part of `Ω^p_{A[T;T⁻¹]/R}` onto its weight-`n` part, for every integer `n`.  It
is the local form of `Ω^p_{L^⋆/S, n} = Ω^p_{L^⋆/S, 0} ⊗ L^{⊗n}`, the trivialization of `L^{⊗n}`
over the affine being `Tⁿ`. -/
@[stacks 0FUH "clause (1), affine local case: Tⁿ • carries weight zero onto weight n"]
def weightComponentSmulEquiv (n : ℤ) (p : ℕ) :
    ↥(weightComponent R A 0 p) ≃ₗ[R] ↥(weightComponent R A n p) :=
  ((smulTEquiv R A n p).submoduleMap (weightComponent R A 0 p)).trans
    (LinearEquiv.ofEq _ _ (by
      rw [map_smulTEquiv_weightComponent R A 0 n p, add_zero]))

/-- The isomorphism of clause (1) is multiplication by `Tⁿ`. -/
@[simp]
theorem coe_weightComponentSmulEquiv (n : ℤ) (p : ℕ) (x : ↥(weightComponent R A 0 p)) :
    (weightComponentSmulEquiv R A n p x : ⋀[A[T;T⁻¹]]^p (Ω[A[T;T⁻¹]⁄R])) =
      (T n : A[T;T⁻¹]) • (x : ⋀[A[T;T⁻¹]]^p (Ω[A[T;T⁻¹]⁄R])) := rfl

/-! ### Freeness of the weight components over the forms of `A` -/

/-- A pullback scaled by `Tᵍ` vanishes only if the form does. -/
theorem eq_zero_of_weightPullback_eq_zero (g : ℤ) (p : ℕ) {ω' : ↥(⋀[A]^p (Ω[A⁄R]))}
    (h : weightPullback R A g p ω' = 0) : ω' = 0 := by
  have h1 : (T (-g) : A[T;T⁻¹]) • weightPullback R A g p ω' = 0 := by rw [h, smul_zero]
  rw [T_smul_weightPullback, neg_add_cancel, weightPullback_zero_apply] at h1
  have h2 := pullbackRetract_mapExteriorPower R A p ω'
  rw [h1, map_zero] at h2
  exact h2.symm

/-- **The weight-`g` forms are free on `1` and `dlog T` over the forms of `A`**: the coefficients
of `Tᵍ ω' + Tᵍ dlog T ∧ ω` are determined by the form. -/
theorem eq_zero_of_weightPullback_add_weightDlog_eq_zero (g : ℤ) (p : ℕ)
    {ω' : ↥(⋀[A]^(p + 1) (Ω[A⁄R]))} {ω : ↥(⋀[A]^p (Ω[A⁄R]))}
    (h : weightPullback R A g (p + 1) ω' + weightDlog R A g p ω = 0) : ω' = 0 ∧ ω = 0 := by
  have h1 : (T (-g) : A[T;T⁻¹]) • (weightPullback R A g (p + 1) ω' + weightDlog R A g p ω) = 0 := by
    rw [h, smul_zero]
  rw [smul_add, T_smul_weightPullback, T_smul_weightDlog, neg_add_cancel,
    weightPullback_zero_apply, weightDlog_zero_apply] at h1
  have hω : ω = 0 := by
    have h2 := residue_mapExteriorPower_add_wedgeLeft R A p ω' ω
    rw [h1, map_zero] at h2
    exact h2.symm
  rw [hω, map_zero, map_zero, add_zero] at h1
  have h3 := pullbackRetract_mapExteriorPower R A (p + 1) ω'
  rw [h1, map_zero] at h3
  exact ⟨h3.symm, hω⟩

end LaurentDeRham

namespace PolynomialDeRham

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-! ### The weight grading of a polynomial algebra -/

/-- The weight grading of a polynomial algebra: the degree-`n` part of `A[X]` is the
`R`-submodule `A Xⁿ` of the monomials of degree `n`. -/
def weightGrading : ℕ → Submodule R A[X] := fun n ↦
  Submodule.restrictScalars R (LinearMap.range (monomial n : A →ₗ[A] A[X]))

/-- The monomial `a Xⁿ` has weight `n`. -/
theorem monomial_mem_weightGrading (n : ℕ) (a : A) :
    (monomial n a : A[X]) ∈ weightGrading R A n :=
  ⟨a, rfl⟩

/-- A constant has weight zero. -/
theorem C_mem_weightGrading (a : A) : (C a : A[X]) ∈ weightGrading R A 0 := by
  rw [← monomial_zero_left]
  exact monomial_mem_weightGrading R A 0 a

/-- The variable has weight one. -/
theorem X_mem_weightGrading : (X : A[X]) ∈ weightGrading R A 1 := by
  rw [← monomial_one_one_eq_X]
  exact monomial_mem_weightGrading R A 1 1

/-- A polynomial of weight `n` is a monomial of degree `n`. -/
theorem exists_monomial_of_mem_weightGrading {n : ℕ} {q : A[X]}
    (hq : q ∈ weightGrading R A n) : ∃ a : A, (monomial n a : A[X]) = q := hq

/-- The weight-`n` component of the relative `p`-forms of `A[X]` over `R`, the grading of
differential forms of Stacks 0FU9 taken for the weight grading of `A[X]`. -/
def weightComponent (n : ℕ) (p : ℕ) : Submodule R (⋀[A[X]]^p (Ω[A[X]⁄R])) :=
  gradedDifferentialFormComponent (weightGrading R A) p n

/-! ### The explicit description of the weight components -/

/-- A form of weight `n` pulled back from `Ω^p_{A/R}`: the map `ω ↦ Xⁿ ω`. -/
def weightPullback (n p : ℕ) :
    ↥(⋀[A]^p (Ω[A⁄R])) →ₗ[R] ↥(⋀[A[X]]^p (Ω[A[X]⁄R])) :=
  DistribSMul.toLinearMap R (↥(⋀[A[X]]^p (Ω[A[X]⁄R]))) ((X : A[X]) ^ n) ∘ₗ
    (mapExteriorPower R A A[X] p).restrictScalars R

/-- `Xⁿ` times the pullback of `ω`. -/
theorem weightPullback_apply (n p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    weightPullback R A n p ω = ((X : A[X]) ^ n) • mapExteriorPower R A A[X] p ω := rfl

/-- In weight zero the pullback is unscaled. -/
theorem weightPullback_zero (p : ℕ) :
    weightPullback R A 0 p = (mapExteriorPower R A A[X] p).restrictScalars R :=
  LinearMap.ext fun ω ↦ by
    rw [weightPullback_apply, pow_zero, one_smul]
    rfl

/-- A form of weight `n + 1` divisible by `dX`: the map `ω ↦ Xⁿ dX ∧ ω`.  The differential `dX`
itself has weight one, so this is the general weight-`n + 1` form divisible by `dX`. -/
def weightDX (n p : ℕ) :
    ↥(⋀[A]^p (Ω[A⁄R])) →ₗ[R] ↥(⋀[A[X]]^(p + 1) (Ω[A[X]⁄R])) :=
  DistribSMul.toLinearMap R (↥(⋀[A[X]]^(p + 1) (Ω[A[X]⁄R]))) ((X : A[X]) ^ n) ∘ₗ
    (exteriorPower.wedgeLeft (D R A[X] (X : A[X])) p).restrictScalars R ∘ₗ
      (mapExteriorPower R A A[X] p).restrictScalars R

/-- `Xⁿ` times `dX` wedged with the pullback of `ω`. -/
theorem weightDX_apply (n p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    weightDX R A n p ω = ((X : A[X]) ^ n) •
      exteriorPower.wedgeLeft (D R A[X] (X : A[X])) p (mapExteriorPower R A A[X] p ω) := rfl

/-- The weight-`n` forms divisible by `dX`, in degree `p + 1`: the forms `X^{n-1} dX ∧ ω` with
`ω` pulled back from `Ω^p_{A/R}`.  There are none in weight zero, because `dX` has weight one. -/
def weightDXForms : (n p : ℕ) → Submodule R (⋀[A[X]]^(p + 1) (Ω[A[X]⁄R]))
  | 0, _ => ⊥
  | n + 1, p => LinearMap.range (weightDX R A n p)

/-- In weight zero no form is divisible by `dX`. -/
theorem weightDXForms_zero (p : ℕ) : weightDXForms R A 0 p = ⊥ := rfl

/-- In weight `n + 1` the forms divisible by `dX` are the `Xⁿ dX ∧ ω`. -/
theorem weightDXForms_succ (n p : ℕ) :
    weightDXForms R A (n + 1) p = LinearMap.range (weightDX R A n p) := rfl

/-- The forms `Xⁿ ω' + X^{n-1} dX ∧ ω` with `ω'` and `ω` pulled back from `A`.  In degree zero,
and in weight zero, there is no `dX` summand.  This is the explicit description of the weight-`n`
component `PolynomialDeRham.weightComponent`. -/
def weightForms (n : ℕ) : (p : ℕ) → Submodule R (⋀[A[X]]^p (Ω[A[X]⁄R]))
  | 0 => LinearMap.range (weightPullback R A n 0)
  | p + 1 => LinearMap.range (weightPullback R A n (p + 1)) ⊔ weightDXForms R A n p

/-- In degree zero the weight-`n` forms are the pullbacks scaled by `Xⁿ`. -/
theorem weightForms_zero (n : ℕ) :
    weightForms R A n 0 = LinearMap.range (weightPullback R A n 0) := rfl

/-- In positive degree the weight-`n` forms are `Xⁿ ω' + X^{n-1} dX ∧ ω`. -/
theorem weightForms_succ (n p : ℕ) :
    weightForms R A n (p + 1) =
      LinearMap.range (weightPullback R A n (p + 1)) ⊔ weightDXForms R A n p := rfl

/-- A pullback scaled by `Xⁿ` has weight `n`. -/
theorem weightPullback_mem_weightForms (n p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    weightPullback R A n p ω ∈ weightForms R A n p := by
  cases p with
  | zero => exact ⟨ω, rfl⟩
  | succ q => exact Submodule.mem_sup_left ⟨ω, rfl⟩

/-- `Xⁿ dX` wedged with a pullback has weight `n + 1`. -/
theorem weightDX_mem_weightForms (n p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    weightDX R A n p ω ∈ weightForms R A (n + 1) (p + 1) :=
  Submodule.mem_sup_right ⟨ω, rfl⟩

/-- Every weight-`n` form of degree zero is `Xⁿ ω'`. -/
theorem exists_of_mem_weightForms_zero {n : ℕ} {x : ↥(⋀[A[X]]^0 (Ω[A[X]⁄R]))}
    (hx : x ∈ weightForms R A n 0) : ∃ ω' : ↥(⋀[A]^0 (Ω[A⁄R])), x = weightPullback R A n 0 ω' := by
  obtain ⟨ω', rfl⟩ := hx
  exact ⟨ω', rfl⟩

/-- Every weight-zero form is pulled back from `A`: there is no `dX` summand. -/
theorem exists_of_mem_weightForms_succ_zero {p : ℕ} {x : ↥(⋀[A[X]]^(p + 1) (Ω[A[X]⁄R]))}
    (hx : x ∈ weightForms R A 0 (p + 1)) :
    ∃ ω' : ↥(⋀[A]^(p + 1) (Ω[A⁄R])), x = weightPullback R A 0 (p + 1) ω' := by
  rw [weightForms_succ, weightDXForms_zero, sup_bot_eq] at hx
  obtain ⟨ω', rfl⟩ := hx
  exact ⟨ω', rfl⟩

/-- Every weight-`n + 1` form of positive degree is `X^{n+1} ω' + Xⁿ dX ∧ ω`. -/
theorem exists_of_mem_weightForms_succ_succ {n p : ℕ} {x : ↥(⋀[A[X]]^(p + 1) (Ω[A[X]⁄R]))}
    (hx : x ∈ weightForms R A (n + 1) (p + 1)) :
    ∃ (ω' : ↥(⋀[A]^(p + 1) (Ω[A⁄R]))) (ω : ↥(⋀[A]^p (Ω[A⁄R]))),
      x = weightPullback R A (n + 1) (p + 1) ω' + weightDX R A n p ω := by
  rw [weightForms_succ, weightDXForms_succ, Submodule.mem_sup] at hx
  obtain ⟨y, ⟨ω', rfl⟩, z, ⟨ω, rfl⟩, rfl⟩ := hx
  exact ⟨ω', ω, rfl⟩

/-! ### The weight components are the explicitly described forms -/

/-- A monomial acts on a relative form as `Xⁿ` times its coefficient. -/
theorem monomial_smul_pow (n : ℕ) (a : A) (p : ℕ) (x : ↥(⋀[A[X]]^p (Ω[A[X]⁄R]))) :
    (monomial n a : A[X]) • x = ((X : A[X]) ^ n) • (a • x) := by
  rw [← C_mul_X_pow_eq_monomial, mul_comm, mul_smul, C_eq_algebraMap, algebraMap_smul]

/-- Powers of the variable act on relative forms through their product. -/
theorem X_pow_smul_X_pow_smul (m n : ℕ) (p : ℕ) (x : ↥(⋀[A[X]]^p (Ω[A[X]⁄R]))) :
    ((X : A[X]) ^ m) • ((X : A[X]) ^ n) • x = ((X : A[X]) ^ (m + n)) • x := by
  rw [smul_smul, ← pow_add]

/-- The differential of the monomial `a X^{n+1}`, in the degree-one splitting: its coefficient
part is `X^{n+1} d a` and its `dX`-part is `(n + 1) a Xⁿ`. -/
theorem D_monomial_succ (n : ℕ) (a : A) :
    D R A[X] (monomial (n + 1) a) =
      ((X : A[X]) ^ (n + 1)) • map R R A A[X] (D R A a) +
        (monomial n (a * ((n + 1 : ℕ) : A)) : A[X]) • D R A[X] (X : A[X]) := by
  rw [D_eq_mapBaseChange_coeffDerivation_add, coeffDerivation_monomial, mapBaseChange_tmul,
    derivative_monomial, Nat.add_sub_cancel]

/-- A monomial scaling of a weight-`n` pullback is a weight-`k + n` pullback. -/
theorem monomial_smul_weightPullback (n k : ℕ) (a : A) (p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    (monomial k a : A[X]) • weightPullback R A n p ω = weightPullback R A (k + n) p (a • ω) := by
  rw [weightPullback_apply, weightPullback_apply, monomial_smul_pow,
    smul_comm a ((X : A[X]) ^ n), X_pow_smul_X_pow_smul, LinearMap.map_smul_of_tower]

/-- A monomial scaling of a weight-`n + 1` `dX`-form is a weight-`k + n + 1` `dX`-form. -/
theorem monomial_smul_weightDX (n k : ℕ) (a : A) (p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    (monomial k a : A[X]) • weightDX R A n p ω = weightDX R A (k + n) p (a • ω) := by
  rw [weightDX_apply, weightDX_apply, monomial_smul_pow, smul_comm a ((X : A[X]) ^ n),
    X_pow_smul_X_pow_smul, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower]

/-- Wedging a weight-`n` pullback by the differential of a constant keeps the weight. -/
theorem wedgeLeft_D_C_weightPullback (n : ℕ) (a : A) (p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    exteriorPower.wedgeLeft (D R A[X] (C a)) p (weightPullback R A n p ω) =
      weightPullback R A n (p + 1) (exteriorPower.wedgeLeft (D R A a) p ω) := by
  rw [weightPullback_apply, ← map_incl_D, map_smul, weightPullback_apply,
    mapExteriorPower_wedgeLeft]

/-- Wedging a weight-`n + 1` `dX`-form by the differential of a constant keeps the weight. -/
theorem wedgeLeft_D_C_weightDX (n : ℕ) (a : A) (p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    exteriorPower.wedgeLeft (D R A[X] (C a)) (p + 1) (weightDX R A n p ω) =
      weightDX R A n (p + 1) (-exteriorPower.wedgeLeft (D R A a) p ω) := by
  rw [weightDX_apply, ← map_incl_D, map_smul, exteriorPower.wedgeLeft_wedgeLeft_comm,
    weightDX_apply, map_neg, map_neg, mapExteriorPower_wedgeLeft, smul_neg]

/-- Wedging a weight-`n` pullback by the differential of a monomial of degree `k + 1` gives a
form of weight `k + n + 1`. -/
theorem wedgeLeft_D_monomial_succ_weightPullback (n k : ℕ) (a : A) (p : ℕ)
    (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    exteriorPower.wedgeLeft (D R A[X] (monomial (k + 1) a)) p (weightPullback R A n p ω) =
      weightPullback R A (k + n + 1) (p + 1) (exteriorPower.wedgeLeft (D R A a) p ω) +
        weightDX R A (k + n) p ((a * ((k + 1 : ℕ) : A)) • ω) := by
  have h1 : exteriorPower.wedgeLeft (((X : A[X]) ^ (k + 1)) • map R R A A[X] (D R A a)) p
      (weightPullback R A n p ω) =
      weightPullback R A (k + n + 1) (p + 1) (exteriorPower.wedgeLeft (D R A a) p ω) := by
    rw [exteriorPower.wedgeLeft_smul, LinearMap.smul_apply, weightPullback_apply, map_smul,
      X_pow_smul_X_pow_smul, show k + 1 + n = k + n + 1 from by omega, weightPullback_apply,
      mapExteriorPower_wedgeLeft]
  have h2 : exteriorPower.wedgeLeft
      ((monomial k (a * ((k + 1 : ℕ) : A)) : A[X]) • D R A[X] (X : A[X])) p
      (weightPullback R A n p ω) = weightDX R A (k + n) p ((a * ((k + 1 : ℕ) : A)) • ω) := by
    rw [exteriorPower.wedgeLeft_smul, LinearMap.smul_apply, weightPullback_apply, map_smul,
      monomial_smul_pow, smul_comm (a * ((k + 1 : ℕ) : A)) ((X : A[X]) ^ n),
      X_pow_smul_X_pow_smul, weightDX_apply, LinearMap.map_smul_of_tower,
      LinearMap.map_smul_of_tower]
  rw [D_monomial_succ, exteriorPower.wedgeLeft_add, LinearMap.add_apply, h1, h2]

/-- Wedging a weight-`n + 1` `dX`-form by the differential of a monomial of degree `k + 1` gives
a form of weight `k + n + 2`. -/
theorem wedgeLeft_D_monomial_succ_weightDX (n k : ℕ) (a : A) (p : ℕ)
    (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    exteriorPower.wedgeLeft (D R A[X] (monomial (k + 1) a)) (p + 1) (weightDX R A n p ω) =
      weightDX R A (k + n + 1) (p + 1) (-exteriorPower.wedgeLeft (D R A a) p ω) := by
  have h1 : exteriorPower.wedgeLeft (((X : A[X]) ^ (k + 1)) • map R R A A[X] (D R A a)) (p + 1)
      (weightDX R A n p ω) =
      weightDX R A (k + n + 1) (p + 1) (-exteriorPower.wedgeLeft (D R A a) p ω) := by
    rw [exteriorPower.wedgeLeft_smul, LinearMap.smul_apply, weightDX_apply, map_smul,
      X_pow_smul_X_pow_smul, show k + 1 + n = k + n + 1 from by omega,
      exteriorPower.wedgeLeft_wedgeLeft_comm, weightDX_apply, map_neg, map_neg,
      mapExteriorPower_wedgeLeft, smul_neg]
  have h2 : exteriorPower.wedgeLeft
      ((monomial k (a * ((k + 1 : ℕ) : A)) : A[X]) • D R A[X] (X : A[X])) (p + 1)
      (weightDX R A n p ω) = 0 := by
    rw [exteriorPower.wedgeLeft_smul, LinearMap.smul_apply, weightDX_apply, map_smul,
      exteriorPower.wedgeLeft_wedgeLeft, smul_zero, smul_zero]
  rw [D_monomial_succ, exteriorPower.wedgeLeft_add, LinearMap.add_apply, h1, h2, add_zero]

/-- The weight components are closed under multiplication by a monomial. -/
theorem monomial_smul_mem_weightForms (k : ℕ) (a : A) {n p : ℕ}
    {x : ↥(⋀[A[X]]^p (Ω[A[X]⁄R]))} (hx : x ∈ weightForms R A n p) :
    (monomial k a : A[X]) • x ∈ weightForms R A (k + n) p := by
  cases p with
  | zero =>
      obtain ⟨ω', rfl⟩ := exists_of_mem_weightForms_zero R A hx
      rw [monomial_smul_weightPullback]
      exact weightPullback_mem_weightForms R A (k + n) 0 _
  | succ q =>
      cases n with
      | zero =>
          obtain ⟨ω', rfl⟩ := exists_of_mem_weightForms_succ_zero R A hx
          rw [monomial_smul_weightPullback]
          exact weightPullback_mem_weightForms R A (k + 0) (q + 1) _
      | succ m =>
          obtain ⟨ω', ω, rfl⟩ := exists_of_mem_weightForms_succ_succ R A hx
          rw [smul_add, monomial_smul_weightPullback, monomial_smul_weightDX]
          exact Submodule.add_mem _
            (weightPullback_mem_weightForms R A (k + (m + 1)) (q + 1) _)
            (weightDX_mem_weightForms R A (k + m) q _)

/-- The weight components are closed under wedging by the differential of a monomial. -/
theorem wedgeLeft_D_monomial_mem_weightForms (k : ℕ) (a : A) {n p : ℕ}
    {x : ↥(⋀[A[X]]^p (Ω[A[X]⁄R]))} (hx : x ∈ weightForms R A n p) :
    exteriorPower.wedgeLeft (D R A[X] (monomial k a)) p x ∈ weightForms R A (k + n) (p + 1) := by
  cases k with
  | zero =>
      rw [monomial_zero_left, show 0 + n = n from Nat.zero_add n]
      cases p with
      | zero =>
          obtain ⟨ω', rfl⟩ := exists_of_mem_weightForms_zero R A hx
          rw [wedgeLeft_D_C_weightPullback]
          exact weightPullback_mem_weightForms R A n 1 _
      | succ q =>
          cases n with
          | zero =>
              obtain ⟨ω', rfl⟩ := exists_of_mem_weightForms_succ_zero R A hx
              rw [wedgeLeft_D_C_weightPullback]
              exact weightPullback_mem_weightForms R A 0 (q + 2) _
          | succ m =>
              obtain ⟨ω', ω, rfl⟩ := exists_of_mem_weightForms_succ_succ R A hx
              rw [map_add, wedgeLeft_D_C_weightPullback, wedgeLeft_D_C_weightDX]
              exact Submodule.add_mem _
                (weightPullback_mem_weightForms R A (m + 1) (q + 2) _)
                (weightDX_mem_weightForms R A m (q + 1) _)
  | succ j =>
      rw [show j + 1 + n = j + n + 1 from by omega]
      cases p with
      | zero =>
          obtain ⟨ω', rfl⟩ := exists_of_mem_weightForms_zero R A hx
          rw [wedgeLeft_D_monomial_succ_weightPullback]
          exact Submodule.add_mem _ (weightPullback_mem_weightForms R A (j + n + 1) 1 _)
            (weightDX_mem_weightForms R A (j + n) 0 _)
      | succ q =>
          cases n with
          | zero =>
              obtain ⟨ω', rfl⟩ := exists_of_mem_weightForms_succ_zero R A hx
              rw [wedgeLeft_D_monomial_succ_weightPullback]
              exact Submodule.add_mem _
                (weightPullback_mem_weightForms R A (j + 0 + 1) (q + 2) _)
                (weightDX_mem_weightForms R A (j + 0) (q + 1) _)
          | succ m =>
              obtain ⟨ω', ω, rfl⟩ := exists_of_mem_weightForms_succ_succ R A hx
              rw [map_add, wedgeLeft_D_monomial_succ_weightPullback,
                wedgeLeft_D_monomial_succ_weightDX]
              refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
              · exact weightPullback_mem_weightForms R A (j + (m + 1) + 1) (q + 2) _
              · exact weightDX_mem_weightForms R A (j + (m + 1)) (q + 1) _
              · exact weightDX_mem_weightForms R A (j + m + 1) (q + 1) _

/-- A differential monomial in polynomials of prescribed weights lies in the weight component of
the sum of their degrees. -/
theorem smul_ιMulti_D_mem_weightComponent (p : ℕ) (w : Fin (p + 1) → ℕ)
    (q : Fin (p + 1) → A[X]) (hq : ∀ i, q i ∈ weightGrading R A (w i)) :
    q 0 • exteriorPower.ιMulti A[X] p (fun i ↦ D R A[X] (q i.succ)) ∈
      weightComponent R A (∑ i, w i) p :=
  homogeneousDifferentialForm_mem_gradedDifferentialFormComponent
    (weightGrading R A) p w (fun i ↦ ⟨q i, hq i⟩) _ rfl

/-- A differential monomial with coefficient `a Xᵏ` and remaining factors the monomials `qᵢ` of
weight `wᵢ` lies in the component of weight `k + ∑ wᵢ`. -/
theorem monomial_smul_ιMulti_D_mem_weightComponent (p : ℕ) (k : ℕ) (a : A) (w : Fin p → ℕ)
    (q : Fin p → A[X]) (hq : ∀ i, q i ∈ weightGrading R A (w i)) :
    (monomial k a : A[X]) • exteriorPower.ιMulti A[X] p (fun i ↦ D R A[X] (q i)) ∈
      weightComponent R A (k + ∑ i, w i) p := by
  have h := smul_ιMulti_D_mem_weightComponent R A p (Fin.cons k w)
    (Fin.cons (monomial k a) q) (Fin.cases (monomial_mem_weightGrading R A k a) hq)
  rw [Fin.sum_univ_succ] at h
  simpa only [Fin.cons_zero, Fin.cons_succ] using h

/-- A linear map out of `Ω^p_{A/R}` lands in a submodule once it does on every generator
`b₀ ⋅ db₁ ∧ ⋯ ∧ db_p`. -/
private theorem mem_of_forall_gen_mem {M : Type*} [AddCommGroup M] [Module R M] {p : ℕ}
    (f : ↥(⋀[A]^p (Ω[A⁄R])) →ₗ[R] M) (N : Submodule R M)
    (h : ∀ b : Fin (p + 1) → A,
      f (b 0 • exteriorPower.ιMulti A p fun i ↦ D R A (b i.succ)) ∈ N)
    (ω : ↥(⋀[A]^p (Ω[A⁄R]))) : f ω ∈ N := by
  have htop : (⊤ : Submodule R ↥(⋀[A]^p (Ω[A⁄R]))) ≤ Submodule.comap f N := by
    rw [← Crystalline.span_range_smul_ιMulti_eq_top (R := R) (D R A)
      (span_range_derivation R A) p, Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    exact h b
  exact htop Submodule.mem_top

/-- A pullback scaled by `Xⁿ` lies in the weight-`n` component. -/
theorem weightPullback_mem_weightComponent (n p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    weightPullback R A n p ω ∈ weightComponent R A n p := by
  have hgen : ∀ b : Fin (p + 1) → A,
      weightPullback R A n p (b 0 • exteriorPower.ιMulti A p fun i ↦ D R A (b i.succ)) ∈
        weightComponent R A n p := by
    intro b
    have hmem := monomial_smul_ιMulti_D_mem_weightComponent R A p n (b 0) (fun _ ↦ 0)
      (fun i ↦ C (b i.succ)) fun i ↦ C_mem_weightGrading R A (b i.succ)
    rw [show n + ∑ _i : Fin p, (0 : ℕ) = n from by simp] at hmem
    rw [weightPullback_apply, map_smul, mapExteriorPower_ιMulti, ← monomial_smul_pow]
    simp only [map_incl_D]
    exact hmem
  exact mem_of_forall_gen_mem R A _ _ hgen ω

/-- `Xⁿ dX` wedged with a pullback lies in the weight-`n + 1` component. -/
theorem weightDX_mem_weightComponent (n p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    weightDX R A n p ω ∈ weightComponent R A (n + 1) (p + 1) := by
  have hgen : ∀ b : Fin (p + 1) → A,
      weightDX R A n p (b 0 • exteriorPower.ιMulti A p fun i ↦ D R A (b i.succ)) ∈
        weightComponent R A (n + 1) (p + 1) := by
    intro b
    have hmem := monomial_smul_ιMulti_D_mem_weightComponent R A (p + 1) n (b 0)
      (Fin.cons 1 fun _ ↦ 0) (Fin.cons X fun j ↦ C (b j.succ))
      (Fin.cases (X_mem_weightGrading R A) fun j ↦ C_mem_weightGrading R A (b j.succ))
    rw [show n + ∑ i : Fin (p + 1), (Fin.cons 1 fun _ ↦ 0 : Fin (p + 1) → ℕ) i = n + 1 from by
      simp [Fin.sum_univ_succ]] at hmem
    have hfun : (fun i : Fin (p + 1) ↦ D R A[X]
          ((Fin.cons X fun j ↦ C (b j.succ) : Fin (p + 1) → A[X]) i)) =
        Fin.cons (D R A[X] (X : A[X])) fun j ↦ D R A[X] (C (b j.succ)) := by
      funext i
      refine Fin.cases ?_ ?_ i <;> intros <;> rfl
    rw [hfun] at hmem
    rw [weightDX_apply, map_smul, LinearMap.map_smul_of_tower, mapExteriorPower_ιMulti,
      exteriorPower.wedgeLeft_ιMulti, ← monomial_smul_pow]
    simp only [map_incl_D]
    exact hmem
  exact mem_of_forall_gen_mem R A _ _ hgen ω

/-- The explicitly described forms have the stated weight. -/
theorem weightForms_le_weightComponent (n p : ℕ) :
    weightForms R A n p ≤ weightComponent R A n p := by
  cases p with
  | zero =>
      rw [weightForms_zero, LinearMap.range_le_iff_comap, eq_top_iff]
      exact fun ω _ ↦ weightPullback_mem_weightComponent R A n 0 ω
  | succ q =>
      cases n with
      | zero =>
          rw [weightForms_succ, weightDXForms_zero, sup_bot_eq, LinearMap.range_le_iff_comap,
            eq_top_iff]
          exact fun ω _ ↦ weightPullback_mem_weightComponent R A 0 (q + 1) ω
      | succ m =>
          rw [weightForms_succ, weightDXForms_succ]
          refine sup_le ?_ ?_ <;> rw [LinearMap.range_le_iff_comap, eq_top_iff]
          · exact fun ω _ ↦ weightPullback_mem_weightComponent R A (m + 1) (q + 1) ω
          · exact fun ω _ ↦ weightDX_mem_weightComponent R A m q ω

/-- A wedge of differentials of monomials has the weight given by the sum of their degrees. -/
theorem ιMulti_D_monomial_mem_weightForms (p : ℕ) :
    ∀ (k : Fin p → ℕ) (c : Fin p → A),
      exteriorPower.ιMulti A[X] p (fun i ↦ D R A[X] (monomial (k i) (c i))) ∈
        weightForms R A (∑ i, k i) p := by
  induction p with
  | zero =>
      intro k c
      have hkey : exteriorPower.ιMulti A[X] 0
          (fun i ↦ D R A[X] (monomial (k i) (c i))) =
          weightPullback R A 0 0 (exteriorPower.ιMulti A 0 fun i ↦ D R A (c i)) := by
        rw [weightPullback_apply, mapExteriorPower_ιMulti, pow_zero, one_smul]
        congr 1
        funext i
        exact i.elim0
      rw [show (∑ i : Fin 0, k i) = 0 from by simp, hkey]
      exact weightPullback_mem_weightForms R A 0 0 _
  | succ q ih =>
      intro k c
      have hcons : (fun i ↦ D R A[X] (monomial (k i) (c i))) =
          Fin.cons (D R A[X] (monomial (k 0) (c 0)))
            (fun i : Fin q ↦ D R A[X] (monomial (k i.succ) (c i.succ))) := by
        funext i
        refine Fin.cases ?_ ?_ i <;> intros <;> rfl
      rw [hcons, ← exteriorPower.wedgeLeft_ιMulti, Fin.sum_univ_succ]
      exact wedgeLeft_D_monomial_mem_weightForms R A (k 0) (c 0)
        (ih (fun i ↦ k i.succ) fun i ↦ c i.succ)

/-- Every form of weight `n` is of the explicitly described shape. -/
theorem weightComponent_le_weightForms (n p : ℕ) :
    weightComponent R A n p ≤ weightForms R A n p := by
  rw [weightComponent, gradedDifferentialFormComponent_le_iff]
  intro degree a hg
  choose c hc using fun i ↦ exists_monomial_of_mem_weightGrading R A (a i).2
  have hsum : n = degree 0 + ∑ i : Fin p, degree i.succ := by rw [hg, Fin.sum_univ_succ]
  rw [hsum]
  simp only [← hc]
  exact monomial_smul_mem_weightForms R A (degree 0) (c 0)
    (ιMulti_D_monomial_mem_weightForms R A p (fun i ↦ degree i.succ) fun i ↦ c i.succ)

/-- **The weight components of the de Rham complex of `A[X]`, explicitly**: a relative form of
weight `n` is `Xⁿ ω' + X^{n-1} dX ∧ ω` with `ω'` and `ω` pulled back from `A`, and in weight zero
the second summand is absent because `dX` has weight one. -/
theorem weightComponent_eq_weightForms (n p : ℕ) :
    weightComponent R A n p = weightForms R A n p :=
  le_antisymm (weightComponent_le_weightForms R A n p) (weightForms_le_weightComponent R A n p)

/-- **The weight-zero forms of `A[X]` are exactly the forms pulled back from `A`.** -/
theorem weightComponent_zero_eq_range (p : ℕ) :
    weightComponent R A 0 p =
      LinearMap.range ((mapExteriorPower R A A[X] p).restrictScalars R) := by
  cases p with
  | zero => rw [weightComponent_eq_weightForms, weightForms_zero, weightPullback_zero]
  | succ q =>
      rw [weightComponent_eq_weightForms, weightForms_succ, weightDXForms_zero, sup_bot_eq,
        weightPullback_zero]

/-- A form pulled back from `Ω^p_{A/R}` has weight zero. -/
theorem mapExteriorPower_mem_weightComponent (p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    mapExteriorPower R A A[X] p ω ∈ weightComponent R A 0 p := by
  rw [weightComponent_zero_eq_range]
  exact ⟨ω, rfl⟩

end PolynomialDeRham

namespace PolynomialDeRham

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-! ### The weight-zero de Rham complex of a polynomial algebra -/

section EvalZero

attribute [local instance] algebraEvalZero isScalarTowerEvalZero

/-- The pullback `Ω^p_{A/R} → Ω^p_{A[X]/R}` is injective, being retracted by the map induced by
evaluation at `0`. -/
theorem injective_mapExteriorPower (p : ℕ) :
    Function.Injective (mapExteriorPower R A A[X] p) := fun ω₁ ω₂ h ↦ by
  have h' := congrArg (mapExteriorPower R A[X] A p) h
  rwa [mapExteriorPower_evalZero, mapExteriorPower_evalZero] at h'

end EvalZero

/-- The de Rham differential preserves weight zero. -/
theorem deRhamDifferential_mem_weightComponent (p : ℕ) {x : ↥(⋀[A[X]]^p (Ω[A[X]⁄R]))}
    (hx : x ∈ weightComponent R A 0 p) :
    deRhamDifferential (A := R) p x ∈ weightComponent R A 0 (p + 1) := by
  rw [weightComponent_zero_eq_range] at hx
  obtain ⟨ω, rfl⟩ := hx
  rw [show ((mapExteriorPower R A A[X] p).restrictScalars R) ω =
      mapExteriorPower R A A[X] p ω from rfl, ← mapExteriorPower_deRhamDifferential]
  exact mapExteriorPower_mem_weightComponent R A (p + 1) _

/-- The de Rham differential on weight-zero forms. -/
def deRhamDifferentialWeightZero (p : ℕ) :
    ↥(weightComponent R A 0 p) →ₗ[R] ↥(weightComponent R A 0 (p + 1)) :=
  (deRhamDifferential (A := R) p).restrict fun _ hx ↦
    deRhamDifferential_mem_weightComponent R A p hx

/-- The differential on weight-zero forms is the de Rham differential. -/
@[simp]
theorem coe_deRhamDifferentialWeightZero (p : ℕ) (x : ↥(weightComponent R A 0 p)) :
    (deRhamDifferentialWeightZero R A p x : ⋀[A[X]]^(p + 1) (Ω[A[X]⁄R])) =
      deRhamDifferential (A := R) p x := rfl

/-- The de Rham differential of weight-zero forms squares to zero. -/
theorem deRhamDifferentialWeightZero_comp_self (p : ℕ) :
    (deRhamDifferentialWeightZero R A (p + 1)).comp (deRhamDifferentialWeightZero R A p) = 0 :=
  LinearMap.ext fun x ↦ by
    refine Subtype.ext ?_
    exact deRhamDifferential_comp_self (A := R) p x.1

/-- **The weight-zero de Rham complex** `Ω^•_{A[X]/R,0}`: the subcomplex of `Ω^•_{A[X]/R}` of the
forms of weight zero for the grading of `A[X]` by the degree of `X`. -/
def deRhamComplexWeightZero : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun p ↦ ModuleCat.of R ↥(weightComponent R A 0 p))
    (fun p ↦ ModuleCat.ofHom (deRhamDifferentialWeightZero R A p))
    fun p ↦ ModuleCat.hom_ext (deRhamDifferentialWeightZero_comp_self R A p)

/-- The degree-`p` term of the weight-zero de Rham complex is the weight-zero part of
`Ω^p_{A[X]/R}`. -/
@[simp]
theorem deRhamComplexWeightZero_X (p : ℕ) :
    (deRhamComplexWeightZero R A).X p = ModuleCat.of R ↥(weightComponent R A 0 p) := rfl

/-- The arrow of the weight-zero de Rham complex out of degree `p` is the de Rham
differential. -/
@[simp]
theorem deRhamComplexWeightZero_d (p : ℕ) :
    (deRhamComplexWeightZero R A).d p (p + 1) =
      ModuleCat.ofHom (deRhamDifferentialWeightZero R A p) := by
  apply CochainComplex.of_d

/-- **The pullback of forms** `Ω^•_{A/R} → Ω^•_{A[X]/R,0}`: a form pulled back from `A` has
weight zero, and the pullback commutes with the de Rham differentials. -/
def inclWeightZero : deRhamComplex R A ⟶ deRhamComplexWeightZero R A :=
  CochainComplex.ofHom
    (fun p ↦ ModuleCat.ofHom (((mapExteriorPower R A A[X] p).restrictScalars R).codRestrict
      (weightComponent R A 0 p) (mapExteriorPower_mem_weightComponent R A p)))
    fun p ↦ by
      ext ω
      simp only [deRhamComplex_d, deRhamComplexWeightZero_d]
      refine Subtype.ext ?_
      exact (mapExteriorPower_deRhamDifferential R A A[X] p ω).symm

/-- The comparison map is the pullback of forms in every degree. -/
@[simp]
theorem inclWeightZero_f_apply (p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    ((inclWeightZero R A).f p).hom ω =
      (⟨mapExteriorPower R A A[X] p ω, mapExteriorPower_mem_weightComponent R A p ω⟩ :
        ↥(weightComponent R A 0 p)) := rfl

/-- In every degree the pullback of forms is a bijection onto the weight-zero forms: it is
injective, and surjective because every weight-zero form is pulled back from `A`. -/
theorem bijective_inclWeightZero_f (p : ℕ) :
    Function.Bijective ((inclWeightZero R A).f p).hom := by
  refine ⟨fun ω₁ ω₂ h ↦ injective_mapExteriorPower R A p (congrArg Subtype.val h), fun x ↦ ?_⟩
  obtain ⟨ω, hω⟩ := (weightComponent_zero_eq_range R A p).le x.2
  exact ⟨ω, Subtype.ext hω⟩

/-- In every degree the pullback of forms is an isomorphism onto the weight-zero forms. -/
instance isIso_inclWeightZero_f (p : ℕ) : IsIso ((inclWeightZero R A).f p) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_inclWeightZero_f R A p)

/-- The pullback of forms is an isomorphism of complexes, being one in every degree. -/
instance isIso_inclWeightZero : IsIso (inclWeightZero R A) :=
  HomologicalComplex.Hom.isIso_of_components _

/-- **Clause (2) of Stacks 0FUH, affine locally**: the de Rham complex of `A` over `R` is the
weight-zero part of the de Rham complex of `A[X]` over `R`, through the pullback of forms.  It is
the local form of `Ω^•_{X/S} = Ω^•_{L/S, 0}`. -/
@[stacks 0FUH "clause (2), affine local case; the printed subscript L/X is a typo for L/S"]
def deRhamComplexWeightZeroIso : deRhamComplex R A ≅ deRhamComplexWeightZero R A :=
  asIso (inclWeightZero R A)

/-- The isomorphism of clause (2) is the pullback of forms. -/
@[simp]
theorem deRhamComplexWeightZeroIso_hom : (deRhamComplexWeightZeroIso R A).hom =
    inclWeightZero R A := rfl

end PolynomialDeRham

namespace KaehlerDifferential

/-- The maps of relative forms compose along a tower `B → C → E` of `R`-algebras: the map
induced by `B → E` is the map induced by `B → C` followed by the map induced by `C → E`. -/
theorem mapExteriorPower_mapExteriorPower (R B C E : Type u) [CommRing R] [CommRing B]
    [CommRing C] [CommRing E] [Algebra R B] [Algebra R C] [Algebra R E] [Algebra B C]
    [Algebra B E] [Algebra C E] [IsScalarTower R B C] [IsScalarTower R B E]
    [IsScalarTower B C E] [IsScalarTower R C E] (p : ℕ) (ω : ↥(⋀[B]^p (Ω[B⁄R]))) :
    mapExteriorPower R C E p (mapExteriorPower R B C p ω) = mapExteriorPower R B E p ω := by
  refine LinearMap.congr_fun (LinearMap.ext_on
    (Crystalline.span_range_smul_ιMulti_eq_top (R := R) (D R B) (span_range_derivation R B) p)
    (f := (mapExteriorPower R C E p).restrictScalars R ∘ₗ
      (mapExteriorPower R B C p).restrictScalars R)
    (g := (mapExteriorPower R B E p).restrictScalars R) ?_) ω
  rintro _ ⟨b, rfl⟩
  have hmap (x : B) : map R R C E (map R R B C (D R B x)) = map R R B E (D R B x) :=
    LinearMap.congr_fun (map_comp_map R B C E) (D R B x)
  simp only [LinearMap.coe_comp, comp_apply, LinearMap.coe_restrictScalars, map_smul,
    LinearMap.map_smul_of_tower, mapExteriorPower_ιMulti, hmap]

end KaehlerDifferential

namespace PolynomialDeRham

section Laurent

open LaurentPolynomial

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-! ### Comparison with the Laurent polynomial algebra -/

/-- `A[T;T⁻¹]` is an `A[X]`-algebra over `R`: the inclusion `A[X] → A[T;T⁻¹]` of the total space
of a line bundle into the complement of its zero section is a map of `R`-algebras. -/
instance isScalarTowerLaurent : IsScalarTower R A[X] A[T;T⁻¹] :=
  .of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R A A[X], IsScalarTower.algebraMap_apply R A A[T;T⁻¹],
      algebraMap_eq_toLaurent, Polynomial.algebraMap_eq, Polynomial.toLaurent_C,
      LaurentPolynomial.C_eq_algebraMap]

/-- The restriction of `dX` to the complement of the zero section is `d T`. -/
theorem map_D_X : map R R A[X] A[T;T⁻¹] (D R A[X] (X : A[X])) = D R A[T;T⁻¹] (T 1) := by
  rw [map_D, algebraMap_eq_toLaurent, Polynomial.toLaurent_X]

/-- On the complement of the zero section, scaling by `Xⁿ` is scaling by `Tⁿ`. -/
theorem X_pow_smul_eq_T_smul (n : ℕ) (p : ℕ) (y : ↥(⋀[A[T;T⁻¹]]^p (Ω[A[T;T⁻¹]⁄R]))) :
    ((X : A[X]) ^ n) • y = (T (n : ℤ) : A[T;T⁻¹]) • y := by
  rw [← algebraMap_smul A[T;T⁻¹] ((X : A[X]) ^ n), algebraMap_eq_toLaurent,
    Polynomial.toLaurent_X_pow]

/-- The restriction of a weight-`n` pullback is the weight-`n` pullback. -/
theorem mapExteriorPower_weightPullback (n p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    mapExteriorPower R A[X] A[T;T⁻¹] p (weightPullback R A n p ω) =
      LaurentDeRham.weightPullback R A (n : ℤ) p ω := by
  rw [weightPullback_apply, map_smul, mapExteriorPower_mapExteriorPower,
    LaurentDeRham.weightPullback_apply, X_pow_smul_eq_T_smul]

/-- The restriction of `Xⁿ dX ∧ ω` is `T^{n+1} dlog T ∧ ω`: the two free generators agree up to
the unit `T`. -/
theorem mapExteriorPower_weightDX (n p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    mapExteriorPower R A[X] A[T;T⁻¹] (p + 1) (weightDX R A n p ω) =
      LaurentDeRham.weightDlog R A ((n : ℤ) + 1) p ω := by
  rw [weightDX_apply, map_smul, mapExteriorPower_wedgeLeft, mapExteriorPower_mapExteriorPower,
    map_D_X, ← LaurentDeRham.T_smul_dlogT, exteriorPower.wedgeLeft_smul, LinearMap.smul_apply,
    X_pow_smul_eq_T_smul, LaurentDeRham.T_smul_T_smul_pow, LaurentDeRham.weightDlog_apply]

/-- The restriction of forms carries the weight-`n` pullbacks to the weight-`n` pullbacks. -/
theorem mapExteriorPower_comp_weightPullback (n p : ℕ) :
    (mapExteriorPower R A[X] A[T;T⁻¹] p).restrictScalars R ∘ₗ weightPullback R A n p =
      LaurentDeRham.weightPullback R A (n : ℤ) p :=
  LinearMap.ext fun ω ↦ mapExteriorPower_weightPullback R A n p ω

/-- The restriction of forms carries the `dX`-forms of weight `n + 1` to the `dlog T`-forms of
weight `n + 1`. -/
theorem mapExteriorPower_comp_weightDX (n p : ℕ) :
    (mapExteriorPower R A[X] A[T;T⁻¹] (p + 1)).restrictScalars R ∘ₗ weightDX R A n p =
      LaurentDeRham.weightDlog R A ((n : ℤ) + 1) p :=
  LinearMap.ext fun ω ↦ mapExteriorPower_weightDX R A n p ω

/-- **In positive weight the restriction of forms is onto**: for `n > 0` every weight-`n` form on
the complement of the zero section is the restriction of a weight-`n` form on the total space. -/
theorem map_weightComponent_eq_laurentWeightComponent (n p : ℕ) (hn : 0 < n) :
    Submodule.map ((mapExteriorPower R A[X] A[T;T⁻¹] p).restrictScalars R)
        (weightComponent R A n p) =
      LaurentDeRham.weightComponent R A (n : ℤ) p := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hcast : ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [weightComponent_eq_weightForms, LaurentDeRham.weightComponent_eq_weightForms]
  cases p with
  | zero =>
      rw [weightForms_zero, LaurentDeRham.weightForms_zero, ← LinearMap.range_comp,
        mapExteriorPower_comp_weightPullback]
  | succ q =>
      rw [weightForms_succ, weightDXForms_succ, LaurentDeRham.weightForms_succ,
        Submodule.map_sup, ← LinearMap.range_comp, ← LinearMap.range_comp,
        mapExteriorPower_comp_weightPullback, mapExteriorPower_comp_weightDX, hcast]

/-- **In positive weight the restriction of forms is injective**: a weight-`n` form on the total
space restricting to zero on the complement of the zero section is zero.  Its coefficients in the
description `Xⁿ ω' + X^{n-1} dX ∧ ω` are read off from the restriction. -/
theorem eq_zero_of_mem_weightComponent_of_mapExteriorPower_eq_zero (n p : ℕ)
    {x : ↥(⋀[A[X]]^p (Ω[A[X]⁄R]))} (hx : x ∈ weightComponent R A n p)
    (h : mapExteriorPower R A[X] A[T;T⁻¹] p x = 0) : x = 0 := by
  rw [weightComponent_eq_weightForms] at hx
  cases p with
  | zero =>
      obtain ⟨ω', rfl⟩ := exists_of_mem_weightForms_zero R A hx
      rw [mapExteriorPower_weightPullback] at h
      rw [LaurentDeRham.eq_zero_of_weightPullback_eq_zero R A (n : ℤ) 0 h, map_zero]
  | succ q =>
      cases n with
      | zero =>
          obtain ⟨ω', rfl⟩ := exists_of_mem_weightForms_succ_zero R A hx
          rw [mapExteriorPower_weightPullback] at h
          rw [LaurentDeRham.eq_zero_of_weightPullback_eq_zero R A ((0 : ℕ) : ℤ) (q + 1) h,
            map_zero]
      | succ m =>
          obtain ⟨ω', ω, rfl⟩ := exists_of_mem_weightForms_succ_succ R A hx
          have hcast : ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
          rw [map_add, mapExteriorPower_weightPullback, mapExteriorPower_weightDX, hcast] at h
          obtain ⟨hω', hω⟩ :=
            LaurentDeRham.eq_zero_of_weightPullback_add_weightDlog_eq_zero R A
              ((m + 1 : ℕ) : ℤ) q h
          rw [hω', hω, map_zero, map_zero, add_zero]

/-- **Clause (3) of Stacks 0FUH, affine locally**: for `n > 0` the restriction of forms along
`A[X] → A[T;T⁻¹]` is an isomorphism from the weight-`n` part of `Ω^p_{A[X]/R}` onto the weight-`n`
part of `Ω^p_{A[T;T⁻¹]/R}`.  It is the local form of `Ω^p_{L/S, n} = Ω^p_{L^⋆/S, n}`; positivity
of `n` is needed, since in weight `n ≤ 0` the form `Tⁿ dlog T` is not the restriction of a form on
the total space. -/
@[stacks 0FUH "clause (3), affine local case; the printed subscript L/X is a typo for L/S"]
def laurentWeightEquiv (n : ℕ) (hn : 0 < n) (p : ℕ) :
    ↥(weightComponent R A n p) ≃ₗ[R] ↥(LaurentDeRham.weightComponent R A (n : ℤ) p) :=
  LinearEquiv.ofBijective
    (((mapExteriorPower R A[X] A[T;T⁻¹] p).restrictScalars R).restrict
      fun x hx ↦ (map_weightComponent_eq_laurentWeightComponent R A n p hn).le ⟨x, hx, rfl⟩)
    ⟨by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro y hy
      refine Subtype.ext ?_
      exact eq_zero_of_mem_weightComponent_of_mapExteriorPower_eq_zero R A n p y.2
        (congrArg Subtype.val hy),
     by
      intro z
      obtain ⟨y, hy, hz⟩ :=
        (map_weightComponent_eq_laurentWeightComponent R A n p hn).ge z.2
      exact ⟨⟨y, hy⟩, Subtype.ext hz⟩⟩

/-- The isomorphism of clause (3) is the restriction of forms. -/
@[simp]
theorem coe_laurentWeightEquiv (n : ℕ) (hn : 0 < n) (p : ℕ) (x : ↥(weightComponent R A n p)) :
    (laurentWeightEquiv R A n hn p x : ⋀[A[T;T⁻¹]]^p (Ω[A[T;T⁻¹]⁄R])) =
      mapExteriorPower R A[X] A[T;T⁻¹] p (x : ⋀[A[X]]^p (Ω[A[X]⁄R])) := rfl

end Laurent

end PolynomialDeRham

end

end
