module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.Kaehler.Polynomial
public import StacksFrontier.RingTheory.DeRham.Complex

/-!
# Integration of polynomials, and the de Rham complex of a polynomial algebra

Let `R` be a commutative ring and `A` an `R`-algebra.  The algebraic Poincaré lemma in one
variable asserts that the inclusion `Ω^•_{A/R} → Ω^•_{A[X]/R}` is a homotopy equivalence when
`R` contains `ℚ`: a homotopy inverse sends `g ω + g' dX ∧ ω'` to `g(0) ω`, and the homotopy sends
`g ω + g' dX ∧ ω'` to `(∫ g') ω'`, where `∫ g'` is the antiderivative of `g'` with vanishing
constant term.  This file provides the affine ingredients of that statement.

The first is the antiderivative itself.  Over a `ℚ`-algebra `A` the derivative `A[X] → A[X]` has
a unique `A`-linear section whose values have vanishing constant term, namely
`∑ aₙ Xⁿ ↦ ∑ (n + 1)⁻¹ aₙ X^{n+1}`; this is `Polynomial.integral`.

The second is the functoriality of the de Rham complex in the algebra variable.  For a tower
`R → A → B` the map `KaehlerDifferential.map R R A B` on differentials induces a map of de Rham
complexes `Ω^•_{A/R} → Ω^•_{B/R}`.  Applied to `A → A[X]` and to evaluation at `0`,
`A[X] → A`, it produces the inclusion and the candidate homotopy inverse of the Poincaré lemma,
and the two compose to the identity on `Ω^•_{A/R}`.

The third is the degree-one case of the decomposition that makes the homotopy writable, namely
`Ω[A[X]⁄R] ≅ (A[X] ⊗_A Ω[A⁄R]) ⊕ A[X] dX`.  The projection onto the second summand is the
`dX`-component `PolynomialDeRham.pderivX`; the projection onto the first is the lift to
`Ω[A[X]⁄R]` of the derivation `∑ aᵢ Xⁱ ↦ ∑ Xⁱ ⊗ d aᵢ` that differentiates the coefficients.
Mathlib's `KaehlerDifferential.mapBaseChange` is the inclusion of the first summand, and the
exact sequence `A[X] ⊗_A Ω[A⁄R] → Ω[A[X]⁄R] → Ω[A[X]⁄A] → 0` is therefore split.

The fourth is the cohomology of the *relative* de Rham complex `Ω^•_{A[X]/A}` of a `ℚ`-algebra
`A`:  it is `A` in degree `0` and vanishes in positive degrees.  Here `Ω[A[X]⁄A] ≅ A[X]` is free
of rank one on `dX`, so the exterior powers vanish above degree one, the degree-zero differential
is `Polynomial.derivative` and the computation is exactly `Polynomial.integral` together with
`Polynomial.eq_C_coeff_zero_of_derivative_eq_zero`.

## Main definitions

* `Polynomial.integral`: the `A`-linear antiderivative `A[X] → A[X]` with vanishing constant
  term, over a `ℚ`-algebra `A`.
* `exteriorPower.mapTower`: the map `⋀[R]^n M → ⋀[S]^n N` induced by an `R`-linear map
  `M → N` into a module over an `R`-algebra `S`.
* `KaehlerDifferential.mapExteriorPower`: the induced map `Ω^p_{A/R} → Ω^p_{B/R}` for a tower
  `R → A → B`.
* `KaehlerDifferential.deRhamComplexMap`: the induced map of de Rham complexes
  `Ω^•_{A/R} → Ω^•_{B/R}`.
* `PolynomialDeRham.incl` and `PolynomialDeRham.evalZero`: the two maps of de Rham complexes
  `Ω^•_{A/R} → Ω^•_{A[X]/R}` and `Ω^•_{A[X]/R} → Ω^•_{A/R}` coming from `A → A[X]` and from
  evaluation at `0`.
* `PolynomialDeRham.pderivX`: the `dX`-component `Ω[A[X]⁄R] → A[X]` of a relative `1`-form.
* `PolynomialDeRham.coeffDerivationMap` and `PolynomialDeRham.coeffDerivation`: coefficientwise
  differentiation `A[X] → A[X] ⊗_A Ω[A⁄R]`, `∑ aᵢ Xⁱ ↦ ∑ Xⁱ ⊗ d aᵢ`, as an `R`-linear map and
  as an `R`-derivation.
* `PolynomialDeRham.coeffProj`: the coefficient component `Ω[A[X]⁄R] → A[X] ⊗_A Ω[A⁄R]` of a
  relative `1`-form.
* `PolynomialDeRham.kaehlerProdEquiv`: the degree-one decomposition
  `Ω[A[X]⁄R] ≅ (A[X] ⊗_A Ω[A⁄R]) ⊕ A[X] dX`.
* `PolynomialDeRham.kerDeRhamDifferentialPolynomialZeroEquiv`: the identification
  `H^0(Ω^•_{A[X]/A}) ≅ A`.

## Main results

* `Polynomial.derivative_integral`: `d/dX (∫ p) = p`.
* `Polynomial.coeff_integral_zero`: `∫ p` has vanishing constant term.
* `Polynomial.eq_integral_of_derivative_eq`: `∫ p` is the only polynomial with vanishing
  constant term whose derivative is `p`.
* `Polynomial.integral_derivative`: `∫ (d/dX p) = p - p(0)`.
* `KaehlerDifferential.mapExteriorPower_deRhamDifferential`: the induced maps commute with the
  de Rham differentials.
* `PolynomialDeRham.incl_comp_evalZero`: the composite `Ω^•_{A/R} → Ω^•_{A[X]/R} → Ω^•_{A/R}`
  is the identity, so `PolynomialDeRham.incl` is a split monomorphism.
* `PolynomialDeRham.pderivX_smul_D_X` and `PolynomialDeRham.pderivX_map_incl`: `A[X] dX` is a
  free rank-one summand of `Ω[A[X]⁄R]`, complementary to the image of `Ω[A⁄R]`.
* `PolynomialDeRham.coeffProj_mapBaseChange`: the coefficient component retracts
  `KaehlerDifferential.mapBaseChange`.
* `PolynomialDeRham.mapBaseChange_coeffProj_add_pderivX_smul`: a relative `1`-form is the sum of
  its coefficient component and its `dX`-component.
* `KaehlerDifferential.oneEquiv_deRhamDifferential_zero`: in degree zero the de Rham differential
  is the universal derivation.
* `PolynomialDeRham.surjective_D_polynomial` and `PolynomialDeRham.D_polynomial_eq_zero_iff`:
  over a `ℚ`-algebra `A`, the derivation `A[X] → Ω[A[X]⁄A]` is surjective and its kernel is the
  constants.
* `PolynomialDeRham.subsingleton_exteriorPower_polynomial`: `⋀[A[X]]^p Ω[A[X]⁄A] = 0` for
  `p ≥ 2`.
* `PolynomialDeRham.exactAt_deRhamComplex_polynomial`: `H^p(Ω^•_{A[X]/A}) = 0` for `p ≥ 1`.

## References

* [Stacks 0FUI](https://stacks.math.columbia.edu/tag/0FUI), the Poincaré lemma
* [Stacks 0FKG](https://stacks.math.columbia.edu/tag/0FKG), the de Rham differentials
-/

open CategoryTheory Polynomial

open scoped TensorProduct

@[expose] public section

noncomputable section

namespace Polynomial

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- The antiderivative `∫ : A[X] → A[X]` over a `ℚ`-algebra `A`: the `A`-linear map sending
`∑ aₙ Xⁿ` to `∑ (n + 1)⁻¹ aₙ X^{n+1}`.  It is the unique `A`-linear section of the derivative
whose values have vanishing constant term. -/
def integral : A[X] →ₗ[A] A[X] :=
  lsum fun i ↦ (monomial (i + 1)).comp (DistribSMul.toLinearMap A A ((i + 1 : ℚ)⁻¹))

/-- The antiderivative of `a Xⁿ` is `(n + 1)⁻¹ a X^{n+1}`. -/
@[simp]
theorem integral_monomial (n : ℕ) (a : A) :
    integral (monomial n a) = monomial (n + 1) (((n : ℚ) + 1)⁻¹ • a) := by
  simp [integral, lsum_apply]

/-- In a `ℚ`-algebra the image of `n + 1` under the structure map is `n + 1`. -/
private theorem algebraMap_natCast_add_one (n : ℕ) :
    algebraMap ℚ A ((n : ℚ) + 1) = (n : A) + 1 := by
  push_cast
  simp

/-- Multiplying by `n + 1` and scaling by `(n + 1)⁻¹` are mutually inverse in a `ℚ`-algebra. -/
private theorem inv_natCast_add_one_smul_mul (n : ℕ) (a : A) :
    (((n : ℚ) + 1)⁻¹ • a) * ((n : A) + 1) = a := by
  have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
  rw [← algebraMap_natCast_add_one (A := A) n, mul_comm, ← Algebra.smul_def, smul_smul,
    mul_inv_cancel₀ hn, one_smul]

/-- The derivative of the antiderivative of `p` is `p`. -/
@[simp]
theorem derivative_integral (p : A[X]) : derivative (integral p) = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
      rw [integral_monomial, derivative_monomial_succ]
      congr 1
      exact inv_natCast_add_one_smul_mul n a

/-- The antiderivative of a polynomial has vanishing constant term. -/
@[simp]
theorem coeff_integral_zero (p : A[X]) : (integral p).coeff 0 = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp [coeff_monomial]

/-- The coefficient of `X^{n+1}` in `∫ p` is `(n + 1)⁻¹` times the coefficient of `Xⁿ` in `p`. -/
theorem coeff_integral_succ (p : A[X]) (n : ℕ) :
    (integral p).coeff (n + 1) = ((n : ℚ) + 1)⁻¹ • p.coeff n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, smul_add]
  | monomial m a =>
      rw [integral_monomial, coeff_monomial, coeff_monomial]
      by_cases h : m = n
      · subst h; simp
      · simp [h, Nat.add_right_cancel_iff]

/-- A polynomial over a `ℚ`-algebra with vanishing derivative is its own constant term. -/
theorem eq_C_coeff_zero_of_derivative_eq_zero {p : A[X]} (hp : derivative p = 0) :
    p = C (p.coeff 0) :=
  have : IsAddTorsionFree A := .of_module_rat A
  eq_C_of_derivative_eq_zero hp

/-- `∫ p` is the only polynomial with vanishing constant term whose derivative is `p`. -/
theorem eq_integral_of_derivative_eq {p q : A[X]} (hq : derivative q = p)
    (hq0 : q.coeff 0 = 0) : q = integral p := by
  have hd : derivative (q - integral p) = 0 := by rw [map_sub, hq, derivative_integral, sub_self]
  have h := eq_C_coeff_zero_of_derivative_eq_zero hd
  rw [coeff_sub, hq0, coeff_integral_zero, sub_zero, map_zero] at h
  rw [← sub_eq_zero, h]

/-- The antiderivative of the derivative of `p` is `p` minus its constant term. -/
@[simp]
theorem integral_derivative (p : A[X]) : integral (derivative p) = p - C (p.coeff 0) := by
  refine (eq_integral_of_derivative_eq ?_ ?_).symm
  · rw [map_sub, derivative_C, sub_zero]
  · rw [coeff_sub, coeff_C_zero, sub_self]

/-- The antiderivative `Polynomial.integral` is injective. -/
theorem integral_injective : Function.Injective (integral (A := A)) := fun p q h ↦ by
  rw [← derivative_integral p, ← derivative_integral q, h]

/-- Over a `ℚ`-algebra every polynomial is a derivative. -/
theorem derivative_surjective : Function.Surjective (derivative (R := A)) :=
  fun p ↦ ⟨integral p, derivative_integral p⟩

end Polynomial

namespace exteriorPower

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
  [IsScalarTower R S N]

/-- The map `⋀[R]^n M → ⋀[S]^n N` induced by an `R`-linear map `f : M → N` into a module `N`
over an `R`-algebra `S`.  Unlike `exteriorPower.map` the two exterior powers are taken over
different rings; the map is `R`-linear only. -/
def mapTower (n : ℕ) (f : M →ₗ[R] N) : ⋀[R]^n M →ₗ[R] ⋀[S]^n N :=
  alternatingMapLinearEquiv
    (({ (ιMulti S n (M := N)).toMultilinearMap.restrictScalars R with
        map_eq_zero_of_eq' := fun v _ _ h hij ↦ (ιMulti S n).map_eq_zero_of_eq v h hij } :
      N [⋀^Fin n]→ₗ[R] ⋀[S]^n N).compLinearMap f)

/-- `exteriorPower.mapTower` sends `v₁ ∧ ⋯ ∧ vₙ` to `f v₁ ∧ ⋯ ∧ f vₙ`. -/
@[simp]
theorem mapTower_ιMulti (n : ℕ) (f : M →ₗ[R] N) (v : Fin n → M) :
    mapTower n f (ιMulti R n v) = ιMulti S n fun i ↦ f (v i) :=
  alternatingMapLinearEquiv_apply_ιMulti _ _

end exteriorPower

namespace KaehlerDifferential

universe u

/-- Linear maps on `Ω[A⁄R]` agreeing on every `d a` are equal. -/
private theorem linearMap_ext_D {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M] {f g : Ω[A⁄R] →ₗ[A] M}
    (h : ∀ a, f (D R A a) = g (D R A a)) : f = g :=
  LinearMap.ext_on (span_range_derivation R A) (by rintro _ ⟨a, rfl⟩; exact h a)

/-- `R`-linear maps on `⋀[A]^p Ω[A⁄R]` agreeing on every `b₀ • d b₁ ∧ ⋯ ∧ d b_p` are equal. -/
private theorem exteriorPower_ext_smul_ιMulti_D {R A M : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M] {p : ℕ} {f g : ⋀[A]^p (Ω[A⁄R]) →ₗ[R] M}
    (h : ∀ b : Fin (p + 1) → A,
      f (b 0 • exteriorPower.ιMulti A p fun i ↦ D R A (b i.succ)) =
        g (b 0 • exteriorPower.ιMulti A p fun i ↦ D R A (b i.succ))) : f = g :=
  LinearMap.ext_on (Crystalline.span_range_smul_ιMulti_eq_top (R := R) (D R A)
    (span_range_derivation R A) p) (by rintro _ ⟨b, rfl⟩; exact h b)

section DegreeZero

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- In degree zero the de Rham differential of `B` over `A` is the universal derivation, read
through the canonical identifications `⋀[B]^0 M ≅ B` and `⋀[B]^1 M ≅ M`. -/
theorem oneEquiv_deRhamDifferential_zero (ξ : ⋀[B]^0 (Ω[B⁄A])) :
    exteriorPower.oneEquiv B (Ω[B⁄A]) (deRhamDifferential (A := A) 0 ξ) =
      D A B (exteriorPower.zeroEquiv B (Ω[B⁄A]) ξ) := by
  refine LinearMap.congr_fun (exteriorPower_ext_smul_ιMulti_D
    (f := (exteriorPower.oneEquiv B (Ω[B⁄A])).toLinearMap.restrictScalars A ∘ₗ
      deRhamDifferential (A := A) 0)
    (g := (D A B).toLinearMap ∘ₗ
      (exteriorPower.zeroEquiv B (Ω[B⁄A])).toLinearMap.restrictScalars A) fun b ↦ ?_) ξ
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
    LinearEquiv.coe_coe, deRhamDifferential_smul_ιMulti_D, map_smul,
    exteriorPower.zeroEquiv_ιMulti, smul_eq_mul, mul_one]
  simp

end DegreeZero

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [Algebra A B] [IsScalarTower R A B]

/-- The map `Ω^p_{A/R} → Ω^p_{B/R}` induced by a tower of `R`-algebras `A → B`: the `p`-th
exterior power of `KaehlerDifferential.map R R A B`, taken over `A` on the source and over `B`
on the target. -/
def mapExteriorPower (p : ℕ) : ⋀[A]^p (Ω[A⁄R]) →ₗ[A] ⋀[B]^p (Ω[B⁄R]) :=
  exteriorPower.mapTower p (map R R A B)

/-- `KaehlerDifferential.mapExteriorPower` sends `ω₁ ∧ ⋯ ∧ ω_p` to the wedge product of the
images of the `ωᵢ` under `KaehlerDifferential.map R R A B`. -/
@[simp]
theorem mapExteriorPower_ιMulti (p : ℕ) (ω : Fin p → Ω[A⁄R]) :
    mapExteriorPower R A B p (exteriorPower.ιMulti A p ω) =
      exteriorPower.ιMulti B p fun i ↦ map R R A B (ω i) :=
  exteriorPower.mapTower_ιMulti _ _ _

/-- The maps `Ω^p_{A/R} → Ω^p_{B/R}` induced by a tower `A → B` commute with the de Rham
differentials. -/
theorem mapExteriorPower_deRhamDifferential (p : ℕ) (ω : ⋀[A]^p (Ω[A⁄R])) :
    mapExteriorPower R A B (p + 1) (deRhamDifferential (A := R) p ω) =
      deRhamDifferential (A := R) (B := B) p (mapExteriorPower R A B p ω) := by
  have key : ((mapExteriorPower R A B (p + 1)).restrictScalars R) ∘ₗ
      deRhamDifferential (A := R) (B := A) p =
      deRhamDifferential (A := R) (B := B) p ∘ₗ
        ((mapExteriorPower R A B p).restrictScalars R) := by
    refine exteriorPower_ext_smul_ιMulti_D fun b ↦ ?_
    simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply]
    rw [deRhamDifferential_smul_ιMulti_D p b, mapExteriorPower_ιMulti, map_smul,
      mapExteriorPower_ιMulti]
    simp only [map_D]
    simpa only [algebraMap_smul] using
      (deRhamDifferential_smul_ιMulti_D (A := R) (B := B) p fun i ↦ algebraMap A B (b i)).symm
  exact LinearMap.congr_fun key ω

/-- The de Rham complex is functorial in the algebra variable: a tower of `R`-algebras `A → B`
induces a map of complexes `Ω^•_{A/R} → Ω^•_{B/R}` of `R`-modules. -/
def deRhamComplexMap : deRhamComplex R A ⟶ deRhamComplex R B :=
  CochainComplex.ofHom (fun p ↦ ModuleCat.ofHom ((mapExteriorPower R A B p).restrictScalars R))
    fun p ↦ by
      ext ω
      simp only [deRhamComplex_d]
      exact (mapExteriorPower_deRhamDifferential R A B p ω).symm

/-- In degree `p` the map of de Rham complexes is `KaehlerDifferential.mapExteriorPower`. -/
@[simp]
theorem deRhamComplexMap_f (p : ℕ) :
    (deRhamComplexMap R A B).f p =
      ModuleCat.ofHom ((mapExteriorPower R A B p).restrictScalars R) := rfl

end KaehlerDifferential

namespace PolynomialDeRham

open KaehlerDifferential

universe u

section Tower

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- The inclusion of de Rham complexes `Ω^•_{A/R} → Ω^•_{A[X]/R}` induced by `A → A[X]`. -/
def incl : deRhamComplex R A ⟶ deRhamComplex R A[X] :=
  deRhamComplexMap R A A[X]

/-- `A` as an `A[X]`-algebra, through evaluation at `0`. -/
local instance algebraEvalZero : Algebra A[X] A := (evalRingHom (0 : A)).toAlgebra

/-- The structure map `A[X] → A` is evaluation at `0`. -/
theorem algebraMap_polynomial_apply (q : A[X]) : algebraMap A[X] A q = q.eval 0 := rfl

/-- The algebras `R → A[X] → A`, with `A[X] → A` evaluation at `0`, form a scalar tower. -/
local instance isScalarTowerEvalZero : IsScalarTower R A[X] A :=
  .of_algebraMap_eq fun r ↦ by
    simp [algebraMap_polynomial_apply, IsScalarTower.algebraMap_apply R A A[X]]

/-- On differentials the inclusion sends `d a` to `d a`, the constant polynomial. -/
@[simp]
theorem map_incl_D (a : A) : map R R A A[X] (D R A a) = D R A[X] (C a) := by
  rw [map_D]
  simp

/-- On differentials evaluation at `0` sends `d g` to `d g(0)`. -/
@[simp]
theorem map_evalZero_D (q : A[X]) : map R R A[X] A (D R A[X] q) = D R A (q.eval 0) := by
  rw [map_D, algebraMap_polynomial_apply]

/-- Evaluation at `0` kills `dX`. -/
@[simp]
theorem map_evalZero_D_X : map R R A[X] A (D R A[X] (X : A[X])) = 0 := by
  rw [map_evalZero_D, eval_X, map_zero]

/-- Evaluation at `0` retracts `Ω[A⁄R] → Ω[A[X]⁄R]`. -/
theorem map_evalZero_map (ω : Ω[A⁄R]) : map R R A[X] A (map R R A A[X] ω) = ω := by
  refine LinearMap.congr_fun (linearMap_ext_D
    (f := (map R R A[X] A).restrictScalars A ∘ₗ map R R A A[X]) (g := LinearMap.id) fun a ↦ ?_) ω
  simp [algebraMap_polynomial_apply]

/-- Evaluation at `0` retracts `Ω^p_{A/R} → Ω^p_{A[X]/R}` in every degree. -/
theorem mapExteriorPower_evalZero (p : ℕ) (ξ : ⋀[A]^p (Ω[A⁄R])) :
    mapExteriorPower R A[X] A p (mapExteriorPower R A A[X] p ξ) = ξ := by
  refine LinearMap.congr_fun (exteriorPower_ext_smul_ιMulti_D
    (f := (mapExteriorPower R A[X] A p).restrictScalars R ∘ₗ
      (mapExteriorPower R A A[X] p).restrictScalars R) (g := LinearMap.id) fun b ↦ ?_) ξ
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
    LinearMap.id_coe, id_eq, map_smul, mapExteriorPower_ιMulti, LinearMap.map_smul_of_tower]
  congr 1
  simp [algebraMap_polynomial_apply]

/-- The map of de Rham complexes `Ω^•_{A[X]/R} → Ω^•_{A/R}` induced by evaluation at `0`.  In
degree `p` it sends `g ω` to `g(0) ω` and kills every form involving `dX`. -/
def evalZero : deRhamComplex R A[X] ⟶ deRhamComplex R A :=
  deRhamComplexMap R A[X] A

/-- Evaluation at `0` is a retraction of the inclusion `Ω^•_{A/R} → Ω^•_{A[X]/R}`. -/
@[simp]
theorem incl_comp_evalZero : incl R A ≫ evalZero R A = 𝟙 (deRhamComplex R A) := by
  ext p ξ
  exact mapExteriorPower_evalZero R A p ξ

/-- The inclusion `Ω^•_{A/R} → Ω^•_{A[X]/R}` is a split monomorphism, with retraction the map
induced by evaluation at `0`. -/
instance : IsSplitMono (incl R A) :=
  ⟨⟨{ retraction := evalZero R A, id := incl_comp_evalZero R A }⟩⟩

/-- The `dX`-component of a relative `1`-form: the unique `A[X]`-linear map `Ω[A[X]⁄R] → A[X]`
sending `d g` to `dg/dX`.  It splits off the free rank-one summand `A[X] dX` of `Ω[A[X]⁄R]`. -/
def pderivX : Ω[A[X]⁄R] →ₗ[A[X]] A[X] :=
  (Polynomial.derivative' (R := A)).restrictScalars R |>.liftKaehlerDifferential

/-- The `dX`-component of `d g` is `dg/dX`. -/
@[simp]
theorem pderivX_D (q : A[X]) : pderivX R A (D R A[X] q) = derivative q :=
  Derivation.congr_fun (Derivation.liftKaehlerDifferential_comp _) q

/-- The `dX`-component of `dX` is `1`. -/
@[simp]
theorem pderivX_D_X : pderivX R A (D R A[X] (X : A[X])) = 1 := by
  rw [pderivX_D, derivative_X]

/-- The `dX`-component of a form pulled back from `Ω[A⁄R]` vanishes. -/
@[simp]
theorem pderivX_map_incl (ω : Ω[A⁄R]) : pderivX R A (map R R A A[X] ω) = 0 := by
  refine LinearMap.congr_fun (linearMap_ext_D
    (f := (pderivX R A).restrictScalars A ∘ₗ map R R A A[X]) (g := 0) fun a ↦ ?_) ω
  simp

/-- `g ↦ g dX` is split by the `dX`-component, so `A[X] dX` is a free rank-one summand of
`Ω[A[X]⁄R]`. -/
@[simp]
theorem pderivX_smul_D_X (g : A[X]) : pderivX R A (g • D R A[X] (X : A[X])) = g := by
  rw [map_smul, pderivX_D_X, smul_eq_mul, mul_one]

end Tower

/-! ### The degree-one decomposition of `Ω[A[X]⁄R]` -/

section Splitting

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- Differentiation of the coefficients of a polynomial, as an `R`-linear map:
`∑ aᵢ Xⁱ ↦ ∑ Xⁱ ⊗ d aᵢ`.  It is a derivation, namely `PolynomialDeRham.coeffDerivation`. -/
def coeffDerivationMap : A[X] →ₗ[R] A[X] ⊗[A] Ω[A⁄R] :=
  Polynomial.lsum fun i ↦
    ((TensorProduct.mk A A[X] (Ω[A⁄R]) ((X : A[X]) ^ i)).restrictScalars R).comp
      (D R A).toLinearMap

/-- Coefficientwise differentiation sends the monomial `a Xⁿ` to `Xⁿ ⊗ d a`. -/
@[simp]
theorem coeffDerivationMap_monomial (n : ℕ) (a : A) :
    coeffDerivationMap R A (monomial n a) = ((X : A[X]) ^ n) ⊗ₜ[A] D R A a := by
  simp [coeffDerivationMap, Polynomial.lsum_apply, Polynomial.sum_monomial_index]

/-- Differentiation of the coefficients of a polynomial: the `R`-derivation
`A[X] → A[X] ⊗[A] Ω[A⁄R]` sending `∑ aᵢ Xⁱ` to `∑ Xⁱ ⊗ d aᵢ`. -/
def coeffDerivation : Derivation R A[X] (A[X] ⊗[A] Ω[A⁄R]) where
  toLinearMap := coeffDerivationMap R A
  map_one_eq_zero' := by
    rw [← C_1, ← monomial_zero_left, coeffDerivationMap_monomial]
    simp
  leibniz' p q := by
    induction p using Polynomial.induction_on' with
    | add p p' hp hp' => simp [add_mul, hp, hp', add_smul, smul_add]; abel
    | monomial m a =>
      induction q using Polynomial.induction_on' with
      | add q q' hq hq' => simp [mul_add, hq, hq', add_smul, smul_add]; abel
      | monomial n b =>
        rw [monomial_mul_monomial, coeffDerivationMap_monomial, coeffDerivationMap_monomial,
          coeffDerivationMap_monomial, Derivation.leibniz, TensorProduct.tmul_add,
          TensorProduct.tmul_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
          TensorProduct.smul_tmul', TensorProduct.smul_tmul', TensorProduct.smul_tmul']
        simp [smul_eq_C_mul, ← C_mul_X_pow_eq_monomial, mul_assoc, ← pow_add, Nat.add_comm]

/-- Coefficientwise differentiation sends the monomial `a Xⁿ` to `Xⁿ ⊗ d a`. -/
@[simp]
theorem coeffDerivation_monomial (n : ℕ) (a : A) :
    coeffDerivation R A (monomial n a) = ((X : A[X]) ^ n) ⊗ₜ[A] D R A a :=
  coeffDerivationMap_monomial R A n a

/-- Coefficientwise differentiation sends the constant polynomial `a` to `1 ⊗ d a`. -/
@[simp]
theorem coeffDerivation_C (a : A) : coeffDerivation R A (C a) = (1 : A[X]) ⊗ₜ[A] D R A a := by
  rw [← monomial_zero_left, coeffDerivation_monomial, pow_zero]

/-- The coefficients of `X` are constants, so differentiating them gives zero. -/
@[simp]
theorem coeffDerivation_X : coeffDerivation R A (X : A[X]) = 0 := by
  rw [← monomial_one_one_eq_X, coeffDerivation_monomial]
  simp

/-- The coefficient component of a relative `1`-form: the unique `A[X]`-linear map
`Ω[A[X]⁄R] → A[X] ⊗[A] Ω[A⁄R]` sending `d g` to `∑ Xⁱ ⊗ d gᵢ`.  It retracts
`KaehlerDifferential.mapBaseChange` and kills `dX`. -/
def coeffProj : Ω[A[X]⁄R] →ₗ[A[X]] A[X] ⊗[A] Ω[A⁄R] :=
  (coeffDerivation R A).liftKaehlerDifferential

/-- The coefficient component of `d g` is the coefficientwise differential of `g`. -/
@[simp]
theorem coeffProj_D (q : A[X]) : coeffProj R A (D R A[X] q) = coeffDerivation R A q :=
  Derivation.congr_fun (Derivation.liftKaehlerDifferential_comp _) q

/-- The coefficient component of `dX` vanishes. -/
@[simp]
theorem coeffProj_D_X : coeffProj R A (D R A[X] (X : A[X])) = 0 := by
  rw [coeffProj_D, coeffDerivation_X]

/-- The coefficient component of a form `ω` pulled back from `Ω[A⁄R]` is `1 ⊗ ω`. -/
@[simp]
theorem coeffProj_map (ω : Ω[A⁄R]) :
    coeffProj R A (map R R A A[X] ω) = (1 : A[X]) ⊗ₜ[A] ω := by
  refine LinearMap.congr_fun (linearMap_ext_D
    (f := (coeffProj R A).restrictScalars A ∘ₗ map R R A A[X])
    (g := TensorProduct.mk A A[X] (Ω[A⁄R]) 1) fun a ↦ ?_) ω
  simp

/-- The coefficient component retracts the base change map `A[X] ⊗[A] Ω[A⁄R] → Ω[A[X]⁄R]`, so
the latter is a split monomorphism. -/
@[simp]
theorem coeffProj_mapBaseChange (ξ : A[X] ⊗[A] Ω[A⁄R]) :
    coeffProj R A (mapBaseChange R A A[X] ξ) = ξ := by
  induction ξ using TensorProduct.induction_on with
  | zero => simp
  | tmul g ω =>
      rw [mapBaseChange_tmul, map_smul, coeffProj_map, TensorProduct.smul_tmul', smul_eq_mul,
        mul_one]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The `dX`-component of a form coming from `A[X] ⊗[A] Ω[A⁄R]` vanishes. -/
@[simp]
theorem pderivX_mapBaseChange (ξ : A[X] ⊗[A] Ω[A⁄R]) :
    pderivX R A (mapBaseChange R A A[X] ξ) = 0 := by
  induction ξ using TensorProduct.induction_on with
  | zero => simp
  | tmul g ω => rw [mapBaseChange_tmul, map_smul, pderivX_map_incl, smul_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

/-- The splitting identity on the generators `d q` of `Ω[A[X]⁄R]`. -/
private theorem mapBaseChange_coeffDerivation (q : A[X]) :
    mapBaseChange R A A[X] (coeffDerivation R A q) + derivative q • D R A[X] (X : A[X]) =
      D R A[X] q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      have hD : D R A[X] (p + q) = D R A[X] p + D R A[X] q := map_add _ _ _
      rw [hD, ← hp, ← hq]
      simp only [map_add, add_smul]
      abel
  | monomial n a =>
      rw [coeffDerivation_monomial, mapBaseChange_tmul, map_incl_D,
        ← C_mul_X_pow_eq_monomial, Derivation.leibniz, Derivation.leibniz_pow, add_comm]
      congr 1
      rw [derivative_C_mul_X_pow, ← Nat.cast_smul_eq_nsmul A[X] n, smul_smul, smul_smul]
      congr 1
      rw [C_mul, map_natCast]

/-- Every relative `1`-form of `A[X]` over `R` is the sum of its coefficient component and its
`dX`-component. -/
theorem mapBaseChange_coeffProj_add_pderivX_smul (ω : Ω[A[X]⁄R]) :
    mapBaseChange R A A[X] (coeffProj R A ω) + pderivX R A ω • D R A[X] (X : A[X]) = ω := by
  refine LinearMap.congr_fun (linearMap_ext_D
    (f := (mapBaseChange R A A[X]).comp (coeffProj R A) +
      (LinearMap.toSpanSingleton A[X] (Ω[A[X]⁄R]) (D R A[X] (X : A[X]))).comp (pderivX R A))
    (g := LinearMap.id) fun q ↦ ?_) ω
  simpa using mapBaseChange_coeffDerivation R A q

/-- The degree-one decomposition `Ω[A[X]⁄R] ≅ (A[X] ⊗[A] Ω[A⁄R]) ⊕ A[X] dX`: a relative `1`-form
of `A[X]` over `R` is determined by its coefficient component and its `dX`-component, and these
may be prescribed independently. -/
def kaehlerProdEquiv : Ω[A[X]⁄R] ≃ₗ[A[X]] (A[X] ⊗[A] Ω[A⁄R]) × A[X] :=
  LinearEquiv.ofLinearMap ((coeffProj R A).prod (pderivX R A))
    ((mapBaseChange R A A[X]).comp (LinearMap.fst A[X] (A[X] ⊗[A] Ω[A⁄R]) A[X]) +
      (LinearMap.toSpanSingleton A[X] (Ω[A[X]⁄R]) (D R A[X] (X : A[X]))).comp
        (LinearMap.snd A[X] (A[X] ⊗[A] Ω[A⁄R]) A[X]))
    (LinearMap.ext fun x ↦ Prod.ext (by
        simp [LinearMap.toSpanSingleton_apply]) (by
        simp [LinearMap.toSpanSingleton_apply]))
    (LinearMap.ext fun ω ↦ by
      simpa [LinearMap.toSpanSingleton_apply] using
        mapBaseChange_coeffProj_add_pderivX_smul R A ω)

/-- `PolynomialDeRham.kaehlerProdEquiv` sends a form to its coefficient and `dX`-components. -/
@[simp]
theorem kaehlerProdEquiv_apply (ω : Ω[A[X]⁄R]) :
    kaehlerProdEquiv R A ω = (coeffProj R A ω, pderivX R A ω) := rfl

/-- The inverse of `PolynomialDeRham.kaehlerProdEquiv` sends `(ξ, g)` to the image of `ξ` under
`KaehlerDifferential.mapBaseChange` plus `g dX`. -/
@[simp]
theorem kaehlerProdEquiv_symm_apply (ξ : A[X] ⊗[A] Ω[A⁄R]) (g : A[X]) :
    (kaehlerProdEquiv R A).symm (ξ, g) =
      mapBaseChange R A A[X] ξ + g • D R A[X] (X : A[X]) := rfl

end Splitting

section Relative

variable (A : Type u) [CommRing A]

/-- `Ω[A[X]⁄A]` is generated by `dX` as an `A[X]`-module. -/
theorem span_D_X_eq_top :
    Submodule.span A[X] (Set.range fun _ : Fin 1 ↦ D A A[X] (X : A[X])) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun ω ↦ ?_
  have hω : ω = polynomialEquiv A ω • D A A[X] (X : A[X]) := by
    conv_lhs => rw [← (polynomialEquiv A).symm_apply_apply ω]
    rw [polynomialEquiv_symm]
  rw [hω]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)

/-- As `Ω[A[X]⁄A]` is generated by one element, its exterior powers vanish above degree one. -/
theorem subsingleton_exteriorPower_polynomial {p : ℕ} (hp : 2 ≤ p) :
    Subsingleton (⋀[A[X]]^p (Ω[A[X]⁄A])) :=
  exteriorPower.subsingleton_of_span_eq_top_of_card_lt _ (span_D_X_eq_top A) p
    (by simp only [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)

variable [Algebra ℚ A]

/-- Over a `ℚ`-algebra every relative `1`-form of `A[X]` over `A` is exact, since every
polynomial has an antiderivative. -/
theorem surjective_D_polynomial : Function.Surjective (D A A[X]) := fun ω ↦
  ⟨integral (polynomialEquiv A ω), (polynomialEquiv A).injective <| by
    rw [polynomialEquiv_D, derivative_integral]⟩

/-- Over a `ℚ`-algebra a polynomial has vanishing relative differential exactly when it is
constant. -/
theorem D_polynomial_eq_zero_iff (q : A[X]) : D A A[X] q = 0 ↔ q = C (q.coeff 0) := by
  rw [← (polynomialEquiv A).map_eq_zero_iff, polynomialEquiv_D]
  exact ⟨eq_C_coeff_zero_of_derivative_eq_zero, fun h ↦ by rw [h]; simp⟩

/-- Over a `ℚ`-algebra every differential of `Ω^•_{A[X]/A}` is surjective: in degree zero because
every polynomial has an antiderivative, and in higher degrees because the target vanishes. -/
theorem surjective_deRhamDifferential_polynomial (p : ℕ) :
    Function.Surjective (deRhamDifferential (A := A) (B := A[X]) p) := by
  match p with
  | 0 =>
      intro η
      obtain ⟨q, hq⟩ := surjective_D_polynomial A (exteriorPower.oneEquiv A[X] (Ω[A[X]⁄A]) η)
      refine ⟨(exteriorPower.zeroEquiv A[X] (Ω[A[X]⁄A])).symm q, ?_⟩
      apply (exteriorPower.oneEquiv A[X] (Ω[A[X]⁄A])).injective
      rw [oneEquiv_deRhamDifferential_zero, LinearEquiv.apply_symm_apply, hq]
  | (n + 1) =>
      have := subsingleton_exteriorPower_polynomial A (p := n + 2) (by omega)
      exact fun η ↦ ⟨0, Subsingleton.elim _ _⟩

/-- The de Rham complex of `A[X]` over a `ℚ`-algebra `A` is exact in every positive degree:
`H^p(Ω^•_{A[X]/A}) = 0` for `p ≥ 1`. -/
theorem exactAt_deRhamComplex_polynomial (p : ℕ) :
    (deRhamComplex A A[X]).ExactAt (p + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ p (p + 1) (p + 2)
    (ComplexShape.prev_eq' _ rfl) (ComplexShape.next_eq' _ rfl),
    ShortComplex.moduleCat_exact_iff]
  intro η _
  obtain ⟨ξ, hξ⟩ := surjective_deRhamDifferential_polynomial A p η
  refine ⟨ξ, ?_⟩
  show ((deRhamComplex A A[X]).d p (p + 1)).hom ξ = η
  rwa [deRhamComplex_d]

/-- Over a `ℚ`-algebra a degree-zero form on `A[X]` is closed exactly when it is constant. -/
theorem deRhamDifferential_polynomial_zero_eq_zero_iff (ξ : ⋀[A[X]]^0 (Ω[A[X]⁄A])) :
    deRhamDifferential (A := A) 0 ξ = 0 ↔
      ∃ a : A, exteriorPower.zeroEquiv A[X] (Ω[A[X]⁄A]) ξ = C a := by
  rw [← (exteriorPower.oneEquiv A[X] (Ω[A[X]⁄A])).map_eq_zero_iff,
    oneEquiv_deRhamDifferential_zero, D_polynomial_eq_zero_iff]
  exact ⟨fun h ↦ ⟨_, h⟩, fun ⟨a, ha⟩ ↦ by rw [ha]; simp⟩

/-- `H^0(Ω^•_{A[X]/A}) = A`: over a `ℚ`-algebra the closed degree-zero forms on `A[X]` are the
constants, a free `A`-module of rank one. -/
def kerDeRhamDifferentialPolynomialZeroEquiv :
    A ≃ₗ[A] LinearMap.ker (deRhamDifferential (A := A) (B := A[X]) 0) :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict _
      ((exteriorPower.zeroEquiv A[X] (Ω[A[X]⁄A])).symm.toLinearMap.restrictScalars A ∘ₗ
        Algebra.linearMap A A[X])
      fun a ↦ by
        rw [LinearMap.mem_ker, deRhamDifferential_polynomial_zero_eq_zero_iff]
        exact ⟨a, by simp [Algebra.linearMap_apply]⟩)
    ⟨fun a b hab ↦ by
      have hab' := Subtype.ext_iff.mp hab
      simpa [Algebra.linearMap_apply] using
        (exteriorPower.zeroEquiv A[X] (Ω[A[X]⁄A])).symm.injective hab',
     fun ξ ↦ by
      obtain ⟨a, ha⟩ := (deRhamDifferential_polynomial_zero_eq_zero_iff A ξ.1).mp
        (LinearMap.mem_ker.mp ξ.2)
      exact ⟨a, Subtype.ext (by
        simp only [LinearMap.codRestrict_apply, LinearMap.coe_comp, Function.comp_apply,
          LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, Algebra.linearMap_apply,
          Polynomial.algebraMap_eq]
        rw [← ha, LinearEquiv.symm_apply_apply])⟩⟩

end Relative

end PolynomialDeRham
