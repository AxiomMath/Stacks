module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The monomial basis of the homogeneous polynomials of a given degree

Let `R` be a commutative ring, `σ` a type of variables and `n : ℕ`. A polynomial is homogeneous
of degree `n` exactly when every multidegree in its support has total degree `n`, which is
`MvPolynomial.homogeneousSubmodule_eq_finsupp_supported`. So the degree-`n` part of
`MvPolynomial σ R` is free on the degree-`n` monomials: a homogeneous polynomial is the sum of
its own terms, and the coefficients of that sum are its own coefficients.

The identification of the degree-`n` part with the finitely supported families of coefficients
indexed by the degree-`n` multidegrees is `MvPolynomial.homogeneousSubmoduleEquivFinsupp`, and
`MvPolynomial.basisHomogeneousSubmodule` is the resulting basis. Both are computed on monomials
below: the basis element at `e` is the monic monomial with exponents `e`, the family attached to
a homogeneous polynomial is its coefficient function, and the inverse equivalence sends
`Finsupp.single e r` to `r` times that monomial.

A family of coefficients assembles into a form in the other orientation,
`({e : σ →₀ ℕ // e.degree = n} →₀ R) ≃ₗ[R] homogeneousSubmodule σ R n`, which is
`(MvPolynomial.homogeneousSubmoduleEquivFinsupp σ R n).symm`; the lemmas below are stated on
that inverse, so they apply to it without unfolding anything.

When `σ` is finite the degree-`n` multidegrees form a finite set (`Finsupp.finite_of_degree_eq`,
used through Mathlib's `MvPolynomial.homogeneousSubmodule_fg`), so the degree-`n` part is then a
finite free module.

## Main definitions

* `MvPolynomial.homogeneousSubmoduleEquivFinsupp`: the degree-`n` homogeneous part is the module
  of finitely supported coefficient families indexed by the degree-`n` multidegrees.
* `MvPolynomial.basisHomogeneousSubmodule`: the monomial basis of the degree-`n` homogeneous
  part.

## Main results

* `MvPolynomial.homogeneousSubmoduleEquivFinsupp_apply` and
  `MvPolynomial.coe_homogeneousSubmoduleEquivFinsupp_symm_single`: the equivalence and its
  inverse on a coefficient and on a monomial.
* `MvPolynomial.coeff_coe_homogeneousSubmoduleEquivFinsupp_symm`: every coefficient of the
  polynomial attached to a coefficient family.
* `MvPolynomial.coe_basisHomogeneousSubmodule_apply` and
  `MvPolynomial.repr_basisHomogeneousSubmodule`: the basis element at a multidegree, and the
  coordinates of a homogeneous polynomial.
* `MvPolynomial.instFreeHomogeneousSubmodule` and
  `MvPolynomial.instFiniteHomogeneousSubmodule`: the degree-`n` part is free, and finite when
  the variables are.
-/

@[expose] public section

namespace MvPolynomial

variable (σ R : Type*) [CommRing R] (n : ℕ)

/-- The degree-`n` homogeneous part of a polynomial ring is the module of finitely
supported families of coefficients indexed by the degree-`n` monomials. -/
@[sga "7 XXII 4.0"]
noncomputable def homogeneousSubmoduleEquivFinsupp :
    homogeneousSubmodule σ R n ≃ₗ[R] ({d : σ →₀ ℕ | d.degree = n} →₀ R) :=
  (LinearEquiv.ofEq _ _ (homogeneousSubmodule_eq_finsupp_supported σ R n)).trans
    (AddMonoidAlgebra.supportedEquivFinsupp {d : σ →₀ ℕ | d.degree = n})

/-- The monomial basis of the degree-`n` homogeneous part of a polynomial ring. -/
noncomputable def basisHomogeneousSubmodule :
    Module.Basis {d : σ →₀ ℕ | d.degree = n} R (homogeneousSubmodule σ R n) :=
  Finsupp.basisSingleOne.map (homogeneousSubmoduleEquivFinsupp σ R n).symm

/-- The degree-`n` homogeneous part of a polynomial ring is a free module. -/
instance instFreeHomogeneousSubmodule : Module.Free R (homogeneousSubmodule σ R n) :=
  Module.Free.of_basis (basisHomogeneousSubmodule σ R n)

/-- With finitely many variables, the degree-`n` homogeneous part of a polynomial ring is a
finite module. -/
instance instFiniteHomogeneousSubmodule [Finite σ] :
    Module.Finite R (homogeneousSubmodule σ R n) :=
  Module.Finite.iff_fg.2 (homogeneousSubmodule_fg σ R n)

variable {σ R n}

/-- The coefficient family attached to a homogeneous polynomial is its coefficient function. -/
@[simp]
theorem homogeneousSubmoduleEquivFinsupp_apply (p : homogeneousSubmodule σ R n)
    (d : {d : σ →₀ ℕ | d.degree = n}) :
    homogeneousSubmoduleEquivFinsupp σ R n p d = (p : MvPolynomial σ R).coeff d := rfl

/-- The polynomial attached to a single coefficient is a monomial. -/
@[simp, sga "7 XXII 4.0" "partial"]
theorem coe_homogeneousSubmoduleEquivFinsupp_symm_single
    (d : {d : σ →₀ ℕ | d.degree = n}) (r : R) :
    (((homogeneousSubmoduleEquivFinsupp σ R n).symm (Finsupp.single d r) :
        homogeneousSubmodule σ R n) : MvPolynomial σ R) = monomial (d : σ →₀ ℕ) r := by
  simp [homogeneousSubmoduleEquivFinsupp, AddMonoidAlgebra.supportedEquivFinsupp,
    ← single_eq_monomial, ← AddMonoidAlgebra.ofCoeff_single]

/-- Every coefficient of the polynomial attached to a coefficient family: at a multidegree of
total degree `n` it is the value of the family, and elsewhere it vanishes. -/
theorem coeff_coe_homogeneousSubmoduleEquivFinsupp_symm
    (f : {d : σ →₀ ℕ | d.degree = n} →₀ R) (e : σ →₀ ℕ) :
    ((((homogeneousSubmoduleEquivFinsupp σ R n).symm f :
        homogeneousSubmodule σ R n) : MvPolynomial σ R)).coeff e =
      if h : e.degree = n then f ⟨e, h⟩ else 0 := by
  by_cases h : e.degree = n
  · rw [dite_eq_left h]
    exact DFunLike.congr_fun
      ((homogeneousSubmoduleEquivFinsupp σ R n).apply_symm_apply f) ⟨e, h⟩
  · rw [dite_eq_right h]
    exact ((mem_homogeneousSubmodule _ _).1
      ((homogeneousSubmoduleEquivFinsupp σ R n).symm f).2).coeff_eq_zero h

/-- **The monomial basis of the degree-`n` homogeneous part of a polynomial ring, evaluated at a
multidegree.** `MvPolynomial.basisHomogeneousSubmodule σ R n` is transported from the standard
basis of the finitely supported functions on the degree-`n` monomials, so its value at `d` is the
monic monomial with exponents `d`. -/
@[simp]
theorem coe_basisHomogeneousSubmodule_apply (d : {d : σ →₀ ℕ | d.degree = n}) :
    ((basisHomogeneousSubmodule σ R n d : homogeneousSubmodule σ R n) : MvPolynomial σ R) =
      monomial (d : σ →₀ ℕ) 1 := by
  simp [basisHomogeneousSubmodule]

/-- The coordinates in the monomial basis are the coefficients. -/
theorem repr_basisHomogeneousSubmodule :
    (basisHomogeneousSubmodule σ R n).repr = homogeneousSubmoduleEquivFinsupp σ R n := by
  ext p d
  simp [basisHomogeneousSubmodule]

/-- The coordinate of a homogeneous polynomial at a degree-`n` multidegree is its coefficient
there. -/
@[simp]
theorem basisHomogeneousSubmodule_repr_apply (p : homogeneousSubmodule σ R n)
    (d : {d : σ →₀ ℕ | d.degree = n}) :
    (basisHomogeneousSubmodule σ R n).repr p d = (p : MvPolynomial σ R).coeff d := by
  rw [repr_basisHomogeneousSubmodule, homogeneousSubmoduleEquivFinsupp_apply]

end MvPolynomial
