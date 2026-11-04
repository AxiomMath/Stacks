module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.FormPolynomial

/-!
# Homogenization at the first variable

`RationalDoublePoints/FormPolynomial.lean` dehomogenizes at the first variable: the `k`-algebra
map `AlgebraicGeometry.dehomogenizeFirst` sends `t₁ ↦ 1` and `tₚ₊₁ ↦ yₚ₊₁`, computing
`q(1, y₂, …, y_{m+1})` on a form `q`. This file provides a section of it — every polynomial in
`y₂, …, y_{m+1}` is the dehomogenization of a *homogeneous* polynomial in `t₁, …, t_{m+1}` —
together with the identity that makes a homogeneous polynomial of degree `n` behave like a
function on lines: scaling the point by `c` scales the value by `cⁿ`.

## Main definitions

* `AlgebraicGeometry.homogenizeFirst`: for `n` at least the total degree, the homogeneous
  polynomial of degree `n` in `t₁, …, t_{m+1}` whose dehomogenization is the given polynomial in
  `y₂, …, y_{m+1}`.

## Main results

* `AlgebraicGeometry.aeval_mul_of_isHomogeneous`: a homogeneous polynomial of degree `n`
  evaluated at a point scaled by `c` is `cⁿ` times its value at the point.
* `AlgebraicGeometry.dehomogenizeFirst_homogenizeFirst`: homogenizing in any degree at least the
  total degree and dehomogenizing again returns the polynomial.
* `AlgebraicGeometry.exists_isHomogeneous_dehomogenizeFirst_eq`: **every polynomial in
  `y₂, …, y_{m+1}` is the dehomogenization of a homogeneous polynomial.**

## Implementation notes

Mathlib has no homogenization operator for `MvPolynomial`. `Polynomial.homogenize` goes from the
univariate `R[X]` to `MvPolynomial (Fin 2) R`, which is the case `m = 1` of what is needed here
and does not generalize along its own construction, since it is written with the explicit
two-variable monomial `fun₀ | 0 => m | 1 => n - m`.

`homogenizeFirst` is therefore defined degree by degree, as
`∑ⱼ t₁^(n-j) · (homogeneousComponent j f)(t₂, …, t_{m+1})`, which avoids computing the degree of
a `Finsupp.cons`: each summand is visibly homogeneous of degree `(n - j) + j = n`, and each
summand dehomogenizes to its own homogeneous component because `t₁ ↦ 1` and the renaming
`tₚ₊₁ ↦ yₚ₊₁` is inverse to `dehomogenizeFirst` on polynomials not involving `t₁`. Mathlib's
`MvPolynomial.sum_homogeneousComponent` then reassembles `f`.

## References

* [Stacks Project, Tag 0BGE](https://stacks.math.columbia.edu/tag/0BGE)
-/

@[expose] public noncomputable section

open MvPolynomial

namespace AlgebraicGeometry

/-! ### Evaluating a homogeneous polynomial at a scaled point -/

/-- **A homogeneous polynomial of degree `n` is `n`-homogeneous as a function:** evaluated at a
point scaled by `c`, its value is `cⁿ` times its value at the point. -/
public theorem aeval_mul_of_isHomogeneous {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    [Algebra R S] {P : MvPolynomial σ R} {n : ℕ} (hP : P.IsHomogeneous n) (c : S) (z : σ → S) :
    MvPolynomial.aeval (fun i => c * z i) P = c ^ n * MvPolynomial.aeval z P := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq,
    MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = n := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hd) (hP.coeff_eq_zero h)
  have hprod : ∏ i ∈ d.support, (c * z i) ^ d i
      = c ^ n * ∏ i ∈ d.support, z i ^ d i := by
    rw [← hdeg, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => mul_pow _ _ _
  rw [hprod]
  ring

/-! ### Homogenization -/

/-- **Homogenization at the first variable in degree `n`:** the polynomial
`∑ⱼ t₁^(n-j) · fⱼ(t₂, …, t_{m+1})`, where `fⱼ` is the degree-`j` homogeneous component of `f`.
For `n` at least the total degree of `f` it is the homogeneous polynomial of degree `n` whose
dehomogenization is `f`. -/
public def homogenizeFirst (k : Type*) [CommRing k] {m : ℕ} (n : ℕ)
    (f : MvPolynomial (Fin m) k) : MvPolynomial (Fin (m + 1)) k :=
  ∑ j ∈ Finset.range (n + 1), MvPolynomial.X 0 ^ (n - j) *
    MvPolynomial.rename Fin.succ (MvPolynomial.homogeneousComponent j f)

/-- The homogenization in degree `n` is homogeneous of degree `n`, whatever `n` is. -/
public theorem isHomogeneous_homogenizeFirst (k : Type*) [CommRing k] {m : ℕ} (n : ℕ)
    (f : MvPolynomial (Fin m) k) : (homogenizeFirst k n f).IsHomogeneous n := by
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have h := (MvPolynomial.isHomogeneous_X_pow (R := k) (0 : Fin (m + 1)) (n - j)).mul
    (MvPolynomial.IsHomogeneous.rename_isHomogeneous
      (f := Fin.succ) (MvPolynomial.homogeneousComponent_isHomogeneous j f))
  rwa [Nat.sub_add_cancel hjn] at h

/-- Renaming `yₚ ↦ tₚ₊₁` is a section of dehomogenization: the variable `t₁` does not occur in
the image, so setting it to `1` changes nothing. -/
public theorem dehomogenizeFirst_rename_succ (k : Type*) [CommRing k] {m : ℕ}
    (f : MvPolynomial (Fin m) k) :
    dehomogenizeFirst k m (MvPolynomial.rename Fin.succ f) = f := by
  rw [dehomogenizeFirst, MvPolynomial.aeval_rename,
    show (Fin.cons 1 MvPolynomial.X : Fin (m + 1) → MvPolynomial (Fin m) k) ∘ Fin.succ
      = MvPolynomial.X from funext fun p => Fin.cons_succ _ _ _,
    MvPolynomial.aeval_X_left_apply]

/-- **Homogenizing in a degree at least the total degree and dehomogenizing again returns the
polynomial.** -/
public theorem dehomogenizeFirst_homogenizeFirst (k : Type*) [CommRing k] {m n : ℕ}
    {f : MvPolynomial (Fin m) k} (hn : f.totalDegree ≤ n) :
    dehomogenizeFirst k m (homogenizeFirst k n f) = f := by
  rw [homogenizeFirst, map_sum]
  have hterm : ∀ j ∈ Finset.range (n + 1),
      dehomogenizeFirst k m (MvPolynomial.X 0 ^ (n - j) *
        MvPolynomial.rename Fin.succ (MvPolynomial.homogeneousComponent j f))
        = MvPolynomial.homogeneousComponent j f := fun j _ => by
    rw [map_mul, map_pow, dehomogenizeFirst_X_zero, one_pow, one_mul,
      dehomogenizeFirst_rename_succ]
  have hsum : ∑ j ∈ Finset.range (f.totalDegree + 1), MvPolynomial.homogeneousComponent j f
      = ∑ j ∈ Finset.range (n + 1), MvPolynomial.homogeneousComponent j f := by
    refine Finset.sum_subset (fun j hj => ?_) (fun j _ hj => ?_)
    · rw [Finset.mem_range] at hj ⊢; omega
    · rw [Finset.mem_range] at hj
      exact MvPolynomial.homogeneousComponent_eq_zero (φ := f) (n := j) (by omega)
  rw [Finset.sum_congr rfl hterm, ← hsum, MvPolynomial.sum_homogeneousComponent]

/-- **Every polynomial in `y₂, …, y_{m+1}` is the dehomogenization of a homogeneous polynomial
in `t₁, …, t_{m+1}`.** -/
public theorem exists_isHomogeneous_dehomogenizeFirst_eq (k : Type*) [CommRing k] {m : ℕ}
    (f : MvPolynomial (Fin m) k) :
    ∃ (n : ℕ) (P : MvPolynomial (Fin (m + 1)) k), P.IsHomogeneous n ∧
      dehomogenizeFirst k m P = f :=
  ⟨f.totalDegree, homogenizeFirst k f.totalDegree f,
    isHomogeneous_homogenizeFirst k _ f, dehomogenizeFirst_homogenizeFirst k le_rfl⟩

end AlgebraicGeometry

end
