module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The monomial basis of the binary forms of a given degree

Let `R` be a commutative ring.  A *binary form of degree `d`* is a homogeneous polynomial of
degree `d` in two variables `T₀, T₁`.  There are `d + 1` monomials of that degree, namely
`T₀^{d-j} T₁^j` for `0 ≤ j ≤ d`, and this file proves that they are a basis: every binary form
of degree `d` is a combination of them, with coefficients recovered from its own coefficients,
and the only combination of them that vanishes is the trivial one.

Geometrically this is `H⁰(𝐏¹_R, 𝒪(d))`; the identification is
`Stacks.ProjectiveSpace.Cohomology.projectiveLineTwistSectionsBasis`, which transports the basis
built here along the degree-zero row of [Stacks, Tag 01XT].

## Main definitions

* `MvPolynomial.binaryExponent` — the exponent vector of `T₀^{d-j} T₁^j`.
* `MvPolynomial.binaryMonomial` — the monomial `T₀^{d-j} T₁^j`.
* `MvPolynomial.homogeneousBinaryBasis` — **the monomial basis** of the degree-`d` homogeneous
  polynomials in two variables, indexed by `Fin (d + 1)`.

## Main results

* `MvPolynomial.coeff_sum_binaryMonomial` — the coefficient extraction that makes the monomials
  independent.
* `MvPolynomial.eq_sum_binaryMonomial` and `MvPolynomial.exists_eq_sum_binaryMonomial` — a binary
  form of degree `d` is a combination of the degree-`d` monomials.
* `MvPolynomial.eq_zero_of_sum_binaryMonomial_eq_zero` — a vanishing combination of the degree-`d`
  monomials has vanishing coefficients.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

universe u

namespace MvPolynomial

/-! ### The degree-`d` monomials in two variables -/

variable (R : Type u) [CommRing R]

/-- The exponent vector of the monomial `T₀^{d-j} T₁^j` in two variables. -/
def binaryExponent (d j : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 (d - j) + Finsupp.single 1 j

/-- The degree-`d` monomial `T₀^{d-j} T₁^j` in two variables. -/
def binaryMonomial (d j : ℕ) : MvPolynomial (Fin 2) R := X 0 ^ (d - j) * X 1 ^ j

variable {R}

/-- The exponent of `T₀` in `T₀^{d-j} T₁^j` is `d - j`. -/
@[simp]
theorem binaryExponent_apply_zero (d j : ℕ) : binaryExponent d j 0 = d - j := by
  simp [binaryExponent]

/-- The exponent of `T₁` in `T₀^{d-j} T₁^j` is `j`. -/
@[simp]
theorem binaryExponent_apply_one (d j : ℕ) : binaryExponent d j 1 = j := by
  simp [binaryExponent]

/-- The exponent vector remembers the index: the exponent of `T₁` is `j`. -/
theorem binaryExponent_injective {d i j : ℕ} (h : binaryExponent d i = binaryExponent d j) :
    i = j := by
  have h1 := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
  simpa using h1

/-- An exponent vector in two variables of total degree `d` is one of the `d + 1` degree-`d`
exponent vectors. -/
theorem binaryExponent_eq_self {m : Fin 2 →₀ ℕ} {d : ℕ} (hm : m 0 + m 1 = d) :
    binaryExponent d (m 1) = m := by
  refine Finsupp.ext fun i => ?_
  fin_cases i <;> simp [binaryExponent]
  omega

/-- The degree-`d` monomials are the monomials with the degree-`d` exponent vectors. -/
theorem binaryMonomial_eq_monomial (d j : ℕ) :
    binaryMonomial R d j = monomial (binaryExponent d j) 1 := by
  rw [binaryMonomial, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial]
  simp [binaryExponent]

/-- The degree-`d` monomials in two variables are homogeneous of degree `d`. -/
theorem binaryMonomial_mem {d j : ℕ} (hj : j ≤ d) :
    binaryMonomial R d j ∈ homogeneousSubmodule (Fin 2) R d := by
  have h : ((X 0 : MvPolynomial (Fin 2) R) ^ (d - j) * X 1 ^ j).IsHomogeneous
      (1 * (d - j) + 1 * j) :=
    ((isHomogeneous_X R 0).pow _).mul ((isHomogeneous_X R 1).pow _)
  rw [mem_homogeneousSubmodule, binaryMonomial, show 1 * (d - j) + 1 * j = d by omega] at *
  exact h

/-- The total degree of an exponent vector in two variables, as read by the weight function of
`MvPolynomial.IsHomogeneous`. -/
theorem weight_one_eq_finTwo (m : Fin 2 →₀ ℕ) : (Finsupp.weight 1) m = m 0 + m 1 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [Fin.sum_univ_two]

/-! ### Independence and spanning -/

/-- The coefficient of an exponent vector in a combination of the degree-`d` monomials. -/
private theorem coeff_sum_binaryMonomial_eq_ite (d : ℕ) (c : ℕ → R) (m : Fin 2 →₀ ℕ) :
    coeff m (∑ j ∈ Finset.range (d + 1), c j • binaryMonomial R d j) =
      if m 0 + m 1 = d then c (m 1) else 0 := by
  classical
  simp only [binaryMonomial_eq_monomial, smul_monomial, smul_eq_mul, mul_one, coeff_sum,
    coeff_monomial]
  split_ifs with hm
  · have hkey : binaryExponent d (m 1) = m := binaryExponent_eq_self hm
    rw [Finset.sum_eq_single (m 1)]
    · simp [hkey]
    · intro j _ hj
      simp only [ite_eq_right_iff]
      intro h
      exact absurd (binaryExponent_injective (h.trans hkey.symm)) hj
    · intro h
      exact absurd (Finset.mem_range.2 (by omega)) h
  · refine Finset.sum_eq_zero fun j hj => ?_
    simp only [ite_eq_right_iff]
    intro h
    exact absurd (by
      have h0 : m 0 = d - j := by rw [← h, binaryExponent_apply_zero]
      have h1 : m 1 = j := by rw [← h, binaryExponent_apply_one]
      have : j ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      omega) hm

/-- **Extracting the `i`-th coefficient of a combination of the degree-`d` monomials.** This is
the linear independence of the `d + 1` monomials of degree `d` in two variables. -/
theorem coeff_sum_binaryMonomial (d : ℕ) (c : ℕ → R) {i : ℕ} (hi : i ≤ d) :
    coeff (binaryExponent d i) (∑ j ∈ Finset.range (d + 1), c j • binaryMonomial R d j) = c i := by
  simp [coeff_sum_binaryMonomial_eq_ite, Nat.sub_add_cancel hi]

/-- **A binary form of degree `d` is a combination of the `d + 1` degree-`d` monomials**, with
its own coefficients. -/
theorem eq_sum_binaryMonomial (d : ℕ) (p : MvPolynomial (Fin 2) R) (hp : p.IsHomogeneous d) :
    p = ∑ j ∈ Finset.range (d + 1), (coeff (binaryExponent d j) p) • binaryMonomial R d j := by
  refine MvPolynomial.ext _ _ fun m => ?_
  rw [coeff_sum_binaryMonomial_eq_ite]
  split_ifs with hm
  · exact congrArg (fun e => coeff e p) (binaryExponent_eq_self hm).symm
  · by_contra hc
    exact hm ((weight_one_eq_finTwo m).symm.trans (hp hc))

/-- Every homogeneous polynomial of degree `d` in two variables is a linear combination of the
`d + 1` monomials `T₀^{d-j} T₁^j`. -/
theorem exists_eq_sum_binaryMonomial (d : ℕ) (p : MvPolynomial (Fin 2) R)
    (hp : p ∈ homogeneousSubmodule (Fin 2) R d) :
    ∃ c : ℕ → R, p = ∑ j ∈ Finset.range (d + 1), c j • binaryMonomial R d j :=
  ⟨fun j => coeff (binaryExponent d j) p,
    eq_sum_binaryMonomial d p ((mem_homogeneousSubmodule _ _).1 hp)⟩

/-- **The degree-`d` monomials are linearly independent**: a combination of them vanishes only
if every coefficient does. -/
theorem eq_zero_of_sum_binaryMonomial_eq_zero (d : ℕ) (c : ℕ → R)
    (h : ∑ j ∈ Finset.range (d + 1), c j • binaryMonomial R d j = 0) {i : ℕ} (hi : i ≤ d) :
    c i = 0 := by
  rw [← coeff_sum_binaryMonomial d c hi, h, coeff_zero]

/-! ### The monomial basis -/

variable (R)

/-- The degree-`d` monomials in two variables, as a family in the submodule of degree-`d`
homogeneous polynomials. -/
def binaryMonomialFamily (d : ℕ) (j : Fin (d + 1)) : homogeneousSubmodule (Fin 2) R d :=
  ⟨binaryMonomial R d j, binaryMonomial_mem (Nat.lt_succ_iff.1 j.2)⟩

/-- The `j`-th member of the monomial family is the monomial `T₀^{d-j} T₁^j`. -/
@[simp]
theorem coe_binaryMonomialFamily (d : ℕ) (j : Fin (d + 1)) :
    (binaryMonomialFamily R d j : MvPolynomial (Fin 2) R) = binaryMonomial R d j := rfl

/-- The coefficients of a combination of the monomial family, read as a function on `ℕ`. -/
private def extendCoeff (d : ℕ) (g : Fin (d + 1) → R) (j : ℕ) : R :=
  if h : j < d + 1 then g ⟨j, h⟩ else 0

private theorem extendCoeff_coe (d : ℕ) (g : Fin (d + 1) → R) (i : Fin (d + 1)) :
    extendCoeff R d g (i : ℕ) = g i := by
  simp [extendCoeff, i.2]

/-- The coercion to polynomials of a combination of the monomial family. -/
private theorem coe_sum_binaryMonomialFamily (d : ℕ) (g : Fin (d + 1) → R) :
    ((∑ j : Fin (d + 1), g j • binaryMonomialFamily R d j :
        homogeneousSubmodule (Fin 2) R d) : MvPolynomial (Fin 2) R) =
      ∑ j ∈ Finset.range (d + 1), extendCoeff R d g j • binaryMonomial R d j := by
  rw [← Fin.sum_univ_eq_sum_range
    (fun j : ℕ => extendCoeff R d g j • binaryMonomial R d j) (d + 1)]
  simp [extendCoeff_coe, binaryMonomialFamily]

/-- The degree-`d` monomials in two variables are linearly independent in the submodule of
degree-`d` homogeneous polynomials. -/
theorem linearIndependent_binaryMonomialFamily (d : ℕ) :
    LinearIndependent R (binaryMonomialFamily R d) := by
  classical
  refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
  have hval : ∑ j ∈ Finset.range (d + 1), extendCoeff R d g j • binaryMonomial R d j = 0 := by
    rw [← coe_sum_binaryMonomialFamily R d g, hg, Submodule.coe_zero]
  have h0 : extendCoeff R d g (i : ℕ) = 0 :=
    eq_zero_of_sum_binaryMonomial_eq_zero d (extendCoeff R d g) hval (Nat.lt_succ_iff.1 i.2)
  rwa [extendCoeff_coe] at h0

/-- The degree-`d` monomials in two variables span the submodule of degree-`d` homogeneous
polynomials. -/
theorem span_binaryMonomialFamily (d : ℕ) :
    ⊤ ≤ Submodule.span R (Set.range (binaryMonomialFamily R d)) := by
  classical
  intro p _
  obtain ⟨c, hc⟩ := exists_eq_sum_binaryMonomial d (p : MvPolynomial (Fin 2) R) p.2
  refine (Submodule.mem_span_range_iff_exists_fun R).2 ⟨fun j : Fin (d + 1) => c (j : ℕ), ?_⟩
  refine Subtype.ext (Eq.trans ?_ hc.symm)
  rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ => c j • binaryMonomial R d j) (d + 1)]
  simp [binaryMonomialFamily]

/-- **The monomial basis of the binary forms of degree `d`.** The degree-`d` homogeneous
polynomials in two variables are free of rank `d + 1` on the monomials `T₀^{d-j} T₁^j`. -/
def homogeneousBinaryBasis (d : ℕ) :
    Module.Basis (Fin (d + 1)) R (homogeneousSubmodule (Fin 2) R d) :=
  Module.Basis.mk (linearIndependent_binaryMonomialFamily R d) (span_binaryMonomialFamily R d)

/-- The `j`-th vector of the monomial basis is the monomial `T₀^{d-j} T₁^j`. -/
@[simp]
theorem coe_homogeneousBinaryBasis (d : ℕ) (j : Fin (d + 1)) :
    ((homogeneousBinaryBasis R d j : homogeneousSubmodule (Fin 2) R d) :
      MvPolynomial (Fin 2) R) = binaryMonomial R d j := by
  rw [homogeneousBinaryBasis, Module.Basis.mk_apply, coe_binaryMonomialFamily]

/-- The degree-`d` homogeneous polynomials in two variables are a free module. -/
instance free_homogeneousSubmodule_finTwo (d : ℕ) :
    Module.Free R (homogeneousSubmodule (Fin 2) R d) :=
  Module.Free.of_basis (homogeneousBinaryBasis R d)

end MvPolynomial
