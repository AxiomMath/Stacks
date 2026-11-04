module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraGrading
public import StacksFrontier.LinearAlgebra.SymmetricAlgebra.AdjoinDegreeOne

/-!
# Adjoining a degree-one variable is graded

`SymmetricAlgebra.prodRightEquivPolynomial` identifies `Sym_R(M ⊕ R)` with `(Sym_R M)[T]`. This
file shows that identification is graded, for the grading of `(Sym_R M)[T]` in which `T` has
degree one and a coefficient in `Sym^i_R(M)` contributes degree `i`: the degree-`n` part is the
span of the monomials `C a * T^j` with `j ≤ n` and `a ∈ Sym^{n-j}_R(M)`, and the isomorphism
carries `Sym^n_R(M ⊕ R)` onto exactly that.

Neither Mathlib nor this repository grades a polynomial ring over a graded base — the only
grading of an `A[X]` here, `PolynomialDeRham.weightGrading`, puts the whole of `A` in degree zero
and carries no graded-ring instance — so the degree-`n` part is defined here.

## Main definitions

* `SymmetricAlgebra.polyDegreePart`: **the degree-`n` part of `(Sym_R M)[T]`** with `T` in
  degree one, together with its `SetLike.GradedMonoid` instance.

## Main results

* `SymmetricAlgebra.polyDegreePart_mul_le`: the parts multiply as a grading does.
* `SymmetricAlgebra.inlAlgHom_symmetricPower_le`: the first summand's algebra map preserves the
  symmetric powers.
* `SymmetricAlgebra.map_symmetricPower_eq_polyDegreePart`: **the isomorphism
  `Sym_R(M ⊕ R) ≅ (Sym_R M)[T]` carries `Sym^n_R(M ⊕ R)` onto the degree-`n` part**, so it is an
  isomorphism of graded rings.

## Implementation notes

The degree-`n` part is a span of monomials rather than a condition on coefficients. The
coefficientwise description would have to say both that `coeff j` lies in `Sym^{n-j}` for `j ≤ n`
and that it vanishes for `j > n`, the truncated subtraction of `ℕ` making the first clause vacuous
beyond `n`; the span says both at once and is what the two inclusions are proved on.

Both inclusions are checked on spanning sets. For the forward one the spanning set of
`Sym^n_R(M ⊕ R)` is the products of `n` degree-one generators
(`SymmetricAlgebra.symmetricPower_eq_span_prod_ι`), each of which goes to a degree-one polynomial,
and `SetLike.prod_mem_graded` against the `SetLike.GradedMonoid` instance assembles the product.
For the reverse one the generator `C a * T^j` is hit by `inlAlgHom a * ι (0, 1) ^ j`, whose
membership in `Sym^n_R(M ⊕ R)` is the gradedness of multiplication on the symmetric algebra.
-/

@[expose] public section

open Polynomial

namespace SymmetricAlgebra

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-- **The degree-`n` part of `(Sym_R M)[T]`**, the variable `T` having degree one and a
coefficient in `Sym^i_R(M)` contributing degree `i`: the span of the monomials `C a * T^j` with
`j ≤ n` and `a ∈ Sym^{n-j}_R(M)`. -/
noncomputable def polyDegreePart (n : ℕ) : Submodule R ((SymmetricAlgebra R M)[X]) :=
  Submodule.span R {p | ∃ (j : ℕ) (a : SymmetricAlgebra R M),
    j ≤ n ∧ a ∈ SymPow.symmetricPower (n - j) R M ∧ p = C a * X ^ j}

variable {R M}

/-- The monomial `C a * T^j` lies in the degree-`n` part when `j ≤ n` and `a ∈ Sym^{n-j}_R(M)`.
-/
theorem mem_polyDegreePart_of (n j : ℕ) (hj : j ≤ n) (a : SymmetricAlgebra R M)
    (ha : a ∈ SymPow.symmetricPower (n - j) R M) :
    C a * X ^ j ∈ polyDegreePart R M n :=
  Submodule.subset_span ⟨j, a, hj, ha, rfl⟩

/-- The unit of `Sym_R M` lies in `Sym^0_R(M)`. -/
theorem one_mem_symmetricPower_zero :
    (1 : SymmetricAlgebra R M) ∈ SymPow.symmetricPower 0 R M := by
  simp [SymPow.symmetricPower]

/-- The generator `ι m` of `Sym_R M` lies in `Sym^1_R(M)`. -/
theorem ι_mem_symmetricPower_one (m : M) :
    ι R M m ∈ SymPow.symmetricPower 1 R M := by
  simp [SymPow.symmetricPower]

/-- **The parts of `(Sym_R M)[T]` multiply as a grading does.** -/
theorem polyDegreePart_mul_le (m n : ℕ) :
    polyDegreePart R M m * polyDegreePart R M n ≤ polyDegreePart R M (m + n) := by
  rw [polyDegreePart, polyDegreePart, Submodule.span_mul_span, Submodule.span_le]
  rintro p ⟨u, ⟨i, a, hi, ha, rfl⟩, v, ⟨j, b, hj, hb, rfl⟩, rfl⟩
  have hab : a * b ∈ SymPow.symmetricPower (m + n - (i + j)) R M := by
    have hsub : m - i + (n - j) = m + n - (i + j) := by omega
    rw [← hsub]
    exact symmetricPower_mul_symmetricPower_le R M (m - i) (n - j)
      (Submodule.mul_mem_mul ha hb)
  have key : (C a * X ^ i : (SymmetricAlgebra R M)[X]) * (C b * X ^ j)
      ∈ polyDegreePart R M (m + n) := by
    have hmul : (C a * X ^ i : (SymmetricAlgebra R M)[X]) * (C b * X ^ j)
        = C (a * b) * X ^ (i + j) := by
      rw [map_mul]; ring
    rw [hmul]
    exact mem_polyDegreePart_of _ _ (by omega) _ hab
  exact key

/-- The parts `SymmetricAlgebra.polyDegreePart R M n` form a graded monoid on `(Sym_R M)[T]`. -/
noncomputable instance : SetLike.GradedMonoid (polyDegreePart R M) where
  one_mem := by
    have h : (1 : (SymmetricAlgebra R M)[X]) = C 1 * X ^ 0 := by simp
    rw [h]
    exact mem_polyDegreePart_of 0 0 le_rfl _ one_mem_symmetricPower_zero
  mul_mem := by
    intro i j a b ha hb
    exact polyDegreePart_mul_le i j (Submodule.mul_mem_mul ha hb)

/-- A degree-one generator of `M ⊕ R` goes to a degree-one polynomial. -/
theorem prodRightToPolynomialGen_mem (mr : M × R) :
    prodRightToPolynomialGen R M mr ∈ polyDegreePart R M 1 := by
  obtain ⟨m, r⟩ := mr
  rw [prodRightToPolynomialGen_apply]
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ ?_)
  · have h : C (ι R M m) = C (ι R M m) * X ^ 0 := by simp
    rw [h]
    exact mem_polyDegreePart_of 1 0 (by omega) _ (ι_mem_symmetricPower_one m)
  · have h : (X : (SymmetricAlgebra R M)[X]) = C 1 * X ^ 1 := by simp
    rw [h]
    exact mem_polyDegreePart_of 1 1 (by omega) _ one_mem_symmetricPower_zero

/-- A product of `n` degree-one generators goes to the degree-`n` part. -/
theorem prod_prodRightToPolynomialGen_mem (n : ℕ) (s : Fin n → M × R) :
    ∏ i : Fin n, prodRightToPolynomialGen R M (s i) ∈ polyDegreePart R M n := by
  have h := SetLike.prod_mem_graded (F := Finset.univ) (polyDegreePart R M)
    (fun _ : Fin n => 1) (fun i : Fin n => prodRightToPolynomialGen R M (s i))
    fun i _ => prodRightToPolynomialGen_mem (s i)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using h

/-- An algebra map sends `Sym^n_R(N)` into `P` once it sends each product of `n` generators
into `P`. -/
private theorem map_symmetricPower_le_of_prod_mem {N B : Type*} [AddCommGroup N] [Module R N]
    [CommRing B] [Algebra R B] (f : SymmetricAlgebra R N →ₐ[R] B) (P : Submodule R B) (n : ℕ)
    (h : ∀ s : Fin n → N, ∏ i, f (ι R N (s i)) ∈ P) :
    Submodule.map f.toLinearMap (SymPow.symmetricPower n R N) ≤ P := by
  rw [symmetricPower_eq_span_prod_ι, Submodule.map_span, Submodule.span_le]
  rintro p ⟨q, ⟨s, rfl⟩, rfl⟩
  rw [AlgHom.toLinearMap_apply, map_prod]
  exact h s

/-- The isomorphism `Sym_R(M ⊕ R) ≅ (Sym_R M)[T]` carries `Sym^n_R(M ⊕ R)` into the degree-`n`
part. -/
theorem map_symmetricPower_le_polyDegreePart (n : ℕ) :
    Submodule.map (prodRightEquivPolynomial R M).toLinearMap
        (SymPow.symmetricPower n R (M × R)) ≤ polyDegreePart R M n := by
  refine map_symmetricPower_le_of_prod_mem (prodRightEquivPolynomial R M).toAlgHom _ n fun s => ?_
  have hfac : ∀ i : Fin n, (prodRightEquivPolynomial R M).toAlgHom (ι R (M × R) (s i))
      = prodRightToPolynomialGen R M (s i) := fun i => by
    obtain ⟨m, r⟩ := s i
    rw [AlgEquiv.toAlgHom_apply, prodRightEquivPolynomial_ι, prodRightToPolynomialGen_apply]
  simp only [hfac]
  exact prod_prodRightToPolynomialGen_mem n s

/-- **The algebra map of the first summand preserves the symmetric powers.** -/
theorem inlAlgHom_symmetricPower_le (k : ℕ) :
    Submodule.map (inlAlgHom R M).toLinearMap (SymPow.symmetricPower k R M)
      ≤ SymPow.symmetricPower k R (M × R) := by
  refine map_symmetricPower_le_of_prod_mem (inlAlgHom R M) _ k fun s => ?_
  simpa only [inlAlgHom_ι] using prod_ι_mem R (fun i : Fin k => ((s i, 0) : M × R))

/-- The `j`-th power of the generator at `(0, 1)` lies in the `j`-th symmetric power. -/
theorem ι_zero_one_pow_mem (j : ℕ) :
    (ι R (M × R) (0, 1)) ^ j ∈ SymPow.symmetricPower j R (M × R) := by
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    prod_ι_mem R (fun _ : Fin j => ((0, 1) : M × R))

/-- The degree-`n` part of `(Sym_R M)[T]` lies in the image of `Sym^n_R(M ⊕ R)` under the
isomorphism `Sym_R(M ⊕ R) ≅ (Sym_R M)[T]`. -/
theorem polyDegreePart_le_map (n : ℕ) :
    polyDegreePart R M n ≤ Submodule.map (prodRightEquivPolynomial R M).toLinearMap
      (SymPow.symmetricPower n R (M × R)) := by
  rw [polyDegreePart, Submodule.span_le]
  rintro p ⟨j, a, hj, ha, rfl⟩
  refine ⟨inlAlgHom R M a * ι R (M × R) (0, 1) ^ j, ?_, ?_⟩
  · have h1 : inlAlgHom R M a ∈ SymPow.symmetricPower (n - j) R (M × R) :=
      inlAlgHom_symmetricPower_le (n - j) ⟨a, ha, rfl⟩
    have hsum : n - j + j = n := by omega
    rw [← hsum]
    exact symmetricPower_mul_symmetricPower_le R (M × R) (n - j) j
      (Submodule.mul_mem_mul h1 (ι_zero_one_pow_mem j))
  · rw [AlgEquiv.toLinearMap_apply, map_mul, map_pow, prodRightEquivPolynomial_inlAlgHom,
      prodRightEquivPolynomial_ι_zero_one]

/-- **Adjoining a degree-one variable is graded.** The isomorphism
`Sym_R(M ⊕ R) ≅ (Sym_R M)[T]` carries the `n`-th symmetric power onto the degree-`n` part of
`(Sym_R M)[T]`, in which `T` has degree one. -/
theorem map_symmetricPower_eq_polyDegreePart (n : ℕ) :
    Submodule.map (prodRightEquivPolynomial R M).toLinearMap
        (SymPow.symmetricPower n R (M × R)) = polyDegreePart R M n :=
  le_antisymm (map_symmetricPower_le_polyDegreePart n) (polyDegreePart_le_map n)

end SymmetricAlgebra

end
