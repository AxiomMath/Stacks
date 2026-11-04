module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

/-!
# Adjoining a degree-one variable to a symmetric algebra

For a module `M` over a commutative ring `R` the symmetric algebra of `M ⊕ R` is the polynomial
algebra over the symmetric algebra of `M`,

`Sym_R(M ⊕ R) ≅ (Sym_R M)[T]`,

the variable `T` being the image of the generator `(0, 1)` of the second summand. This file
constructs that isomorphism.

## Main definitions

* `SymmetricAlgebra.inlAlgHom`: the algebra map `Sym_R(M) ⟶ Sym_R(M ⊕ R)` induced by the
  inclusion `m ↦ (m, 0)` of the first summand.
* `SymmetricAlgebra.prodRightEquivPolynomial`: **the isomorphism
  `Sym_R(M ⊕ R) ≅ (Sym_R M)[T]`**.

## Main results

* `SymmetricAlgebra.prodRightEquivPolynomial_ι`,
  `SymmetricAlgebra.prodRightEquivPolynomial_symm_C` and
  `SymmetricAlgebra.prodRightEquivPolynomial_symm_X`: the isomorphism carries the generator
  `(m, r)` to `C (ι m) + r • T`, a constant `C a` back to the image of `a` along the first summand,
  and the variable `T` back to the generator `(0, 1)`.

## Implementation notes

The second summand is `R` itself rather than a free module of rank one on a chosen basis, which
is what makes the statement an isomorphism of algebras over `R` with no basis in sight: the
generator adjoined is `(0, 1)`, and `Polynomial.aevalTower` is the universal property of
`(Sym_R M)[T]` as an `R`-algebra rather than as a `Sym_R M`-algebra, so no intermediate
`Algebra (Sym_R M) (Sym_R (M × R))` instance has to be introduced.

Both directions come from universal properties and nothing else. A map out of `Sym_R(M ⊕ R)` is a
linear map out of `M ⊕ R`, so the forward direction is `SymmetricAlgebra.lift` applied to
`(m, r) ↦ C (ι m) + r • T`; a map out of a polynomial algebra is an algebra map on coefficients
together with a value for the variable, so the inverse is `Polynomial.aevalTower` applied to the
algebra map induced by `m ↦ (m, 0)` and to the generator `(0, 1)`. That the two are mutually
inverse is checked on generators by `SymmetricAlgebra.algHom_ext` and `Polynomial.algHom_ext'`.

Nothing here is graded. Under this isomorphism the grading of `Sym_R(M ⊕ R)` by its symmetric
powers corresponds to the grading of `(Sym_R M)[T]` in which `T` has degree one and a coefficient
in `Sym^i_R(M)` contributes degree `i`; that correspondence is a separate statement and is not
proved here.
-/

@[expose] public section

open Polynomial

namespace SymmetricAlgebra

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-- The linear map `M ⊕ R ⟶ (Sym_R M)[T]` sending `(m, r)` to `C (ι m) + r • T`. -/
noncomputable def prodRightToPolynomialGen : M × R →ₗ[R] (SymmetricAlgebra R M)[X] :=
  LinearMap.coprod
    ((CAlgHom (R := R) (A := SymmetricAlgebra R M)).toLinearMap ∘ₗ ι R M)
    (LinearMap.toSpanSingleton R _ (X : (SymmetricAlgebra R M)[X]))

/-- `SymmetricAlgebra.prodRightToPolynomialGen` sends `(m, r)` to `C (ι m) + r • T`. -/
@[simp]
theorem prodRightToPolynomialGen_apply (m : M) (r : R) :
    prodRightToPolynomialGen R M (m, r) = C (ι R M m) + r • X :=
  rfl

/-- **The algebra map `Sym_R(M) ⟶ Sym_R(M ⊕ R)`** induced by the inclusion `m ↦ (m, 0)` of the
first summand. -/
noncomputable def inlAlgHom : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R (M × R) :=
  lift (ι R (M × R) ∘ₗ LinearMap.inl R M R)

/-- `SymmetricAlgebra.inlAlgHom` carries the generator at `m` to the generator at `(m, 0)`. -/
@[simp]
theorem inlAlgHom_ι (m : M) : inlAlgHom R M (ι R M m) = ι R (M × R) (m, 0) := by
  simp [inlAlgHom]

/-- The generator of `M ⊕ R` at `(0, r)` is `r` times the generator at `(0, 1)`. -/
theorem ι_zero_right (r : R) : ι R (M × R) (0, r) = r • ι R (M × R) (0, 1) := by
  have h : ((0 : M), r) = r • ((0 : M), (1 : R)) := by ext <;> simp
  rw [h, map_smul]

/-- The generator of `M ⊕ R` at `(m, r)` splits as the generator at `(m, 0)` plus `r` times the
generator at `(0, 1)`. -/
theorem ι_prod_eq (m : M) (r : R) :
    ι R (M × R) (m, r) = ι R (M × R) (m, 0) + r • ι R (M × R) (0, 1) := by
  rw [← ι_zero_right, ← map_add]
  congr 1
  ext <;> simp

/-- **Adjoining a degree-one variable: `Sym_R(M ⊕ R) ≅ (Sym_R M)[T]`.** The generator at `(m, r)`
goes to `C (ι m) + r • T`, and the variable `T` comes from the generator at `(0, 1)`. -/
noncomputable def prodRightEquivPolynomial :
    SymmetricAlgebra R (M × R) ≃ₐ[R] (SymmetricAlgebra R M)[X] :=
  AlgEquiv.ofAlgHom (lift (prodRightToPolynomialGen R M))
    (aevalTower (inlAlgHom R M) (ι R (M × R) (0, 1)))
    (by
      refine Polynomial.algHom_ext' (SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => ?_)) ?_
      · change (lift (prodRightToPolynomialGen R M))
            ((aevalTower (inlAlgHom R M) (ι R (M × R) (0, 1))) (C (ι R M m))) = C (ι R M m)
        rw [aevalTower_C, inlAlgHom_ι, lift_ι_apply, prodRightToPolynomialGen_apply, zero_smul,
          add_zero]
      · change (lift (prodRightToPolynomialGen R M))
            ((aevalTower (inlAlgHom R M) (ι R (M × R) (0, 1))) X) = X
        rw [aevalTower_X, lift_ι_apply, prodRightToPolynomialGen_apply, map_zero, map_zero,
          one_smul, zero_add])
    (SymmetricAlgebra.algHom_ext (LinearMap.ext fun mr => by
      obtain ⟨m, r⟩ := mr
      change (aevalTower (inlAlgHom R M) (ι R (M × R) (0, 1)))
          ((lift (prodRightToPolynomialGen R M)) (ι R (M × R) (m, r))) = ι R (M × R) (m, r)
      rw [lift_ι_apply, prodRightToPolynomialGen_apply, map_add, map_smul, aevalTower_C,
        aevalTower_X, inlAlgHom_ι]
      exact (ι_prod_eq R M m r).symm))

/-- The isomorphism carries the generator at `(m, r)` to `C (ι m) + r • T`. -/
@[simp]
theorem prodRightEquivPolynomial_ι (m : M) (r : R) :
    prodRightEquivPolynomial R M (ι R (M × R) (m, r)) = C (ι R M m) + r • X :=
  lift_ι_apply _ _

/-- The inverse isomorphism carries the variable `T` to the generator at `(0, 1)`. -/
@[simp]
theorem prodRightEquivPolynomial_symm_X :
    (prodRightEquivPolynomial R M).symm X = ι R (M × R) (0, 1) :=
  aevalTower_X _ _

/-- The inverse isomorphism carries the constant `C a` to the image of `a` along the first
summand. -/
@[simp]
theorem prodRightEquivPolynomial_symm_C (a : SymmetricAlgebra R M) :
    (prodRightEquivPolynomial R M).symm (C a) = inlAlgHom R M a :=
  aevalTower_C _ _ _

/-- The isomorphism carries the image of the first summand to the constants. -/
theorem prodRightEquivPolynomial_inlAlgHom (a : SymmetricAlgebra R M) :
    prodRightEquivPolynomial R M (inlAlgHom R M a) = C a := by
  rw [← prodRightEquivPolynomial_symm_C R M a, AlgEquiv.apply_symm_apply]

/-- The isomorphism carries the generator at `(0, 1)` to the variable. -/
theorem prodRightEquivPolynomial_ι_zero_one :
    prodRightEquivPolynomial R M (ι R (M × R) (0, 1)) = X := by
  rw [← prodRightEquivPolynomial_symm_X R M, AlgEquiv.apply_symm_apply]

end SymmetricAlgebra

end
