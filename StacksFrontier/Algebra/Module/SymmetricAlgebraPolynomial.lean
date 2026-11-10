module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The symmetric algebra of a module with a free rank-one summand split off

For a commutative ring `R` and an `R`-module `M`,

  `Sym(M × R) ≅ Sym(M)[X]`,

the polynomial variable corresponding to the summand `R`.

## Main definitions

* `Stacks.SymmetricAlgebraProd.inlAlgHom`: the inclusion `Sym(M) ⟶ Sym(M × R)` along `m ↦ (m, 0)`.
* `Stacks.SymmetricAlgebraProd.toPolynomialAlgHom` and
  `Stacks.SymmetricAlgebraProd.ofPolynomialAlgHom`: the two algebra maps.
* `Stacks.SymmetricAlgebraProd.prodSelfEquivPolynomial`: the isomorphism.

## Main results

* `Stacks.SymmetricAlgebraProd.isSymmetricAlgebra_toPolynomialLinearMap`: the map
  `(m, r) ↦ C (ι m) + r • X` exhibits `Sym(M)[X]` as the symmetric algebra of `M × R`, which is
  the form in which the universal property is usually consumed.

## Implementation notes

Both directions come from universal properties, so no computation with monomials is needed. The
map out of `Sym(M × R)` is `SymmetricAlgebra.lift` of `(m, r) ↦ C (ι m) + r • X`; the map into it
is `Polynomial.aevalTower` of the inclusion `Sym(M) ⟶ Sym(M × R)` evaluated at the image of
`(0, 1)`. That the composites are the identity is checked by `SymmetricAlgebra.algHom_ext` on one
side and `Polynomial.algHom_ext'` on the other, so on `ι (m, r)` for the first and on `C a` and
`X` for the second.

*Why this statement.* It is the algebraic content of `Sym(M) = Sym(K)[s]` for a module `M` with a
surjection `q : M ⟶ R` onto the free rank-one module and `K = ker q`, once a splitting of `q` has
identified `M` with `K × R`. That fact is what
`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/SectionOfQuotient.lean` records as missing from
the repository, and what the conormal clause of [Stacks, Tag 0B3V] — that the conormal sheaf of
the section attached to an invertible quotient `q` is `ker(q) ⊗ ℒ^{⊗ -1}` — needs locally.

The identification of `M` with `K × R` is deliberately *not* part of this statement. Over a ring
the splitting exists exactly when `q` is a split epimorphism, which is a hypothesis on `q`, not a
theorem; and on a scheme it holds only locally, so a global statement phrased through `ker q`
would be false. Supplying the splitting is the caller's job, and here `M × R` is taken as given.

This is a statement about modules over a ring. It mentions no sheaf of modules and so no sheaf of
rings, which is why it can be stated at all while the migration away from
`CategoryTheory.Sheaf.toRingCat` is in progress: a consumer on a scheme applies it to the modules
of sections over an open, whatever spelling of the structure sheaf of rings that consumer is
written in.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
-/

@[expose] public noncomputable section

open Polynomial

namespace Stacks.SymmetricAlgebraProd

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

/-- The inclusion `Sym(M) ⟶ Sym(M × R)` induced by the linear map `m ↦ (m, 0)`. -/
def inlAlgHom : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R (M × R) :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι R (M × R)).comp (LinearMap.inl R M R))

/-- `inlAlgHom` sends `ι m` to `ι (m, 0)`. -/
@[simp]
theorem inlAlgHom_ι (m : M) :
    inlAlgHom R M (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι R (M × R) (m, 0) :=
  SymmetricAlgebra.lift_ι_apply _ m

/-- The linear map `(m, r) ↦ C (ι m) + r • X` from `M × R` to `Sym(M)[X]`. -/
def toPolynomialLinearMap : (M × R) →ₗ[R] Polynomial (SymmetricAlgebra R M) :=
  LinearMap.coprod
    ((Polynomial.CAlgHom (R := R) (A := SymmetricAlgebra R M)).toLinearMap.comp
      (SymmetricAlgebra.ι R M))
    (LinearMap.toSpanSingleton R (Polynomial (SymmetricAlgebra R M)) Polynomial.X)

/-- `toPolynomialLinearMap` sends `(m, r)` to `C (ι m) + r • X`. -/
@[simp]
theorem toPolynomialLinearMap_apply (m : M) (r : R) :
    toPolynomialLinearMap R M (m, r) =
      Polynomial.C (SymmetricAlgebra.ι R M m) + r • Polynomial.X := rfl

/-- The algebra map `Sym(M × R) ⟶ Sym(M)[X]` lifting `(m, r) ↦ C (ι m) + r • X`. -/
def toPolynomialAlgHom :
    SymmetricAlgebra R (M × R) →ₐ[R] Polynomial (SymmetricAlgebra R M) :=
  SymmetricAlgebra.lift (toPolynomialLinearMap R M)

/-- `toPolynomialAlgHom` sends `ι (m, r)` to `C (ι m) + r • X`. -/
@[simp]
theorem toPolynomialAlgHom_ι (m : M) (r : R) :
    toPolynomialAlgHom R M (SymmetricAlgebra.ι R (M × R) (m, r)) =
      Polynomial.C (SymmetricAlgebra.ι R M m) + r • Polynomial.X :=
  SymmetricAlgebra.lift_ι_apply _ (m, r)

/-- The algebra map `Sym(M)[X] ⟶ Sym(M × R)` which is `inlAlgHom` on coefficients and sends `X`
to the image of `(0, 1)`. -/
def ofPolynomialAlgHom :
    Polynomial (SymmetricAlgebra R M) →ₐ[R] SymmetricAlgebra R (M × R) :=
  Polynomial.aevalTower (inlAlgHom R M) (SymmetricAlgebra.ι R (M × R) (0, 1))

/-- `ofPolynomialAlgHom` sends `X` to `ι (0, 1)`. -/
@[simp]
theorem ofPolynomialAlgHom_X :
    ofPolynomialAlgHom R M Polynomial.X = SymmetricAlgebra.ι R (M × R) (0, 1) :=
  Polynomial.aevalTower_X _ _

/-- `ofPolynomialAlgHom` sends the constant `C a` to `inlAlgHom a`. -/
@[simp]
theorem ofPolynomialAlgHom_C (a : SymmetricAlgebra R M) :
    ofPolynomialAlgHom R M (Polynomial.C a) = inlAlgHom R M a :=
  Polynomial.aevalTower_C _ _ a

/-- `ofPolynomialAlgHom` is a left inverse of `toPolynomialAlgHom`. -/
theorem ofPolynomialAlgHom_comp_toPolynomialAlgHom :
    (ofPolynomialAlgHom R M).comp (toPolynomialAlgHom R M) = AlgHom.id R _ := by
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
  obtain ⟨m, r⟩ := x
  have key : ((m, 0) + r • ((0 : M), (1 : R)) : M × R) = (m, r) := by
    simp
  change ofPolynomialAlgHom R M (toPolynomialAlgHom R M
      (SymmetricAlgebra.ι R (M × R) (m, r))) = SymmetricAlgebra.ι R (M × R) (m, r)
  rw [toPolynomialAlgHom_ι, map_add, map_smul, ofPolynomialAlgHom_C, ofPolynomialAlgHom_X,
    inlAlgHom_ι, ← map_smul, ← map_add, key]

/-- `toPolynomialAlgHom` is a left inverse of `ofPolynomialAlgHom`. -/
theorem toPolynomialAlgHom_comp_ofPolynomialAlgHom :
    (toPolynomialAlgHom R M).comp (ofPolynomialAlgHom R M) = AlgHom.id R _ := by
  refine Polynomial.algHom_ext' (SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => ?_)) ?_
  · simp
  · simp

/-- **`Sym(M × R) ≅ Sym(M)[X]`.** -/
def prodSelfEquivPolynomial :
    SymmetricAlgebra R (M × R) ≃ₐ[R] Polynomial (SymmetricAlgebra R M) :=
  AlgEquiv.ofAlgHom (toPolynomialAlgHom R M) (ofPolynomialAlgHom R M)
    (toPolynomialAlgHom_comp_ofPolynomialAlgHom R M)
    (ofPolynomialAlgHom_comp_toPolynomialAlgHom R M)

/-- **`Sym(M)[X]` is the symmetric algebra of `M × R`**, by way of `(m, r) ↦ C (ι m) + r • X`.
This is the form the universal property is consumed in. -/
@[ega "II 1.7.1" "case F = A"]
theorem isSymmetricAlgebra_toPolynomialLinearMap :
    IsSymmetricAlgebra (toPolynomialLinearMap R M) :=
  (prodSelfEquivPolynomial R M).bijective

end Stacks.SymmetricAlgebraProd

end
