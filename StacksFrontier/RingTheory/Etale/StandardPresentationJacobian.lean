module

public import StacksFrontier.RingTheory.Etale.DirectedColimitPresentation

/-!
# The standard presentation of an étale algebra, with its Jacobian determinant

Stacks 00U9 says that an étale algebra `S` over `R` is a quotient
`R[x_1, …, x_n]/(g_1, …, g_n)` by as many equations as variables **whose Jacobian determinant
`Δ = det(∂g_λ/∂x_μ)` is invertible in the quotient**.  Mathlib proves the tag in the form
`Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`, whose witness is an
`Algebra.SubmersivePresentation` of relative dimension `0`; the invertible Jacobian is the
field `Algebra.SubmersivePresentation.jacobian_isUnit` of that witness.

`Algebra.Etale.exists_algEquiv_quotient_span_range` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/StandardPresentationExists.lean`
already extracts the presentation from that witness, but it discards the Jacobian: its
conclusion is only the existence of an isomorphism
`S ≃ₐ[R] R[x_1, …, x_n]/(g_1, …, g_n)`.  This file keeps the Jacobian, in the shape
`MvPolynomial.detJacobian` in which
`Algebra.etale_mvPolynomialQuotient_of_isUnit_det` and
`MvPolynomial.exists_ge_isUnit_detJacobian_of_directed` consume it.

## Main results

* `Algebra.Etale.exists_isUnit_detJacobian_algEquiv_quotient_span_range`: an étale algebra is a
  quotient `R[x_1, …, x_n]/(g_1, …, g_n)` by a family indexed by the variables whose Jacobian
  determinant is invertible in the quotient.

## Implementation notes

*Why the variables are reindexed through the relation map.*  A
`Algebra.PreSubmersivePresentation R S ι σ` has variables `ι`, relations `σ` and an injective
`map : σ → ι`, and its Jacobian is the determinant of the **square** matrix
`(∂(relation j)/∂x_{map i})_{i, j : σ}`, a submatrix of the full matrix of partial derivatives.
`MvPolynomial.detJacobian`, by contrast, takes a family indexed by the variables themselves and
differentiates with respect to all of them.  The two agree exactly when `map` is the identity.
At relative dimension `0` the two index types have the same cardinality, so the injective `map`
is bijective, and reindexing the variables along `map` itself — rather than along an arbitrary
bijection `Fin n ≃ ι` — makes `map` the identity on the nose.  That is why the variable equivalence
below is `fσ.trans β` with `β` the equivalence `Equiv.ofBijective` builds from `map`: no
permutation sign is then left to account for.

`Algebra.SubmersivePresentation.reindex` carries the invertibility of the Jacobian along, by
`Algebra.PreSubmersivePresentation.jacobian_reindex`, so nothing about the Jacobian has to be
recomputed; what is computed here is only the identification of the reindexed Jacobian matrix
with the matrix of partial derivatives that `MvPolynomial.detJacobian` takes the determinant of.

## References

* [Stacks Project, Tag 00U9](https://stacks.math.columbia.edu/tag/00U9)
-/

@[expose] public section

universe u

open MvPolynomial

namespace Algebra.Etale

/-- **An étale algebra has a standard presentation with invertible Jacobian determinant.**  An
étale `R`-algebra `S` is isomorphic to `R[x_1, …, x_n]/(g_1, …, g_n)` for a family `g` of
polynomials indexed by the variables whose Jacobian determinant
`MvPolynomial.detJacobian g = det(∂g_μ/∂x_λ)` is invertible in the quotient.

This is Stacks 00U9 in the form its consumers in this development want: it is
`Algebra.Etale.exists_algEquiv_quotient_span_range` with the Jacobian determinant retained, and
it is the converse of `Algebra.etale_mvPolynomialQuotient_of_isUnit_det`. -/
theorem exists_isUnit_detJacobian_algEquiv_quotient_span_range (R S : Type u) [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.Etale R S] :
    ∃ (n : ℕ) (g : Fin n → MvPolynomial (Fin n) R),
      IsUnit (Ideal.Quotient.mk (Ideal.span (Set.range g)) (detJacobian g)) ∧
      Nonempty (S ≃ₐ[R] MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range g)) := by
  classical
  obtain ⟨ι, σ, _, _, Q, hQ⟩ :=
    (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero (R := R) (S := S)).mp
      inferInstance |>.out
  have hle := Q.toPreSubmersivePresentation.card_relations_le_card_vars_of_isFinite
  have hcard : Nat.card σ = Nat.card ι := by
    have : Nat.card ι - Nat.card σ = 0 := hQ
    omega
  set n := Nat.card σ
  let fσ : Fin n ≃ σ := (Finite.equivFin σ).symm
  let β : σ ≃ ι :=
    Equiv.ofBijective Q.map ((Nat.bijective_iff_injective_and_card Q.map).2 ⟨Q.map_inj, hcard⟩)
  let Q' : SubmersivePresentation R S (Fin n) (Fin n) := Q.reindex (fσ.trans β) fσ
  have hmap : ∀ i : Fin n, Q'.map i = i := by
    intro i
    show fσ.symm (β.symm (β (fσ i))) = i
    simp
  have hdet : Q'.jacobiMatrix.det = detJacobian Q'.relation := by
    rw [detJacobian]
    congr 1
    ext a b
    rw [PreSubmersivePresentation.jacobiMatrix_apply, hmap]
    rfl
  let δ := (Ideal.quotientEquivAlgOfEq R Q'.toPresentation.span_range_relation_eq_ker).trans
      (Q'.toPresentation.quotientEquiv.restrictScalars R)
  have hδ : ∀ p : Q'.Ring,
      δ (Ideal.Quotient.mk (Ideal.span (Set.range Q'.relation)) p) =
        algebraMap Q'.Ring S p := by
    intro p
    show Q'.toPresentation.quotientEquiv
        (Ideal.quotientEquivAlgOfEq R Q'.toPresentation.span_range_relation_eq_ker
          (Ideal.Quotient.mk _ p)) = _
    rw [Ideal.quotientEquivAlgOfEq_mk]
    exact Q'.toPresentation.quotientEquiv_mk p
  refine ⟨n, Q'.relation, ?_, ⟨δ.symm⟩⟩
  have hu := Q'.jacobian_isUnit
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, hdet, ← hδ] at hu
  simpa only [AlgEquiv.symm_apply_apply] using hu.map δ.symm

end Algebra.Etale

/-! ### Pushing a standard presentation along a ring map -/

namespace MvPolynomial

/-- **Invertibility of the Jacobian determinant is preserved by a change of coefficients.**  If
the Jacobian determinant of `g : κ → R[x_k : k ∈ κ]` is invertible in `R[x] ⧸ (g)`, then the
Jacobian determinant of the family obtained by pushing the coefficients along `ψ : R →+* R'` is
invertible in `R'[x] ⧸ (ψ g)`.

Together with `Algebra.etale_mvPolynomialQuotient_of_isUnit_det` this is the standard-presentation
form of "an étale algebra stays étale after base change of the coefficients", and it is how a
presentation found at one stage of an inverse system is carried to a later stage. -/
theorem isUnit_detJacobian_map {R : Type*} [CommRing R] {R' : Type*} [CommRing R']
    (ψ : R →+* R') {κ : Type*} [Fintype κ] [DecidableEq κ] (g : κ → MvPolynomial κ R)
    (hg : IsUnit (Ideal.Quotient.mk (Ideal.span (Set.range g)) (detJacobian g))) :
    IsUnit (Ideal.Quotient.mk (Ideal.span (Set.range fun k ↦ map ψ (g k)))
      (detJacobian fun k ↦ map ψ (g k))) := by
  have hle : Ideal.span (Set.range g) ≤
      (Ideal.span (Set.range fun k ↦ map ψ (g k))).comap (MvPolynomial.map ψ) := by
    rw [Ideal.span_le]
    rintro x ⟨k, rfl⟩
    exact Ideal.subset_span ⟨k, rfl⟩
  have hu := hg.map (Ideal.quotientMap
    (Ideal.span (Set.range fun k ↦ map ψ (g k))) (MvPolynomial.map ψ) hle)
  rwa [Ideal.quotientMap_mk, map_detJacobian] at hu

end MvPolynomial

end
