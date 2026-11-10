module

public import StacksFrontier.RingTheory.Etale.DirectedColimitPresentation

/-!
# An étale algebra has a square presentation with invertible Jacobian determinant

An étale algebra `A` over a commutative ring `R` is standard smooth of relative dimension zero,
which is the substantial direction of Stacks 00U9, available as Mathlib's
`Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`. This file converts that statement
into the concrete shape the commutative-algebra core of Stacks 07SQ consumes: there are a
natural number `n` and polynomials `g₁, …, gₙ` in `n` variables over `R` such that

`A ≅ R[x₁, …, xₙ] ⧸ (g₁, …, gₙ)`

and the Jacobian determinant `det (∂g_b/∂x_a)` is invertible in that quotient.

## Main results

* `Algebra.exists_square_presentation_isUnit_detJacobian_of_etale`: the conversion.

## Implementation notes

*Why a conversion is needed at all.* Mathlib states relative dimension zero as the existence of
an `Algebra.SubmersivePresentation` whose variables `ι` and relations `σ` are arbitrary finite
types, related by an injective `Algebra.PreSubmersivePresentation.map : σ → ι` which selects the
coordinates the Jacobian is taken in. The core of Stacks 07SQ, in
`StacksFrontier/RingTheory/Etale/DirectedColimitPresentation.lean`, instead indexes relations *by
the variables*, so that the Jacobian is `MvPolynomial.detJacobian`, the determinant of the full
square matrix of partial derivatives. The two agree once the presentation is reindexed so that
`map` becomes the identity, and that reindexing is what this file performs.

*Why `map` may be made the identity.* Relative dimension zero says
`Nat.card ι - Nat.card σ = 0`, and `map` injective says `Nat.card σ ≤ Nat.card ι`; together the
two cardinalities agree, so the injection `map` is a bijection. Reindexing the variables along
`Fin n ≃ σ ≃ ι`, where the second equivalence is `map` itself, and the relations along the same
`Fin n ≃ σ`, turns `map` into the identity of `Fin n`, by
`Algebra.PreSubmersivePresentation.reindex` computing it as `e.symm ∘ map ∘ f`. With `map` the
identity, `Algebra.PreSubmersivePresentation.jacobiMatrix_apply` reads
`jacobiMatrix a b = pderiv a (relation b)`, which is `MvPolynomial.detJacobian`'s matrix on the
nose.

*Transporting invertibility.* The presentation's Jacobian is a unit of `A`, namely the image of
the determinant under `algebraMap R[x] A`, whereas what is wanted is invertibility of its class
in `R[x] ⧸ (g)`. The two are identified by the presentation's own
`Algebra.Presentation.quotientEquiv`, composed with the rewriting of `(g)` as the kernel given
by `Algebra.Presentation.span_range_relation_eq_ker`; under that isomorphism the class of a
polynomial corresponds to its image in `A`, so invertibility passes across.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 00U9](https://stacks.math.columbia.edu/tag/00U9)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
-/

@[expose] public section

universe u v

open MvPolynomial

namespace Algebra

/-- **An étale algebra has a square presentation whose Jacobian determinant is invertible.**
If `A` is an étale `R`-algebra then there are `n` polynomials `g₁, …, gₙ` in `n` variables over
`R` presenting `A`, that is `A ≅ R[x₁, …, xₙ] ⧸ (g₁, …, gₙ)`, whose Jacobian determinant
`det (∂g_b/∂x_a)` is invertible in the quotient.

This is the substantial direction of Stacks 00U9, Mathlib's
`Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`, put in the shape that the
commutative-algebra core of Stacks 07SQ consumes: it is the exact converse of
`Algebra.etale_mvPolynomialQuotient_of_isUnit_det`, and it supplies the hypothesis `hg` of
`MvPolynomial.exists_ge_etale_quotient_of_directed`. -/
theorem exists_square_presentation_isUnit_detJacobian_of_etale (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A] [Algebra.Etale R A] :
    ∃ (n : ℕ) (g : Fin n → MvPolynomial (Fin n) R),
      IsUnit (Ideal.Quotient.mk (Ideal.span (Set.range g)) (detJacobian g)) ∧
        Nonempty (A ≃ₐ[R] MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range g)) := by
  classical
  obtain ⟨ι, σ, _, _, P, hP⟩ :=
    (Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp inferInstance :
      IsStandardSmoothOfRelativeDimension 0 R A).out
  have : Fintype σ := Fintype.ofFinite σ
  have : Fintype ι := Fintype.ofFinite ι
  -- The variables and the relations are equinumerous, so `map` is a bijection.
  have hle : Nat.card σ ≤ Nat.card ι :=
    P.toPreSubmersivePresentation.card_relations_le_card_vars_of_isFinite
  have hcard : Nat.card σ = Nat.card ι := le_antisymm hle (Nat.le_of_sub_eq_zero hP)
  have hbij : Function.Bijective P.map :=
    (Nat.bijective_iff_injective_and_card P.map).mpr ⟨P.map_inj, hcard⟩
  -- Reindex so that `map` becomes the identity of `Fin n`.
  set n : ℕ := Fintype.card σ with hn
  set fe : Fin n ≃ σ := (Fintype.equivFin σ).symm with hfe
  set me : σ ≃ ι := Equiv.ofBijective P.map hbij with hme
  set Q : SubmersivePresentation R A (Fin n) (Fin n) := P.reindex (fe.trans me) fe with hQ
  have hmap : ∀ k : Fin n, Q.map k = k := by
    intro k
    change (fe.trans me).symm (P.map (fe k)) = k
    have hval : P.map (fe k) = me (fe k) := rfl
    rw [hval, Equiv.symm_trans_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  set g : Fin n → MvPolynomial (Fin n) R := Q.relation with hg
  have hspan : Ideal.span (Set.range g) = Q.ker := Q.span_range_relation_eq_ker
  -- With `map` the identity the presentation's Jacobian matrix is the full square matrix of
  -- partial derivatives, so its determinant is `detJacobian g`.
  have hjac : Q.jacobiMatrix = Matrix.of fun a b => pderiv a (g b) := by
    ext a b
    rw [PreSubmersivePresentation.jacobiMatrix_apply, hmap]
    rfl
  have hdet : Q.jacobiMatrix.det = detJacobian g := by rw [hjac]; rfl
  have hunit : IsUnit (algebraMap Q.Ring A (detJacobian g)) := by
    have h := Q.jacobian_isUnit
    rwa [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, hdet] at h
  -- The presentation identifies the quotient by `(g)` with `A`.
  set E : (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range g)) ≃ₐ[R] A :=
    (Ideal.quotientEquivAlgOfEq R hspan).trans (Q.quotientEquiv.restrictScalars R) with hEdef
  have hE : ∀ p : MvPolynomial (Fin n) R,
      E (Ideal.Quotient.mk (Ideal.span (Set.range g)) p) = algebraMap Q.Ring A p := by
    intro p
    simp [hEdef, Ideal.quotientEquivAlgOfEq_mk]
  refine ⟨n, g, ?_, ⟨E.symm⟩⟩
  have h := hunit.map E.symm
  rwa [← hE, E.symm_apply_apply] at h

end Algebra

end
