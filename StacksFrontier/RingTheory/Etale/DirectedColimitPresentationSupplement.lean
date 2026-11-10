module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import StacksFrontier.RingTheory.Etale.DirectedColimitPresentation
public import StacksFrontier.RingTheory.MvPolynomial.DirectedColimit
public import StacksFrontier.RingTheory.Spectrum.Prime.DirectedColimit

/-!
# Supplement to `DirectedColimitPresentation`

The results of this module extend those of
`StacksFrontier.RingTheory.Etale.DirectedColimitPresentation`.
They use imports, universe variables or `open` declarations that the base module does not
have, and are kept in a module of their own so that its header is unchanged.

## Main results

* `exists_isUnit_detJacobian_of_etale`
* `RingHom.exists_isUnit_detJacobian_of_etale`
-/

@[expose] public section

universe u v w

open MvPolynomial TensorProduct

namespace Algebra

/-- **An étale algebra has a standard-étale presentation.**  If `T` is an étale `R`-algebra then
there are a natural number `n`, a family `g` of `n` polynomials in `n` variables over `R` whose
Jacobian determinant is invertible in `R[x] ⧸ (g)`, and an isomorphism `R[x] ⧸ (g) ≃ₐ[R] T`.

This is the converse of `Algebra.etale_mvPolynomialQuotient_of_isUnit_det`: the direction of
Stacks 00U9 that *produces* a standard-étale presentation, which is how the proof of Stacks 07SQ
presents the étale chart of the limit.

Mathlib's `Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero` supplies a submersive
presentation of relative dimension zero.  Its variables and its relations are indexed by two
different finite types, of equal cardinality because the dimension vanishes, so its injective
`map` from relations to variables is a bijection; reindexing the variables along that bijection
and both index types along `Fin n` turns the presentation into one whose `map` is the identity,
which is the square shape `MvPolynomial.detJacobian` is stated for. -/
theorem exists_isUnit_detJacobian_of_etale {R : Type u} [CommRing R] {T : Type v} [CommRing T]
    [Algebra R T] [Algebra.Etale R T] :
    ∃ (n : ℕ) (g : Fin n → MvPolynomial (Fin n) R),
      IsUnit (Ideal.Quotient.mk (Ideal.span (Set.range g)) (detJacobian g)) ∧
        Nonempty ((MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range g)) ≃ₐ[R] T) := by
  classical
  obtain ⟨ι, σ, hσ, hι, P, hdim⟩ :=
    (Etale.iff_isStandardSmoothOfRelativeDimension_zero (R := R) (S := T)).mp inferInstance |>.out
  have _ : Finite σ := hσ
  have _ : Finite ι := hι
  have hle : Nat.card σ ≤ Nat.card ι := P.card_relations_le_card_vars_of_isFinite
  have hdim' : Nat.card ι - Nat.card σ = 0 := hdim
  have hcard : Nat.card σ = Nat.card ι := le_antisymm hle (by omega)
  have hbij : Function.Bijective P.map :=
    (Nat.bijective_iff_injective_and_card _).2 ⟨P.map_inj, hcard⟩
  set n := Nat.card σ with hn
  let e : σ ≃ ι := Equiv.ofBijective P.map hbij
  let d : Fin n ≃ σ := (Finite.equivFin σ).symm
  let Q : SubmersivePresentation R T (Fin n) (Fin n) := P.reindex (d.trans e) d
  have hQmap : ∀ k, Q.map k = k := by
    intro k
    change (P.toPreSubmersivePresentation.reindex (d.trans e) d).map k = k
    rw [PreSubmersivePresentation.reindex_map]
    have he : ∀ x, e.symm (P.map x) = x := fun x => e.symm_apply_apply x
    simp [he]
  have hdet : Q.jacobiMatrix.det = detJacobian Q.relation := by
    rw [detJacobian]
    congr 1
    ext i j
    rw [PreSubmersivePresentation.jacobiMatrix_apply, hQmap]
    rfl
  have hspan : Ideal.span (Set.range Q.relation) = Q.ker := Q.span_range_relation_eq_ker
  let ε : (Q.Ring ⧸ Ideal.span (Set.range Q.relation)) ≃ₐ[R] T :=
    (Ideal.quotientEquivAlgOfEq R hspan).trans (Q.quotientEquiv.restrictScalars R)
  have hεmk : ∀ p : Q.Ring,
      ε (Ideal.Quotient.mk (Ideal.span (Set.range Q.relation)) p)
        = algebraMap Q.Ring T p := by
    intro p
    change Q.quotientEquiv (Ideal.quotientEquivAlgOfEq R hspan (Ideal.Quotient.mk _ p)) = _
    rw [Ideal.quotientEquivAlgOfEq_mk, Presentation.quotientEquiv_mk]
  refine ⟨n, Q.relation, ?_, ⟨ε⟩⟩
  have hunit : IsUnit (algebraMap Q.Ring T (detJacobian Q.relation)) := by
    have h := Q.jacobian_isUnit
    rwa [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, hdet] at h
  have h1 : IsUnit (ε (Ideal.Quotient.mk (Ideal.span (Set.range Q.relation))
      (detJacobian Q.relation))) := by rw [hεmk]; exact hunit
  simpa using h1.map ε.symm

end Algebra

/-- **A standard-étale presentation of an étale ring map.**  For an étale homomorphism
`ψ : R →+* T` there are a square family `g` of polynomials over `R` with invertible Jacobian
determinant and a ring isomorphism `ε : R[x] ⧸ (g) ≃+* T` carrying the structure homomorphism of
the presentation to `ψ`.

This is `Algebra.exists_isUnit_detJacobian_of_etale` read for a bare ring map, which is the form
the geometric side uses: `ψ` is the restriction of global functions along an étale chart, and the
compatibility clause is what makes the classes of the variables a family of functions on the
chart killing the `g`. -/
theorem RingHom.exists_isUnit_detJacobian_of_etale {R T : Type u} [CommRing R] [CommRing T]
    {ψ : R →+* T} (hψ : ψ.Etale) :
    ∃ (n : ℕ) (g : Fin n → MvPolynomial (Fin n) R)
      (ε : (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range g)) ≃+* T),
      IsUnit (Ideal.Quotient.mk (Ideal.span (Set.range g)) (detJacobian g)) ∧
        ε.toRingHom.comp
            ((Ideal.Quotient.mk (Ideal.span (Set.range g))).comp MvPolynomial.C) = ψ := by
  let := ψ.toAlgebra
  have : Algebra.Etale R T := hψ
  obtain ⟨n, g, hunit, ⟨ε⟩⟩ := Algebra.exists_isUnit_detJacobian_of_etale (R := R) (T := T)
  refine ⟨n, g, ε.toRingEquiv, hunit, RingHom.ext fun a => ?_⟩
  have h : ε (algebraMap R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range g)) a)
      = algebraMap R T a := ε.commutes a
  exact h

end
