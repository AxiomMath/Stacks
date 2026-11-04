module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.RepresentableEqualizer

/-!
# Standard presentations of étale algebras

An étale algebra `S` over `R` is a quotient `R[x₁, …, x_n]/(P₁, …, P_n)` with as many equations as
variables (Stacks 00U9, Mathlib's `Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`),
and such a quotient stays étale after any base change `R → R'`, presented by the same equations
with their coefficients pushed to `R'`.  For an étale morphism `V ⟶ Y` of affine schemes this
gives the datum `Stacks.EtaleCohomology.StandardPresentationOver` of step (2) of the proof of
Stacks 04I6, which `Stacks.EtaleCohomology.homOverEquivSolutions` takes as a hypothesis.

## Main results

* `Algebra.Etale.exists_algEquiv_quotient_span_range`: an étale algebra is a quotient
  `R[x₁, …, x_n]/(P₁, …, P_n)`.
* `Algebra.Etale.quotient_span_range_map`: such a quotient stays étale after a base change of the
  coefficients.
* `Stacks.EtaleCohomology.exists_standardPresentationOver`: an étale morphism of affine schemes
  has a standard presentation, with étale presented ring.

## References

* [Stacks Project, Tag 00U9](https://stacks.math.columbia.edu/tag/00U9)
* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TensorProduct

universe u

namespace Algebra.Etale

/-- **An étale algebra is presented by as many equations as variables.** An étale `R`-algebra
`S` is isomorphic to `R[x₁, …, x_n]/(P₁, …, P_n)` for some `n` and polynomials `Pⱼ`: a submersive
presentation of relative dimension `0` (Stacks 00U9) has as many relations as variables. -/
theorem exists_algEquiv_quotient_span_range (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.Etale R S] :
    ∃ (n : ℕ) (P : Fin n → MvPolynomial (Fin n) R),
      Nonempty (S ≃ₐ[R] MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range P)) := by
  obtain ⟨ι, σ, _, _, Q, hQ⟩ :=
    (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero (R := R) (S := S)).mp
      inferInstance |>.out
  have hle := Q.toPreSubmersivePresentation.card_relations_le_card_vars_of_isFinite
  have hcard : Nat.card σ = Nat.card ι := by
    have : Nat.card ι - Nat.card σ = 0 := hQ
    omega
  let Q' := Q.toPresentation.reindex ((finCongr hcard).trans (Finite.equivFin ι).symm)
    (Finite.equivFin σ).symm
  exact ⟨_, Q'.relation, ⟨(Q'.quotientEquiv.restrictScalars R).symm.trans
    (Ideal.quotientEquivAlgOfEq R Q'.span_range_relation_eq_ker.symm)⟩⟩

/-- **A presented étale algebra stays étale after base change of the coefficients.** If
`A[x₁, …, x_n]/(P₁, …, P_n)` is étale over `A`, then for every ring map `κ : A → R` the quotient
`R[x₁, …, x_n]/(κ P₁, …, κ P_n)` is étale over `R`: it is the base change, presented by the base
change of the naive presentation. -/
theorem quotient_span_range_map {A R : Type u} [CommRing A] [CommRing R] (κ : A →+* R) {n : ℕ}
    (P : Fin n → MvPolynomial (Fin n) A)
    [Algebra.Etale A (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range P))] :
    Algebra.Etale R (MvPolynomial (Fin n) R ⧸
      Ideal.span (Set.range fun j => MvPolynomial.map κ (P j))) := by
  let : Algebra A R := κ.toAlgebra
  set Q := MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range P)
  let N := (Algebra.Presentation.naive (v := P)).baseChange R
  have hrel : N.relation = fun j => MvPolynomial.map κ (P j) := rfl
  have e : (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range fun j => MvPolynomial.map κ (P j)))
      ≃ₐ[R] R ⊗[A] Q :=
    (Ideal.quotientEquivAlgOfEq R (by rw [← hrel, N.span_range_relation_eq_ker])).trans
      (N.quotientEquiv.restrictScalars R)
  exact Algebra.Etale.of_equiv e.symm

end Algebra.Etale

namespace Stacks.EtaleCohomology

/-- **An étale morphism of affine schemes has a standard presentation.** For `pV : V ⟶ Y` étale
with `V` and `Y` affine, `Γ(V, ⊤)` is, compatibly with the structure maps from `Γ(Y, ⊤)`, a
quotient `Γ(Y, ⊤)[x₁, …, x_n]/(P₁, …, P_n)` with as many equations as variables, and that
quotient is étale over `Γ(Y, ⊤)`. -/
theorem exists_standardPresentationOver {Y V : Scheme.{u}} [IsAffine Y] [IsAffine V]
    (pV : V ⟶ Y) [Etale pV] :
    ∃ (n : ℕ) (P : Fin n → MvPolynomial (Fin n) Γ(Y, ⊤)),
      Nonempty (StandardPresentationOver V pV P) ∧
      Algebra.Etale Γ(Y, ⊤) (MvPolynomial (Fin n) Γ(Y, ⊤) ⧸ Ideal.span (Set.range P)) := by
  let : Algebra Γ(Y, ⊤) Γ(V, ⊤) := pV.appTop.hom.toAlgebra
  have : Algebra.Etale Γ(Y, ⊤) Γ(V, ⊤) :=
    HasRingHomProperty.appTop (P := @AlgebraicGeometry.Etale) _ inferInstance
  obtain ⟨n, P, ⟨e⟩⟩ := Algebra.Etale.exists_algEquiv_quotient_span_range Γ(Y, ⊤) Γ(V, ⊤)
  refine ⟨n, P, ⟨⟨e.toRingEquiv.toCommRingCatIso, ?_⟩⟩, Algebra.Etale.of_equiv e⟩
  ext r
  exact e.commutes r

end Stacks.EtaleCohomology
