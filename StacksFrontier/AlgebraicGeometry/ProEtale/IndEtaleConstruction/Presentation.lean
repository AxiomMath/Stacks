module

public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

/-!
# Square presentations of étale algebras

An étale algebra is standard smooth of relative dimension zero, hence admits a presentation by
equally many variables and relations whose Jacobian determinant is invertible. Conversely such a
presentation always presents an étale algebra.

Packaging this data together with faithful flatness of the structure map gives the indexing set
`S(A)` of the construction of a faithfully flat ind-étale algebra splitting all faithfully flat
étale covers: `StandardEtalePresentation A` is the type of faithfully flat square presentations
over `A`, and every faithfully flat étale `A`-algebra is isomorphic to the algebra presented by
one of its elements.

## Main definitions

* `AlgebraicGeometry.ProEtale.jacobianDeterminant`
* `AlgebraicGeometry.ProEtale.presentedAlgebra`
* `AlgebraicGeometry.ProEtale.StandardEtalePresentation`

## Main results

* `AlgebraicGeometry.ProEtale.presentedAlgebra_etale`
* `AlgebraicGeometry.ProEtale.exists_fin_algEquiv_quotientSpanRange_of_etale`
* `AlgebraicGeometry.ProEtale.exists_standardEtalePresentation_of_etale_faithfullyFlat`

## Implementation notes

`StandardEtalePresentation A` is not Mathlib's `StandardEtalePresentation R S`, which presents an
algebra as `(R[x]/f)_g`. Here the presentation is by a square system of polynomial relations with
invertible Jacobian, that is, a submersive presentation of relative dimension zero, and the
presented algebra is part of the data rather than a parameter.
-/

open MvPolynomial

@[expose] public section

namespace AlgebraicGeometry.ProEtale

universe u

/-- The determinant of the square Jacobian matrix of a list of polynomials. -/
noncomputable def jacobianDeterminant {A : Type u} [CommRing A] {n : ℕ}
    (f : Fin n → MvPolynomial (Fin n) A) : MvPolynomial (Fin n) A :=
  Matrix.det (fun i j ↦ pderiv i (f j))

/-- The algebra presented by a square list of polynomial relations. -/
abbrev presentedAlgebra (A : Type u) [CommRing A] {n : ℕ}
    (f : Fin n → MvPolynomial (Fin n) A) :=
  MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)

/-- A faithfully flat standard smooth presentation of relative dimension zero over `A`: a square
system of polynomial relations whose Jacobian determinant is invertible in the quotient and whose
quotient is faithfully flat over `A`. -/
structure StandardEtalePresentation (A : Type u) [CommRing A] where
  /-- The number of variables, which is also the number of relations. -/
  variableCount : ℕ
  /-- The defining relations. -/
  relations : Fin variableCount → MvPolynomial (Fin variableCount) A
  /-- The Jacobian determinant is invertible in the presented algebra. -/
  jacobian_isUnit : IsUnit
    (Ideal.Quotient.mk (Ideal.span (Set.range relations))
      (jacobianDeterminant relations))
  /-- The presented algebra is faithfully flat over `A`. -/
  faithfullyFlat :
    (algebraMap A (presentedAlgebra A relations)).FaithfullyFlat

/-- For a square pre-submersive presentation with identity indexing map, the Jacobian matrix is
the matrix of partial derivatives of the relations. -/
private lemma jacobiMatrix_eq_pderiv {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {n : ℕ} (Q : Algebra.PreSubmersivePresentation A B (Fin n) (Fin n))
    (h : ∀ i, Q.map i = i) : Q.jacobiMatrix = fun i j ↦ pderiv i (Q.relation j) := by
  ext i j
  rw [Q.jacobiMatrix_apply, h i]

/-- The algebra presented by a square system of relations with invertible Jacobian determinant is
étale: the system is a submersive presentation of relative dimension zero. -/
lemma presentedAlgebra_etale {A : Type u} [CommRing A]
    (p : StandardEtalePresentation A) :
    Algebra.Etale A (presentedAlgebra A p.relations) := by
  let n := p.variableCount
  let I : Ideal (MvPolynomial (Fin n) A) := Ideal.span (Set.range p.relations)
  let S := MvPolynomial (Fin n) A ⧸ I
  let val : Fin n → S := fun i ↦ Ideal.Quotient.mk I (MvPolynomial.X i)
  have hEval : MvPolynomial.aeval val = Ideal.Quotient.mkₐ A I := by
    ext i
    rw [MvPolynomial.aeval_X, Ideal.Quotient.mkₐ_eq_mk]
  let G : Algebra.Generators A S (Fin n) :=
    { val := val
      σ' := fun s ↦ Classical.choose (Ideal.Quotient.mk_surjective s)
      aeval_val_σ' := fun s ↦ by
        rw [hEval]
        exact Classical.choose_spec (Ideal.Quotient.mk_surjective s) }
  let P : Algebra.Presentation A S (Fin n) (Fin n) :=
    { toGenerators := G
      relation := p.relations
      span_range_relation_eq_ker := by
        rw [Algebra.Generators.ker_eq_ker_aeval_val, hEval]
        change Ideal.span (Set.range p.relations) = RingHom.ker (Ideal.Quotient.mk I)
        rw [Ideal.mk_ker] }
  let Q₀ : Algebra.PreSubmersivePresentation A S (Fin n) (Fin n) :=
    { toPresentation := P
      map := id
      map_inj := Function.injective_id }
  let Q : Algebra.SubmersivePresentation A S (Fin n) (Fin n) :=
    { toPreSubmersivePresentation := Q₀
      jacobian_isUnit := by
        have hdet : Q₀.jacobian =
            Ideal.Quotient.mk I (jacobianDeterminant p.relations) := by
          rw [Q₀.jacobian_eq_jacobiMatrix_det]
          rw [jacobiMatrix_eq_pderiv Q₀ fun _ ↦ rfl]
          change MvPolynomial.aeval (Q₀.val)
            (Matrix.det fun i j ↦ MvPolynomial.pderiv i (p.relations j)) = _
          rw [hEval]
          rfl
        rw [hdet]
        exact p.jacobian_isUnit }
  exact Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mpr
    (Q.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension, n]))

/-- An étale algebra admits a submersive presentation whose relations are indexed by the same
type as its variables, with the indexing map the identity. -/
private lemma exists_square_submersive_presentation {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B] (h : Algebra.Etale A B) :
    ∃ n : ℕ, ∃ Q : Algebra.SubmersivePresentation A B (Fin n) (Fin n),
      ∀ i, Q.map i = i := by
  obtain ⟨ι, σ, hσ, hι, P, hP⟩ :=
    (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp h).out
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : Fintype σ := Fintype.ofFinite σ
  have hcard : Fintype.card σ = Fintype.card ι := by
    dsimp [Algebra.Presentation.dimension] at hP
    simpa only [Nat.card_eq_fintype_card] using
      Nat.le_antisymm P.card_relations_le_card_vars_of_isFinite (Nat.sub_eq_zero_iff_le.mp hP)
  let evar : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let emap : σ ≃ ι := Equiv.ofBijective P.map
    ((Fintype.bijective_iff_injective_and_card P.map).mpr ⟨P.map_inj, hcard⟩)
  let erel : Fin (Fintype.card ι) ≃ σ := evar.trans emap.symm
  let Q := P.reindex evar erel
  refine ⟨Fintype.card ι, Q, fun i ↦ ?_⟩
  change evar.symm (emap (emap.symm (evar i))) = i
  simp

/-- The algebra presented by the relations of a submersive presentation is the presented
algebra. -/
private noncomputable def squarePresentationEquiv {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B] {n : ℕ}
    (Q : Algebra.SubmersivePresentation A B (Fin n) (Fin n)) :
    presentedAlgebra A Q.relation ≃ₐ[A] B :=
  (Ideal.quotientEquivAlgOfEq A Q.span_range_relation_eq_ker).trans
    (Q.quotientEquiv.restrictScalars A)

/-- **[Stacks Project, Tag 00U9] in presented form.**  An étale algebra is, as an algebra over its
base, the quotient of a polynomial ring in finitely many variables by *equally many* relations.

No invertible Jacobian is recorded: the determinant is available (it is
`StandardEtalePresentation.jacobian_isUnit` below) but a consumer which only needs the étaleness of
the presented algebra can recover it from the étaleness of the algebra itself, and faithful
flatness — which
`AlgebraicGeometry.ProEtale.exists_standardEtalePresentation_of_etale_faithfullyFlat` requires —
is not needed for the presentation alone. -/
lemma exists_fin_algEquiv_quotientSpanRange_of_etale {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (he : Algebra.Etale A B) :
    ∃ (n : ℕ) (P : Fin n → MvPolynomial (Fin n) A),
      Nonempty (B ≃ₐ[A] (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range P))) := by
  obtain ⟨n, Q, _⟩ := exists_square_submersive_presentation he
  exact ⟨n, Q.relation, ⟨(squarePresentationEquiv Q).symm⟩⟩

/-- Every faithfully flat étale `A`-algebra is isomorphic to the algebra presented by an element
of `StandardEtalePresentation A`. -/
lemma exists_standardEtalePresentation_of_etale_faithfullyFlat
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (he : Algebra.Etale A B) (hf : (algebraMap A B).FaithfullyFlat) :
    ∃ p : StandardEtalePresentation A,
      Nonempty (presentedAlgebra A p.relations ≃ₐ[A] B) := by
  obtain ⟨n, Q, hQ⟩ := exists_square_submersive_presentation he
  let e := squarePresentationEquiv Q
  have hJ : IsUnit (Ideal.Quotient.mk (Ideal.span (Set.range Q.relation))
      (Matrix.det (fun i j ↦ pderiv i (Q.relation j)))) := by
    rw [← MulEquiv.isUnit_map e.toMulEquiv]
    convert Q.jacobian_isUnit using 1
    rw [Q.jacobian_eq_jacobiMatrix_det, jacobiMatrix_eq_pderiv Q.toPreSubmersivePresentation hQ]
    simp [e, squarePresentationEquiv]
  let p : StandardEtalePresentation A :=
    { variableCount := n
      relations := Q.relation
      jacobian_isUnit := hJ
      faithfullyFlat := by
        have : Module.FaithfullyFlat A B :=
          RingHom.faithfullyFlat_algebraMap_iff.mp hf
        exact RingHom.faithfullyFlat_algebraMap_iff.mpr
          (Module.FaithfullyFlat.of_linearEquiv A B e.toLinearEquiv) }
  exact ⟨p, ⟨e⟩⟩

end AlgebraicGeometry.ProEtale

end
