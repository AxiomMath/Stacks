module

public import StacksFrontier.AlgebraicGeometry.Conormal.ChartAssociatedGraded
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ConormalApproximation

/-!
# The chart of a base change, presented as the concrete quotient Stacks 0CAY compares

Stacks 0CAY compares the conormal algebras of the two closed immersions `Y_t ↪ Y_σ` and
`Y_t ↪ Y_{σ'}` chart by chart, and on a chart the comparison it has available is the *algebraic*
one `Stacks.ConormalApproximation.exists_finiteType_coefficients_associatedGraded_equiv`: an
`AssociatedGraded.GradedAlgEquiv J (A ⧸ R) (A ⧸ R')` where `A = D[x_1, …, x_n]` is a polynomial
ring over `D = 𝒪^∧_{S,s}`, the two ideals `R`, `R'` are the modules of relations of the two
specialised relation matrices, and `J = I · A` for the ideal `I ⊆ D`.

`Stacks.Conormal.ChartAssociatedGradedEquiv.ofQuotientPresentation` turns such a comparison into
the chart-local comparison the gluing pipeline consumes, given for each side a
`Stacks.Conormal.ChartQuotientPresentation`: an identification of the chart ring with `A ⧸ R`
carrying the kernel ideal of the immersion to the image of `J`. This file supplies that
identification from the two facts about the particular immersion that the source uses — the chart
of `Y_σ` is `Spec(B ⊗_{C,σ} D)`, and the fibre is cut out in it by `I`.

## Main results

* `Stacks.ConormalApproximation.ker_tensorQuotientMap`: **the fibre is cut out by `I`** — the
  kernel of the base change `B ⊗_{C,σ} D → B ⊗_{C,σ} (D ⧸ I)` of the quotient by `I` is the ideal
  that `I` generates in `B ⊗_{C,σ} D`.
* `Stacks.ConormalApproximation.chartQuotientPresentationOfBaseChange`: **the chart presentation**
  — an identification of the functions on an affine chart with the base change `B ⊗_{C,σ} D`,
  under which the kernel ideal of the immersion is the ideal `I` generates, presents the chart
  ring as `A ⧸ R` with the kernel ideal the image of `J = I · A`.

## Implementation notes

The identification of the chart ring with `B ⊗_{C,σ} D` is taken as a hypothesis, as is the
description of the kernel ideal: both are statements about one affine chart of the base change
`Y ×_T Spec(D)` of a morphism of schemes, and neither is about conormal algebras. What this file
adds is the passage from them to the ambient *polynomial* ring over which the algebraic
comparison is stated, which is `Stacks.ConormalApproximation.quotRangeEquivTensor` — Stacks 0CAZ —
together with the matching of the two ideals,
`Stacks.ConormalApproximation.map_symm_quotRangeEquivTensor_map_algebraMap`.

A map `σ : C →+* D` that is not the `algebraMap` of an ambient `Algebra C D` instance — the
primed side of 0CAY, where `σ' = τ' ∘ (C → C')` — is handled by the caller installing
`σ'.toAlgebra`, for which `algebraMap C D` is `σ'`; the relation matrix
`relationMapOfHom σ' P.relation` is then the one of this file's statements.

## References

* [Stacks Project, Tag 0CAY](https://stacks.math.columbia.edu/tag/0CAY)
* [Stacks Project, Tag 0CAZ](https://stacks.math.columbia.edu/tag/0CAZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TensorProduct

universe u v w

namespace Stacks.ConormalApproximation

/-- **The fibre of a base change is cut out by the ideal of the base.** The kernel of the map
`B ⊗_{C,σ} D → B ⊗_{C,σ} (D ⧸ I)` obtained by base changing the quotient by `I` is the ideal that
`I` generates in `B ⊗_{C,σ} D`. For `I` the maximal ideal of `D = 𝒪^∧_{S,s}` this is the statement
that the fibre `Y_t` is cut out in the chart of `Y_σ` by the maximal ideal, the geometric input of
Stacks 0CAY read on one chart. -/
theorem ker_tensorQuotientMap {C : Type u} {B : Type v} {D : Type w}
    [CommRing C] [CommRing B] [CommRing D] [Algebra C B] [Algebra C D] (I : Ideal D) :
    RingHom.ker (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ C I) (AlgHom.id C B)) =
      I.map (algebraMap D (TensorProduct C D B)) := by
  rw [Algebra.TensorProduct.rTensor_ker (Ideal.Quotient.mkₐ C I) Ideal.Quotient.mk_surjective,
    ← RingHom.ker_coe_toRingHom, Ideal.Quotient.mkₐ_ker]
  rfl

/-- **The chart of `Y_σ` is `Spec(A ⧸ R)` with the fibre cut out by the image of `J`.**
Let `B = C[x_1, …, x_n]/(f_1, …, f_m)` be presented over `C`, let `σ : C → D` make `D` a
`C`-algebra and let `I ⊆ D` be an ideal. Suppose the functions on an affine chart `V` of the
ambient scheme of an immersion `i` are identified with the base change `B ⊗_{C,σ} D` in such a way
that the kernel ideal of `i` on that chart becomes the ideal `I` generates — that is, the chart is
`Spec(B ⊗_{C,σ} D)` and the source is the closed subscheme cut out by `I`, which for `I` the
maximal ideal of `D` is the fibre. Then the chart ring is presented as the quotient of
`A = D[x_1, …, x_n]` by the module of relations, with the kernel ideal the image of `J = I · A`.

This is the data `Stacks.Conormal.ChartAssociatedGradedEquiv.ofQuotientPresentation` consumes,
over the very ambient ring and ideal that
`Stacks.ConormalApproximation.exists_finiteType_coefficients_associatedGraded_equiv` compares
across. -/
def chartQuotientPresentationOfBaseChange {Z X : Scheme.{u}} (i : Z ⟶ X) (V : X.affineOpens)
    {C : Type v} {B : Type w} {D : Type*} [CommRing C] [CommRing B] [CommRing D]
    [Algebra C B] [Algebra C D] {n m : ℕ} (P : Algebra.Presentation C B (Fin n) (Fin m))
    (I : Ideal D) (eq : Γ(X, V) ≃+* TensorProduct C D B)
    (hker : (Stacks.Conormal.chartIdeal i V).map (eq : Γ(X, V) →+* TensorProduct C D B) =
      I.map (algebraMap D (TensorProduct C D B))) :
    Stacks.Conormal.ChartQuotientPresentation i V
      (I.map (MvPolynomial.C : D →+* MvPolynomial (Fin n) D))
      (LinearMap.range (relationMapOfHom (algebraMap C D) P.relation)) where
  equiv := eq.trans (quotRangeEquivTensor D P).symm.toRingEquiv
  map_chartIdeal := by
    have h : (Stacks.Conormal.chartIdeal i V).map
          ((eq.trans (quotRangeEquivTensor D P).symm.toRingEquiv :
            Γ(X, V) ≃+* MvPolynomial (Fin n) D ⧸
              LinearMap.range (relationMapOfHom (algebraMap C D) P.relation)) :
            Γ(X, V) →+* MvPolynomial (Fin n) D ⧸
              LinearMap.range (relationMapOfHom (algebraMap C D) P.relation)) =
        ((Stacks.Conormal.chartIdeal i V).map
            (eq : Γ(X, V) →+* TensorProduct C D B)).map
          ((quotRangeEquivTensor D P).symm.toRingEquiv :
            TensorProduct C D B →+*
              MvPolynomial (Fin n) D ⧸
                LinearMap.range (relationMapOfHom (algebraMap C D) P.relation)) := by
      rw [Ideal.map_map]
      rfl
    rw [h, hker, map_symm_quotRangeEquivTensor_map_algebraMap]

/-- **The chart presentation from the affine description of the chart and of the fibre.** The
hypotheses are the two identifications of Stacks 0CAY's first step on one chart — the functions on
the chart of the ambient are the base change `B ⊗_{C,σ} D`, the functions on the corresponding
chart of the source are the base change `B ⊗_{C,σ} (D ⧸ I)` — together with the statement that the
restriction map between them is the base change of the quotient by `I`. The kernel ideal is then
the ideal `I` generates, by `ker_tensorQuotientMap`, and
`chartQuotientPresentationOfBaseChange` applies. -/
def chartQuotientPresentationOfBaseChangeFibre {Z X : Scheme.{u}} (i : Z ⟶ X)
    (V : X.affineOpens) {C : Type v} {B : Type w} {D : Type*} [CommRing C] [CommRing B]
    [CommRing D] [Algebra C B] [Algebra C D] {n m : ℕ}
    (P : Algebra.Presentation C B (Fin n) (Fin m)) (I : Ideal D)
    (eq : Γ(X, V) ≃+* TensorProduct C D B)
    (eqZ : Γ(Z, i ⁻¹ᵁ V.1) ≃+* TensorProduct C (D ⧸ I) B)
    (hres : ∀ x : Γ(X, V), eqZ ((i.app V).hom x) =
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ C I) (AlgHom.id C B) (eq x)) :
    Stacks.Conormal.ChartQuotientPresentation i V
      (I.map (MvPolynomial.C : D →+* MvPolynomial (Fin n) D))
      (LinearMap.range (relationMapOfHom (algebraMap C D) P.relation)) :=
  chartQuotientPresentationOfBaseChange i V P I eq (by
    have key : Stacks.Conormal.chartIdeal i V =
        (RingHom.ker (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ C I)
          (AlgHom.id C B))).comap (eq : Γ(X, V) →+* TensorProduct C D B) := by
      ext x
      rw [RingHom.mem_ker, Ideal.mem_comap, RingHom.mem_ker,
        show (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ C I) (AlgHom.id C B))
            ((eq : Γ(X, V) →+* TensorProduct C D B) x) = eqZ ((i.app V).hom x) from (hres x).symm]
      exact (map_eq_zero_iff eqZ eqZ.injective).symm
    rw [key, Ideal.map_comap_of_surjective (eq : Γ(X, V) →+* TensorProduct C D B) eq.surjective,
      ker_tensorQuotientMap])

end Stacks.ConormalApproximation

end
