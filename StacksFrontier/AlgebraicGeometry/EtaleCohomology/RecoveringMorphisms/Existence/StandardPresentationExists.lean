module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.RepresentableEqualizer
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Etale.StandardEtale
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.StandardPresentationExists

/-!
# Standard presentations of affine étale schemes over an affine base

An étale morphism `p : V ⟶ Y` of affine schemes admits a *standard presentation*
`Γ(V, ⊤) ≅ Γ(Y, ⊤)[x₁, …, xₙ]/(P₁, …, Pₙ)` with as many relations as variables, and the
presented algebra is étale over `Γ(Y, ⊤)`.  This is Stacks 00U9 read through Mathlib's
`Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`, packaged as the datum
`Stacks.EtaleCohomology.StandardPresentationOver` which step (2) of the proof of Stacks 04I6
consumes, and which was taken there as a datum rather than produced.

## References

* [Stacks Project, Tag 00U9](https://stacks.math.columbia.edu/tag/00U9)
* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.EtaleCohomology

/-- An étale algebra is presented by a square system of relations. -/
theorem exists_square_presentation_of_etale {A C : Type u} [CommRing A] [CommRing C]
    [Algebra A C] [Algebra.Etale A C] :
    ∃ (n : ℕ) (P : Fin n → MvPolynomial (Fin n) A),
      Nonempty ((MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range P)) ≃ₐ[A] C) := by
  have hs : Algebra.IsStandardSmoothOfRelativeDimension 0 A C :=
    Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp inferInstance
  obtain ⟨ι, σ, hσ, hι, Q, hQ⟩ := hs.out
  have : Finite ι := hι
  have : Finite σ := hσ
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : Fintype σ := Fintype.ofFinite σ
  have hcard : Fintype.card σ = Fintype.card ι := by
    dsimp [Algebra.Presentation.dimension] at hQ
    simpa only [Nat.card_eq_fintype_card] using Nat.le_antisymm
      Q.card_relations_le_card_vars_of_isFinite (Nat.sub_eq_zero_iff_le.mp hQ)
  have hb : Function.Bijective Q.map :=
    (Fintype.bijective_iff_injective_and_card Q.map).mpr ⟨Q.map_inj, hcard⟩
  let evar : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let emap : σ ≃ ι := Equiv.ofBijective Q.map hb
  let erel : Fin (Fintype.card ι) ≃ σ := evar.trans emap.symm
  let Q' := Q.reindex evar erel
  exact ⟨Fintype.card ι, Q'.relation, ⟨(Ideal.quotientEquivAlgOfEq A
    Q'.span_range_relation_eq_ker).trans (Q'.quotientEquiv.restrictScalars A)⟩⟩

end Stacks.EtaleCohomology
