module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.StandardPresentationExists
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.PresentationEtale
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtaleConstruction.Presentation

/-!
# Every affine étale chart of an affine scheme carries a standard presentation

`Stacks.EtaleCohomology.StandardPresentationOver` is the datum
`Γ(V, ⊤) = Γ(S, ⊤)[x₁, …, xₙ]/(P₁, …, Pₙ)` of step (2) of the proof of [Stacks Project, Tag 04I6].
For `S` affine and `V` an *affine* object of the small étale site of `S`, such a presentation
exists.

This is [Stacks Project, Tag 00U9]. The chart is étale over `S` because it is an object of the
small étale site (`AlgebraicGeometry.SmallEtale.etale_structureMorphism`); both schemes being
affine, the ring map on global functions is étale
(`AlgebraicGeometry.HasRingHomProperty.iff_of_isAffine`), and an étale algebra is the quotient of a
polynomial ring in `n` variables by `n` relations,
`AlgebraicGeometry.ProEtale.exists_fin_algEquiv_quotientSpanRange_of_etale`.

## Main results

* `Stacks.EtaleCohomology.exists_standardPresentationOverSmallEtale`: an affine object of the
  small étale site of an affine scheme carries a standard presentation.

## Implementation notes

The `Γ(S, ⊤)`-algebra structure on `Γ(V, ⊤)` is the one given by the structure morphism of the
chart, so the compatibility field `comp_iso_hom` of
`Stacks.EtaleCohomology.StandardPresentationOver` is exactly the statement that the algebra
equivalence commutes with the two structure maps; it is `AlgEquiv.commutes` read in `CommRingCat`.
This is the reverse of `Stacks.EtaleCohomology.StandardPresentationOver.algEquiv`, which reads the
field as an algebra equivalence.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 00U9](https://stacks.math.columbia.edu/tag/00U9)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- **Every affine étale chart of an affine scheme carries a standard presentation**
([Stacks Project, Tag 00U9]): there are an `n` and a square system `P` of `n` polynomials in `n`
variables over `Γ(S, ⊤)` with `Γ(V, ⊤) = Γ(S, ⊤)[x₁, …, xₙ]/(P₁, …, Pₙ)` as `Γ(S, ⊤)`-algebras. -/
theorem exists_standardPresentationOverSmallEtale {B : AlgebraicGeometry.BigEtaleSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S} [IsAffine S]
    (V : AlgebraicGeometry.SmallEtale B S hS)
    [IsAffine ((AlgebraicGeometry.SmallEtale.toScheme B S hS).obj V)] :
    ∃ (n : ℕ) (P : Fin n → MvPolynomial (Fin n) Γ(S, ⊤)),
      Nonempty (StandardPresentationOver
        ((AlgebraicGeometry.SmallEtale.toScheme B S hS).obj V)
        (AlgebraicGeometry.SmallEtale.schemeStructureHom B S hS V) P) := by
  obtain ⟨n, P, hP, -⟩ := exists_standardPresentationOver
    (Y := S) (V := (AlgebraicGeometry.SmallEtale.toScheme B S hS).obj V)
    (pV := AlgebraicGeometry.SmallEtale.schemeStructureHom B S hS V)
  exact ⟨n, P, hP⟩

end Stacks.EtaleCohomology

end
