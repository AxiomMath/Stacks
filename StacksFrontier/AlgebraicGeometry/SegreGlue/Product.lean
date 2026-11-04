module

public import StacksFrontier.AlgebraicGeometry.SegreGlue.Glue
public import StacksFrontier.AlgebraicGeometry.SegreProjection.Handover

/-!
# The Segre projection to the product

`Stacks.AlgebraicGeometry.SegreClosedImmersion.absoluteSegre_of_projSegreIso` reduces Stacks Tag
01WD to *an* isomorphism between `AlgebraicGeometry.Proj` of the Segre product and the product of
the two integral models of projective space.  This file names the morphism:
`Stacks.AlgebraicGeometry.SegreGlue.segreProd`, the pair of glued Segre projections
`Stacks.AlgebraicGeometry.SegreGlue.projLeftGlued` and
`Stacks.AlgebraicGeometry.SegreGlue.projRightGlued`, and derives Tag 01WD from its being an
isomorphism.  That it is one is `Stacks.AlgebraicGeometry.SegreProdIso.isIso_segreProd`.

## Main definitions

* `Stacks.AlgebraicGeometry.SegreGlue.segreProd`: the morphism
  `Proj (Segre product) ⟶ ℙᵐ ×  ℙⁿ` obtained from the two glued projections by the universal
  property of the fibre product.

## Main results

* `Stacks.AlgebraicGeometry.SegreGlue.absoluteSegre_of_isIso_segreProd`: if `segreProd n m` is an
  isomorphism then `Stacks.AlgebraicGeometry.SegreEmbedding.AbsoluteSegre n m` holds.

* `Stacks.AlgebraicGeometry.SegreGlue.exists_segreEmbedding_of_isIso_segreProd`: the statement of
  Tag 01WD itself, over an arbitrary base scheme, from the same hypothesis.

## Implementation notes

The product of the two projective spaces is `AlgebraicGeometry.projectiveSpaceOver m` applied to
`AlgebraicGeometry.projectiveSpaceAtUniverse n`, which is by definition the fibre product of the
two integral models over the terminal scheme.  The compatibility condition that
`CategoryTheory.Limits.pullback.lift` asks for is therefore an equality of two morphisms into the
terminal scheme, and holds by `CategoryTheory.Limits.terminal.hom_ext`.

Both gradings are definitions rather than instances, and a local instance introduced in a
*statement* does not survive into the proof of that statement; so the canonical gradings are
supplied in the *body* of `segreProd`, and the statements below mention only the named objects
`Stacks.AlgebraicGeometry.SegreClosedImmersion.projSegre`,
`AlgebraicGeometry.projectiveSpaceAtUniverse` and `AlgebraicGeometry.projectiveSpaceOver`, and so
carry no local instance.

For the same reason no simp lemma identifying `segreProd n m ≫ pullback.fst _ _` with
`Stacks.AlgebraicGeometry.SegreGlue.projLeftGlued` is stated here: its statement would have to
name the glued projection, which only exists under a local grading instance.  The identification
is `CategoryTheory.Limits.pullback.lift_fst` and is available by unfolding `segreProd`.

## References

* [Stacks Project, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.AlgebraicGeometry.SegreGlue

universe u

/-- **The Segre projection to the product.**  The two glued Segre projections, assembled by the
universal property of the fibre product into a single morphism from `AlgebraicGeometry.Proj` of
the Segre product to the product of the two integral models of projective space. -/
public def segreProd (n m : ℕ) :
    SegreClosedImmersion.projSegre (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) ⟶
      projectiveSpaceOver m (projectiveSpaceAtUniverse.{u} n) :=
  letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
    MvPolynomial.gradedAlgebra
  letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) :=
    MvPolynomial.gradedAlgebra
  letI := Stacks.RingTheory.SegreProduct.gradingGradedAlgebra (ULift.{u} ℤ)
    (Fin (n + 1)) (Fin (m + 1))
  pullback.lift
    (projLeftGlued (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)))
    (projRightGlued (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)))
    (terminal.hom_ext _ _)

/-- If the Segre projection to the product is an isomorphism then
`Stacks.AlgebraicGeometry.SegreEmbedding.AbsoluteSegre n m` holds. -/
public theorem absoluteSegre_of_isIso_segreProd (n m : ℕ) (h : IsIso (segreProd.{u} n m)) :
    SegreEmbedding.AbsoluteSegre.{u} n m :=
  SegreClosedImmersion.absoluteSegre_of_projSegreIso n m (asIso (segreProd.{u} n m))

/-- **Tag 01WD from the isomorphism of the named morphism.**  If the Segre projection to the
product is an isomorphism then, over every base scheme `S`, the fibre product of `ℙⁿ_S` and
`ℙᵐ_S` over `S` admits a closed immersion into `ℙ^{nm+n+m}_S` over `S`. -/
public theorem exists_segreEmbedding_of_isIso_segreProd (n m : ℕ) (S : Scheme.{u})
    (h : IsIso (segreProd.{u} n m)) :
    ∃ f : pullback ((projectiveSpaceOver n S) ↘ S) ((projectiveSpaceOver m S) ↘ S) ⟶
        projectiveSpaceOver (n * m + n + m) S,
      IsClosedImmersion f ∧
        f ≫ ((projectiveSpaceOver (n * m + n + m) S) ↘ S) =
          pullback.fst ((projectiveSpaceOver n S) ↘ S) ((projectiveSpaceOver m S) ↘ S) ≫
            ((projectiveSpaceOver n S) ↘ S) :=
  SegreEmbedding.exists_segreEmbedding_of_absolute n m S
    (absoluteSegre_of_isIso_segreProd n m h)

end Stacks.AlgebraicGeometry.SegreGlue

end
