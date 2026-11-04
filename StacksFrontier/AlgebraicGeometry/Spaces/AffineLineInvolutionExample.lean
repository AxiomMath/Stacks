module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionUniversalHomeomorphism

/-!
# The affine line with its nonzero points identified with their negatives (Stacks 05Z6)

Let `k` be a field in which `2` is invertible, let `B` be a big fppf site containing
`Spec k` and let `X = 𝐀¹_k/\{x ∼ -x ∣ x ≠ 0\}` be the quotient of the affine line by the
punctured graph of negation, the algebraic space of Stacks 02Z1.  **Stacks 05Z6** asserts, of
the two morphisms
`𝐀¹_k ⟶ X ⟶ 𝐀¹_k`
— the projection onto the quotient and the morphism descended from squaring the coordinate —
that the first is étale surjective, that the second is universally injective, that their
composition is the map `x ↦ x²` and hence universally closed, and that the second morphism is
therefore a universal homeomorphism although it is not separated.

This file states all of that as a single result,
`AlgebraicGeometry.AffineLineInvolution.nonSeparatedUniversalHomeomorphism_squaringMap`.  The
two morphisms are not produced existentially: the source's `𝐀¹_k → X` is
`Stacks.Groupoids.toQuotientSheaf` of the relation of Stacks 02Z1 and its `X → 𝐀¹_k` is
`AlgebraicGeometry.AffineLineInvolution.squaringMap`, so every assertion of the example is
made of those two named morphisms.  Both ends of the chain are the same object, the restricted
functor of points of the affine line, and the composition is accordingly an endomorphism of it,
as in the source.  Nothing is left to a caller: no existential escape, no clause handed out as
a hypothesis, no `Prop` binder standing in for content.

## Main results

* `AlgebraicGeometry.AffineLineInvolution.nonSeparatedUniversalHomeomorphism_squaringMap`: the
  whole of **Stacks 05Z6** — the quotient is an algebraic space, the chart onto it is surjective
  and étale, the squaring map out of it is universally injective, the composite of the two is
  squaring the coordinate and is universally closed, and the squaring map is a universal
  homeomorphism which is not separated.

## Implementation notes

Each clause is a result the library already has, and the statement below is their conjunction:

* `AlgebraicGeometry.AffineLineInvolution.isAlgebraicSpace_involutionQuotient_of_isAffineHom`
  for the algebraic-space property of the quotient, which is Stacks 02Z1 with the
  effective-descent hypotheses of Stacks 0265 discharged by affineness of the relation;
* `AlgebraicGeometry.AffineLineInvolution.presheafSurjective_quotientChart` and
  `AlgebraicGeometry.AffineLineInvolution.presheafEtale_quotientChart` for the first arrow,
  read through `AlgebraicGeometry.AffineLineInvolution.affineLinePointsIso`;
* `AlgebraicGeometry.AffineLineInvolution.universallyInjective_squaringMap`, which is part (4)
  of Stacks 05VS;
* `AlgebraicGeometry.AffineLineInvolution.toQuotientSheaf_comp_squaringMap` for the
  composition, and
  `AlgebraicGeometry.Space.universallyClosed_toQuotientSheaf_comp_squaringMap` for its
  universal closedness, which comes from integrality of squaring on the affine line;
* `AlgebraicGeometry.AffineLineInvolution.universalHomeomorphism_squaringMap` and
  `AlgebraicGeometry.AffineLineInvolution.not_isSeparated_squaringMap` for the two concluding
  assertions.

The surjectivity and étaleness of the first arrow are the representable morphism properties of
`CategoryTheory.MorphismProperty.presheaf`: the arrow is relatively representable and every
represented base change of it is a surjective, resp. étale, morphism of schemes.  The library
proves them of `AlgebraicGeometry.AffineLineInvolution.quotientChart`, the same arrow with its
source spelled as the presheaf represented by the chart of the affine line rather than as the
restricted functor of points; the two differ by precomposition with
`AlgebraicGeometry.AffineLineInvolution.affineLinePointsIso`, and
`CategoryTheory.MorphismProperty.relative_respectsIso` carries each property across it.  The
spelling used here is the one in which both ends of `𝐀¹_k ⟶ X ⟶ 𝐀¹_k` are the same object, so
that the composition is an endomorphism of `𝐀¹_k` and the assertion that it is `x ↦ x²` is an
equality of endomorphisms.

The hypothesis `(2 : k) ≠ 0` is the standing hypothesis of the example: the graph of negation
on the punctured line is a relation on the affine line only when `-1 ≠ 1`, and in
characteristic two the relation is the diagonal, the quotient is the affine line itself and the
final assertion is false.  It is the hypothesis under which the quotient of Stacks 02Z1 is
formed, not an extra assumption on the conclusions; the clauses which do not need it are proved
in the library without it.

## References

* [Stacks Project, Tag 05Z6](https://stacks.math.columbia.edu/tag/05Z6)
* [Stacks Project, Tag 02Z1](https://stacks.math.columbia.edu/tag/02Z1)
* [Stacks Project, Tag 05VS](https://stacks.math.columbia.edu/tag/05VS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AffineLineInvolution

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)]

/-- The chart of the involution quotient, read on the restricted functor of points of the
affine line, is the projection onto the quotient sheaf precomposed with
`AlgebraicGeometry.AffineLineInvolution.affineLinePointsIso`. -/
private theorem affineLinePointsIso_hom_comp_quotientChart :
    (affineLinePointsIso k B hk).hom ≫ quotientChart k B hk =
      Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
        (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k) :=
  (affineLinePointsIso k B hk).hom_inv_id_assoc _

/-- A representable morphism property of the chart of the involution quotient holds of the
projection onto the quotient sheaf: the two differ by precomposition with the isomorphism
`AlgebraicGeometry.AffineLineInvolution.affineLinePointsIso`, and a property of the form
`CategoryTheory.MorphismProperty.presheaf` respects isomorphisms. -/
private theorem presheaf_toQuotientSheaf_of_presheaf_quotientChart
    (P : MorphismProperty (BigFppfOver B (Spec (.of k)) hk))
    (hP : P.presheaf (quotientChart k B hk)) :
    P.presheaf (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
      (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k)) :=
  affineLinePointsIso_hom_comp_quotientChart k B hk ▸
    MorphismProperty.RespectsIso.precomp P.presheaf (affineLinePointsIso k B hk).hom
      (quotientChart k B hk) hP

/-- **Stacks 05Z6.**  Let `k` be a field in which `2` is invertible, let `B` be a big fppf site
containing `Spec k`, and let `X = 𝐀¹_k/\{x ∼ -x ∣ x ≠ 0\}` be the quotient of the affine line
by the punctured graph of negation.  Then `X` is an algebraic space over `k`, and of the two
morphisms
`𝐀¹_k ⟶ X ⟶ 𝐀¹_k`,
the projection onto the quotient and the morphism descended from squaring the coordinate:

1. the first is surjective and étale;
2. the second is universally injective;
3. their composition is the map `x ↦ x²`;
4. hence that composition is universally closed;
5. therefore the second morphism is a universal homeomorphism;
6. but the second morphism is not separated.

The projection is surjective and étale because the relation is an étale equivalence relation
whose morphism into the self-product of the affine line is affine, which makes the presentation
of Stacks 0265 unconditional here.  Squaring is injective on field-valued points up to the
relation and integral on the affine line, which gives (2) and (4); a universally injective,
universally closed and surjective morphism of algebraic spaces is a universal homeomorphism,
which gives (5).  For (6) the relation is a represented base change of the relative diagonal of
the squaring map and is not a closed immersion, its restriction to the punctured summand
factoring through the split section of the fibre square with components the identity and
negation. -/
@[stacks 05Z6]
theorem nonSeparatedUniversalHomeomorphism_squaringMap (hchar : (2 : k) ≠ 0) :
    IsAlgebraicSpace B (Spec (.of k)) hk (involutionQuotient k B hk).obj ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B (Spec (.of k)) hk)).presheaf
          (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
            (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k)) ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B (Spec (.of k)) hk)).presheaf
          (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
            (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k)) ∧
      Space.UniversallyInjective B (Spec (.of k)) hk (squaringMap k B hk) ∧
      Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
            (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k) ≫
          squaringMap k B hk =
        (Over.post (X := B.obj hk) B.inclusion).op.whiskerLeft
          (yoneda.map (affineLineSquare k)) ∧
      Space.UniversallyClosed B (Spec (.of k)) hk
          (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
              (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k) ≫
            squaringMap k B hk) ∧
      Space.UniversalHomeomorphism B (Spec (.of k)) hk (squaringMap k B hk) ∧
      ¬ Space.IsSeparated B (Spec (.of k)) hk (squaringMap k B hk) :=
  ⟨isAlgebraicSpace_involutionQuotient_of_isAffineHom k B hk hchar,
    presheaf_toQuotientSheaf_of_presheaf_quotientChart k B hk _
      (presheafSurjective_quotientChart k B hk hchar),
    presheaf_toQuotientSheaf_of_presheaf_quotientChart k B hk _
      (presheafEtale_quotientChart k B hk hchar),
    universallyInjective_squaringMap k hchar B hk,
    toQuotientSheaf_comp_squaringMap k B hk,
    Space.universallyClosed_toQuotientSheaf_comp_squaringMap B k hk,
    universalHomeomorphism_squaringMap k B hk hchar,
    not_isSeparated_squaringMap k B hk hchar⟩

end AlgebraicGeometry.AffineLineInvolution

end
