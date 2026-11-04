module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionSquaringMap
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAffineRelation

/-!
# The étale presentation of the quotient of the affine line by the punctured involution

The example of Stacks 05Z6 exhibits two morphisms
`𝐀¹_k ⟶ X ⟶ 𝐀¹_k` with `X = 𝐀¹_k/\{x ∼ -x ∣ x ≠ 0\}`, the first étale surjective, the second
universally injective, whose composite is `x ↦ x²` and therefore universally closed. **This file
supplies the first assertion: the chart `𝐀¹_k ⟶ X` is surjective and étale, with no
hypothesis.**

Surjectivity and étaleness of a quotient chart are two of the three conclusions of Stacks 0265,
and in this development they come with a descent hypothesis — see
`AlgebraicGeometry.Space.surjective_toQuotientSheaf` and
`AlgebraicGeometry.Space.etale_toQuotientSheaf`. The hypothesis is discharged here because the
relation of this example is an **affine** morphism:
`AlgebraicGeometry.Space.etale_toQuotientSheaf_of_isAffineHom` asks nothing else. The relation
scheme `𝐀¹_k ⨿ (𝐀¹_k ∖ \{0\})` is affine, being a coproduct of two affines, and the self-product
`𝐀¹_k ×_k 𝐀¹_k` is affine, being a fibre product of affines over an affine base; a morphism
between affine schemes is affine.

## Main results

* `AlgebraicGeometry.AffineLineInvolution.isAffine_relationScheme` and
  `AlgebraicGeometry.AffineLineInvolution.isAffine_prod_affineLine`: the source and the target of
  the relation of Stacks 02Z1 are affine, so the relation is an affine morphism, by Mathlib's
  instance `AlgebraicGeometry.isAffineHom_of_isAffine`.
* `AlgebraicGeometry.AffineLineInvolution.isAlgebraicSpace_involutionQuotient_of_isAffineHom`:
  **Stacks 02Z1 with both descent hypotheses discharged** — away from characteristic two the
  quotient is an algebraic space over the ground field, outright.
* `AlgebraicGeometry.AffineLineInvolution.presheafSurjective_quotientChart` and
  `AlgebraicGeometry.AffineLineInvolution.presheafEtale_quotientChart`: **the étale presentation
  of Stacks 05Z6** — the chart `𝐀¹_k ⟶ X` is surjective and étale, with no hypothesis beyond
  characteristic different from two.

## Implementation notes

The chart of this example, `AlgebraicGeometry.AffineLineInvolution.quotientChart`, is
definitionally `Stacks.Groupoids.quotientChart` of the involution relation at the chart
`AlgebraicGeometry.AffineLineInvolution.affineLineChart`: both are the canonical map
`yoneda.obj U ⟶ (U/R)` on the representable presheaf, the identification of the restricted
functor of points of the affine line with that presheaf being
`AlgebraicGeometry.Space.pointsYonedaIso`.

Characteristic different from two enters only through
`AlgebraicGeometry.AffineLineInvolution.isEtaleEquivalenceRelation`: the graph of negation is a
*relation* on the affine line only when `-1 ≠ 1`, since otherwise the two legs of the punctured
summand agree and the induced map to the self-product is not a monomorphism. Affineness of the
relation needs no such hypothesis, and is stated without one.

## References

* [Stacks Project, Tag 05Z6](https://stacks.math.columbia.edu/tag/05Z6)
* [Stacks Project, Tag 02Z1](https://stacks.math.columbia.edu/tag/02Z1)
* [Stacks Project, Tag 0265](https://stacks.math.columbia.edu/tag/0265)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AffineLineInvolution

variable (k : Type u) [Field k]

/-- The relation scheme of Stacks 02Z1 is affine: it is the coproduct of the affine line and of
its puncture, both affine, and binary coproducts in `CategoryTheory.Over S` are created by the
forgetful functor to schemes. -/
instance isAffine_relationScheme : IsAffine (relationScheme k).left :=
  have _h1 : IsAffine ((Over.forget (Spec (.of k))).obj (affineLine k)) :=
    isAffine_affineLine k
  have _h2 : IsAffine ((Over.forget (Spec (.of k))).obj (puncturedAffineLine k)) :=
    isAffine_puncturedAffineLine k
  IsAffine.of_isIso
    (PreservesColimitPair.iso (Over.forget (Spec (.of k)))
      (affineLine k) (puncturedAffineLine k)).inv

/-- The self-product of the affine line over the ground field is affine: the binary product in
`CategoryTheory.Over (Spec k)` is the fibre product of the two structure morphisms, by
`CategoryTheory.Over.prodLeftIsoPullback`, and the structure morphism of the affine line is an
affine morphism. -/
instance isAffine_prod_affineLine :
    IsAffine ((affineLine k ⨯ affineLine k : Over (Spec (.of k))).left) :=
  have _h : IsAffineHom (affineLine k).hom := inferInstance
  IsAffine.of_isIso (Over.prodLeftIsoPullback (affineLine k) (affineLine k)).hom

variable (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)]

/-- **Stacks 02Z1 with no descent hypothesis.** Away from characteristic two the quotient of the
affine line by the punctured graph of negation is an algebraic space over the ground field.

This is `AlgebraicGeometry.AffineLineInvolution.isAlgebraicSpace_involutionQuotient` with both
instances of `AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve` discharged, which is
possible because the relation is affine, being a morphism between affine schemes
(`AlgebraicGeometry.isAffineHom_of_isAffine`). -/
theorem isAlgebraicSpace_involutionQuotient_of_isAffineHom (hchar : (2 : k) ≠ 0) :
    IsAlgebraicSpace B (Spec (.of k)) hk (involutionQuotient k B hk).obj :=
  have : NeZero (2 : k) := ⟨hchar⟩
  have _hrel : Stacks.Groupoids.IsEtaleEquivalenceRelation
      (R := relationScheme k)
      (U := (Over.post B.inclusion).obj (affineLineChart k B hk))
      (involutionRelation k) := isEtaleEquivalenceRelation k
  Space.isAlgebraicSpace_quotientSheaf_of_isAffineHom B (Spec (.of k)) hk
    (affineLineChart k B hk) (involutionRelation k)
    (inferInstanceAs (IsAffineHom (involutionRelation k).left))

/-- **Stacks 05Z6, the étale presentation, surjectivity half.** The chart `𝐀¹_k ⟶ X` of the
quotient of the affine line by the punctured graph of negation is surjective: it is
representable, and every represented base change of it is a surjective morphism of schemes.

This is the surjectivity conclusion of Stacks 0265 for this example, with the effective-descent
hypothesis discharged by affineness of the relation. -/
theorem presheafSurjective_quotientChart (hchar : (2 : k) ≠ 0) :
    (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of k)) hk)).presheaf (quotientChart k B hk) :=
  have : NeZero (2 : k) := ⟨hchar⟩
  have _hrel : Stacks.Groupoids.IsEtaleEquivalenceRelation
      (R := relationScheme k)
      (U := (Over.post B.inclusion).obj (affineLineChart k B hk))
      (involutionRelation k) := isEtaleEquivalenceRelation k
  Space.presheaf_surjective_quotientChart_of_relativelyRepresentable_diag B (Spec (.of k)) hk
    (affineLineChart k B hk) (involutionRelation k)
    (Space.relativelyRepresentable_diag_quotientSheaf_of_isAffineHom B (Spec (.of k)) hk
      (affineLineChart k B hk) (involutionRelation k)
      (inferInstanceAs (IsAffineHom (involutionRelation k).left)))

/-- **Stacks 05Z6, the étale presentation, étaleness half.** The chart `𝐀¹_k ⟶ X` of the quotient
of the affine line by the punctured graph of negation is étale: it is representable, and every
represented base change of it is an étale morphism of schemes.

Together with `AlgebraicGeometry.AffineLineInvolution.presheafSurjective_quotientChart` this is
the first assertion of the example of Stacks 05Z6, that `𝐀¹_k ⟶ X` is étale surjective. It is
the étaleness conclusion of Stacks 0265 for this example, with the effective-descent hypothesis
discharged by affineness of the relation. -/
theorem presheafEtale_quotientChart (hchar : (2 : k) ≠ 0) :
    (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of k)) hk)).presheaf (quotientChart k B hk) :=
  have : NeZero (2 : k) := ⟨hchar⟩
  have _hrel : Stacks.Groupoids.IsEtaleEquivalenceRelation
      (R := relationScheme k)
      (U := (Over.post B.inclusion).obj (affineLineChart k B hk))
      (involutionRelation k) := isEtaleEquivalenceRelation k
  Space.presheaf_etale_quotientChart_of_relativelyRepresentable_diag B (Spec (.of k)) hk
    (affineLineChart k B hk) (involutionRelation k)
    (Space.relativelyRepresentable_diag_quotientSheaf_of_isAffineHom B (Spec (.of k)) hk
      (affineLineChart k B hk) (involutionRelation k)
      (inferInstanceAs (IsAffineHom (involutionRelation k).left)))

end AlgebraicGeometry.AffineLineInvolution

end
