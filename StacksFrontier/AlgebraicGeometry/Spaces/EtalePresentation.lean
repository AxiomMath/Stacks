module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.EquivalenceRelations

/-!
# Presentations of algebraic spaces (Stacks 0263)

A *presentation* of an algebraic space `F` over `S` consists of a scheme `U` over `S`, an étale
equivalence relation `R` on `U`, and a surjective étale morphism from `U` to `F` whose kernel
pair is `R`.

## Main definitions

* `AlgebraicGeometry.Space.Presentation`: **Stacks 0263**, a presentation of an algebraic
  space.

## Main results

There are no results beyond the definition; its fields are the étale equivalence relation, the
surjective étale atlas, and the kernel-pair identification.

## Implementation notes

The schemes `U` and `R` are objects of the chosen big fppf site over `S`, so that their
represented presheaves can map to `F`. Their structure morphisms to `S` are transported to
schemes by the site's inclusion when asserting that the two projections form an étale
equivalence relation in the sense of Tag 02WS. Surjectivity and étaleness of the atlas are the
relatively representable forms of Tag 02YU, as elsewhere for charts. The equality `R = U ×_F U`
is recorded as the canonical pullback square of represented presheaves, so that clients can use
the `IsPullback` field directly.

## References

* [Stacks Project, Tag 0263](https://stacks.math.columbia.edu/tag/0263)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 0263.** An étale presentation of an algebraic space by a scheme over `S` together
with an étale equivalence relation on it. -/
@[stacks 0263]
structure Presentation (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hF : IsAlgebraicSpace B S hS F) where
  /-- The presenting scheme over `S`. -/
  U : BigFppfOver B S hS
  /-- The scheme of relations over `S`. -/
  R : BigFppfOver B S hS
  /-- The target projection of the relation. -/
  target : R ⟶ U
  /-- The source projection of the relation. -/
  source : R ⟶ U
  /-- The two projections make `R` an étale equivalence relation on `U` over `S`. -/
  isEtaleEquivalenceRelation : Stacks.Groupoids.IsEtaleEquivalenceRelation
    (prod.lift ((Over.post B.inclusion).map target) ((Over.post B.inclusion).map source))
  /-- The atlas morphism from `U` to the algebraic space. -/
  toSpace : yoneda.obj U ⟶ F
  /-- The atlas is surjective after every representable base change. -/
  surjective : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) toSpace
  /-- The atlas is étale after every representable base change. -/
  etale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) toSpace
  /-- The relation is the fibre product `U ×_F U`. -/
  isPullback : IsPullback (yoneda.map target) (yoneda.map source) toSpace toSpace

end AlgebraicGeometry.Space

end
