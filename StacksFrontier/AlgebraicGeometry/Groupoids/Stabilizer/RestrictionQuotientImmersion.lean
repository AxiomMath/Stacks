module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictedQuotientOpenImmersion

/-!
# The quotient of a restriction is an open subsheaf of the quotient

Let `(U, R, s, t, c)` be a groupoid scheme over `S` whose source and target maps are finite
locally free and whose associated pre-relation `j = (t, s)` is an equivalence relation, and let
`g : U' ⟶ U` be an open immersion of schemes over `S`. Then the induced map of fppf quotient
sheaves `U'/R' ⟶ U/R` is representable by open immersions.

This is the step of the proof of Tag 07S6 that follows the restriction step: having restricted
the groupoid to each member of a covering of `U` by `R`-invariant affine opens, the quotients
of the restrictions have to be recognized as open subsheaves of the quotient of `U` before
they can be glued. The source invokes Tag 02WU for this, and the work here is to check that
Tag 02WU's six conditions on the endpoints of the relation follow from the two hypotheses of
Tag 07S6 that bear on them.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.groupoidSource_surjective` and
  `AlgebraicGeometry.groupoidTarget_surjective`: the source and target maps of *any* groupoid
  scheme are surjective, the identity being a section of both.
* `AlgebraicGeometry.groupoidPreRelation_isEquivalenceRelation`: the pre-relation of a groupoid
  scheme whose target and source maps are an equivalence relation is itself one, in the sense
  of its own two projections.
* `AlgebraicGeometry.Space.isOpenImmersion_restrictedQuotientMap_of_groupoid`: the map of fppf
  quotient sheaves induced by restricting the pre-relation of such a groupoid scheme along an
  open immersion is representable by open immersions.

## Implementation notes

Nothing here carries a `@[stacks …]` attribute. Tag 02WU is already formalized as
`AlgebraicGeometry.Space.isOpenImmersion_restrictedQuotientMap`, stated with the six
conditions on the endpoints of the relation that the source's own statement asks for; this
module only discharges those conditions from the hypotheses of Tag 07S6 and does not prove
anything the source records separately.

Surjectivity of the endpoints is not assumed and does not need the equivalence-relation
hypothesis: `Stacks.Groupoids.GroupoidScheme.identity` is a section of both the source and the
target of any groupoid scheme, and a morphism of schemes with a section is surjective on
points. Flatness and local finite presentation come from finite local freeness through Tag
02KB, `Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation`.
Flatness and local finite presentation of `g` are inferred from it being an open immersion.

Both endpoints are assumed finite locally free, as in condition (1) of Tag 07S6, even though
the hypothesis on the target follows from the one on the source through the inverse of the
groupoid, which is an isomorphism on underlying schemes.

Invariance of the image of `g` plays no role here: the statement holds for every open
immersion into the objects. It is the *affineness* of the quotients, supplied by Tag 03BM
through the restriction step, that needs invariance.

The restriction appearing in the conclusion is the restriction of the *pre-relation*, which is
how `Stacks.Groupoids.restrictQuotientSheafMap` and
`Stacks.Groupoids.FiniteFlatQuotient` are phrased. Its comparison with the restriction of the
groupoid is `AlgebraicGeometry.restrictionIso`, with the induced identification of quotient
sheaves `AlgebraicGeometry.groupoidRestrictionQuotientIso`.

## References

* [Stacks Project, Tag 0231](https://stacks.math.columbia.edu/tag/0231)
* [Stacks Project, Tag 0232](https://stacks.math.columbia.edu/tag/0232)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
* [Stacks Project, Tag 02WU](https://stacks.math.columbia.edu/tag/02WU)
* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
* [Stacks Project, Tag 07S6](https://stacks.math.columbia.edu/tag/07S6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids Stacks.Morphisms

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} (G : GroupoidScheme S)

/-! ### The endpoints of a groupoid scheme are surjective -/

/-- A morphism with a section is surjective. -/
private theorem surjective_of_comp_eq_id {X Y : Scheme.{u}} (s : X ⟶ Y) (f : Y ⟶ X)
    (h : s ≫ f = 𝟙 X) : Surjective f := by
  have : Surjective (s ≫ f) := by rw [h]; infer_instance
  exact Surjective.of_comp s f

/-- The source map of a groupoid scheme is surjective: the identity is a section of it. -/
theorem groupoidSource_surjective : Surjective G.source.left :=
  surjective_of_comp_eq_id _ _ (Stacks.Groupoids.identity_left_comp_source_left G)

/-- The target map of a groupoid scheme is surjective: the identity is a section of it. -/
theorem groupoidTarget_surjective : Surjective G.target.left :=
  surjective_of_comp_eq_id _ _ (Stacks.Groupoids.identity_left_comp_target_left G)

/-! ### The pre-relation of a groupoid scheme, as an equivalence relation -/

/-- The two projections of `AlgebraicGeometry.groupoidPreRelation` are the target and the
source maps of the groupoid scheme, so the pre-relation of a groupoid scheme whose target and
source maps are an equivalence relation is an equivalence relation in its own right. -/
theorem groupoidPreRelation_isEquivalenceRelation
    [IsEquivalenceRelation G.target G.source] :
    IsEquivalenceRelation (PreRelation.target (groupoidPreRelation G))
      (PreRelation.source (groupoidPreRelation G)) := by
  rw [show PreRelation.target (groupoidPreRelation G) = G.target from
      prod.lift_fst G.target G.source,
    show PreRelation.source (groupoidPreRelation G) = G.source from
      prod.lift_snd G.target G.source]
  infer_instance

/-! ### Tag 02WU applied to a finite locally free groupoid -/

namespace Space

/-- **The open-subsheaf step of Stacks Project, Tag 07S6.** For a groupoid scheme whose source
and target maps are finite locally free and whose target and source maps are an equivalence
relation, and for an open immersion `g` into its objects, the induced map of fppf quotient
sheaves from the quotient of the restricted pre-relation to the quotient of the pre-relation
is representable by open immersions. -/
theorem isOpenImmersion_restrictedQuotientMap_of_groupoid
    (B : BigFppfSite.{u}) (hS : B.Contains S)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {U' : Over S} (g : U' ⟶ G.objects)
    [IsEquivalenceRelation G.target G.source]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [AlgebraicGeometry.IsOpenImmersion g.left] :
    IsOpenImmersion B S hS
      (restrictQuotientSheafMap (BigFppfOver.topology B S hS)
        (Over.post (X := B.obj hS) B.inclusion) (groupoidPreRelation G) g).hom := by
  have _ := groupoidPreRelation_isEquivalenceRelation G
  have hsrc : PreRelation.source (groupoidPreRelation G) = G.source :=
    prod.lift_snd G.target G.source
  have htgt : PreRelation.target (groupoidPreRelation G) = G.target :=
    prod.lift_fst G.target G.source
  have hS' := (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
    G.source.left).mp inferInstance
  have hT' := (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
    G.target.left).mp inferInstance
  refine isOpenImmersion_restrictedQuotientMap B hS (groupoidPreRelation G) g ?_ ?_ ?_ ?_ ?_ ?_
    inferInstance inferInstance
  · rw [hsrc]; exact groupoidSource_surjective G
  · rw [htgt]; exact groupoidTarget_surjective G
  · rw [hsrc]; exact hS'.2.1
  · rw [htgt]; exact hT'.2.1
  · rw [hsrc]; exact hS'.2.2
  · rw [htgt]; exact hT'.2.2

end Space

end AlgebraicGeometry

end
