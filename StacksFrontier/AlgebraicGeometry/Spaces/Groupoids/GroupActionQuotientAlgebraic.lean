module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAlgebraicGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional

/-!
# Stacks 02Z2, the algebraic-space conclusion

Let an abstract group `G` act on an object `V` of a big fppf site of `S` by automorphisms of
`S`-schemes, subject to the condition `(*)` of Stacks 02Z2 that no nonidentity element fix a
point and act trivially on its residue field.
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActionRelation` builds the graph relation
`R = ∐_{g ∈ G} V` of such an action, proves it is an étale equivalence relation, and proves
that its scheme of arrows again satisfies the size cutoff of the site, so that the relation is
a relation *inside* the site.

Stacks 02Z2 then concludes, by Stacks 02WW, that the quotient `V/R` is an algebraic space.
`AlgebraicGeometry.Space.isAlgebraicSpace_actionQuotient` draws that conclusion from the form
of 02WW that still carries an effective-descent hypothesis. This file states it with the
hypothesis discharged, which is the conclusion of the tag.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_actionQuotient_unconditional`: **Stacks 02Z2.**
  The quotient `V/R` of an object of the big fppf site of `S` by a group action satisfying
  `(*)` is an algebraic space over `S`.

## Implementation notes

Every input is discharged rather than assumed. That the graph relation is an étale equivalence
relation is `AlgebraicGeometry.Space.actionRelation_isEtaleEquivalenceRelation`; that its
scheme of arrows lies in the site — needed before the relation can be read as a pair of
morphisms of the site at all — is `AlgebraicGeometry.Space.contains_actionRelationScheme`; and
the effective-descent hypothesis of Stacks 02WW is
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft`, exactly
the substitution made in
`StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional`.

The surviving `HasSheafify (BigFppfOver.topology B S hS) (Type u)` assumption is not an open
mathematical assumption but the choice of universe in which the quotient presheaf is
sheafified; it is already part of the statement of
`AlgebraicGeometry.Space.actionQuotient`.

## References

* [Stacks Project, Tag 02Z2](https://stacks.math.columbia.edu/tag/02Z2)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u v

namespace AlgebraicGeometry.Space

/-- **Stacks 02Z2.** Let a group `G` act on an object `V` of the big fppf site of `S` so that
no nonidentity element fixes a point of `V` and acts trivially on its residue field. Then the
quotient `V/R` of `V` by the graph relation `R = ∐_{g ∈ G} V` of the action is an algebraic
space over `S`.

This is `AlgebraicGeometry.Space.isAlgebraicSpace_actionQuotient` with its descent hypothesis
discharged by
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft`. -/
@[stacks 02Z2 "the quotient is an algebraic space"]
theorem isAlgebraicSpace_actionQuotient_unconditional {S : Scheme.{u}} (G : Type v) [Group G]
    [Small.{u} G] (B : BigFppfSite.{u}) (hS : B.Contains S) (V : BigFppfOver B S hS)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (a : G →* Aut (underlyingOver B hS V))
    (ha : ActsNontriviallyOnFixedResidueFields (underlyingOver B hS V) G a) :
    IsAlgebraicSpace B S hS (actionQuotient G B hS V a) :=
  isAlgebraicSpace_actionQuotient G B hS V a ha
    (isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft B S hS)

end AlgebraicGeometry.Space

end
