module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleAbelian

/-!
# Colimits of abelian sheaves on the small étale site

Abelian sheaves on the small étale site of a scheme `X : Scheme.{u}`, with coefficients in
`AddCommGrpCat.{max (u + 1) v}`, have colimits of every shape that is small in the coefficient
universe. This is `CategoryTheory.Sheaf.instHasColimitsOfShape`, which builds the colimit by
sheafifying a colimit of presheaves, with its two hypotheses supplied by
`AlgebraicGeometry.Scheme.hasSheafify_smallEtaleTopology` and `AddCommGrpCat.hasColimitsOfShape`.

## Main results

* `AlgebraicGeometry.Scheme.hasColimitsOfShape_sheaf_smallEtaleTopology`: colimits of every shape
  small in the coefficient universe.
* `AlgebraicGeometry.Scheme.hasColimit_sheaf_smallEtaleTopology`: the same for a single diagram.
* `AlgebraicGeometry.Scheme.hasCoproducts_sheaf_smallEtaleTopology`: coproducts indexed by a
  `Type u`.

## Implementation notes

Instance search does not find these instances by itself in reasonable time: it enumerates the
many `HasColimit` instances whose index category is a composite or an equivalence, and each
candidate unifies the index category against the small model of `X.Etale`. The conclusions are
therefore stated explicitly, both as `HasColimitsOfShape` and as `HasColimit` of a single
diagram, since providing only the former leaves the `HasColimit` search divergent.

The two results are registered as instances in the scoped namespace
`AlgebraicGeometry.Scheme.SmallEtaleColimits`, at a priority high enough to be tried before the
competing instances. They are not global instances: the coefficient universe `max (u + 1) v` is
not determined by the arguments, so a global instance makes the unifier stick on
`max (u + 1) v =?= u` rather than backtrack. This is the same reason
`AlgebraicGeometry.Scheme.hasSheafify_smallEtaleTopology` and
`AlgebraicGeometry.Scheme.wEqualsLocallyBijective_smallEtaleTopology` carry `priority := low`.
Use `open scoped AlgebraicGeometry.Scheme.SmallEtaleColimits` to make them available.

The smallness hypothesis is `Small.{max (u + 1) v} K` rather than
`HasColimitsOfShape K AddCommGrpCat.{max (u + 1) v}`, which would be one more goal for instance
search to resolve.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w w'

namespace AlgebraicGeometry.Scheme

/-- **Abelian sheaves on the small étale site of `X : Scheme.{u}` with coefficients in
`AddCommGrpCat.{max (u + 1) v}` have colimits of every shape `K` whose objects form a type small
in the coefficient universe.**

Mathlib's `CategoryTheory.Sheaf.instHasColimitsOfShape` with its two hypotheses discharged:
colimits in `AddCommGrpCat.{max (u + 1) v}` of a shape small in that universe, and
sheafification on this site at this coefficient universe. -/
theorem hasColimitsOfShape_sheaf_smallEtaleTopology (X : Scheme.{u}) (K : Type w)
    [Category.{w'} K] [Small.{max (u + 1) v} K] :
    HasColimitsOfShape K (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
  let : HasColimitsOfShape K AddCommGrpCat.{max (u + 1) v} :=
    AddCommGrpCat.hasColimitsOfShape
  Sheaf.instHasColimitsOfShape

/-- **A single diagram of abelian sheaves on the small étale site, of a shape small in the
coefficient universe, has a colimit.**

This is `AlgebraicGeometry.Scheme.hasColimitsOfShape_sheaf_smallEtaleTopology` applied to one
diagram, stated separately so that instance search for `HasColimit` finds it directly. -/
theorem hasColimit_sheaf_smallEtaleTopology (X : Scheme.{u}) {K : Type w} [Category.{w'} K]
    [Small.{max (u + 1) v} K]
    (F : K ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) : HasColimit F :=
  (hasColimitsOfShape_sheaf_smallEtaleTopology.{u, v} X K).has_colimit F

/-- **Abelian sheaves on the small étale site of `X : Scheme.{u}` have coproducts indexed by any
`Type u`.** -/
theorem hasCoproducts_sheaf_smallEtaleTopology (X : Scheme.{u}) :
    HasCoproducts.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
  fun _ => hasColimitsOfShape_sheaf_smallEtaleTopology.{u, v} X _

namespace SmallEtaleColimits

attribute [scoped instance 10000] hasColimitsOfShape_sheaf_smallEtaleTopology
  hasColimit_sheaf_smallEtaleTopology

end SmallEtaleColimits

end AlgebraicGeometry.Scheme

end
