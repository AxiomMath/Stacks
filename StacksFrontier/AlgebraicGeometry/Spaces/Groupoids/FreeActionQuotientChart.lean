module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FiniteFreeActionSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SurjectivePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleLocalization
public import StacksFrontier.CategoryTheory.Sites.TorsorObjectCriterion

/-!
# The chart of the quotient by a free action, inside the spaces-étale site of the quotient

Let a group `G` act freely on an object `V` of a big fppf site over a scheme `S`. The quotient
`V/G` is an algebraic space over `S` ([Stacks, Tag 071S], proved as
`AlgebraicGeometry.Space.isAlgebraicSpace_actionQuotient_of_actsFreelyOnNonemptyPoints`), and
the chart `h_V ⟶ V/G` is defined as
`AlgebraicGeometry.Space.freeActionQuotientMap`, a morphism of presheaves on the big fppf site.

The results about that chart which are in the library — that its kernel pair is the disjoint union of
one copy of `V` per group element, and that it is finite locally free and surjective — are all
stated in that presheaf spelling, as properties holding after every representable base change.
This file moves the chart into the *spaces-étale site of the quotient*, which is the site on
which [Stacks, Tag 0727] speaks: it reads the two properties of the chart that the small site
needs, étaleness and surjectivity on points, in the spellings
`AlgebraicGeometry.Space.IsEtale` and `Function.Surjective ∘ pointsMap`, and exhibits the chart
as an object of `AlgebraicGeometry.Space.SpacesEtale` over the quotient.

## Main definitions

* `AlgebraicGeometry.Space.actionQuotientSpace` is the quotient `V/G`, as an algebraic space
  over `S` rather than as a presheaf.
* `AlgebraicGeometry.Space.freeActionQuotientChart` is the chart `h_V ⟶ V/G`, as an object of
  the spaces-étale site of `V/G`.

## Main results

* `AlgebraicGeometry.Space.isEtale_freeActionQuotientChart`: the chart is étale as a morphism
  of algebraic spaces, which is what makes it an object of the small site of the quotient.
* `AlgebraicGeometry.Space.surjective_pointsMap_freeActionQuotientMap`: the chart is surjective
  on the points of [Stacks, Tag 03BU], which is the covering condition of the spaces-étale
  site.
* `AlgebraicGeometry.Space.splittingSieve_mem_freeActionQuotientChart`: **the chart covers every
  object of the spaces-étale site of the quotient**, which is the first of the three conditions
  of `CategoryTheory.IsTorsorObject` for the chart over the quotient.

## Implementation notes

Both translations are applications of existing bridges, and neither needs a new geometric input.
Étaleness goes through `AlgebraicGeometry.Space.isEtale_iff_presheaf_of_yoneda`, which says
that for a morphism out of a representable the two notions agree, applied to
`AlgebraicGeometry.Space.quotientMap_etale_unconditional` ([Stacks, Tag 02WW]) — available
because the chart is by definition the quotient map of the graph relation of the action, and
that relation is an étale equivalence relation by
`AlgebraicGeometry.Space.isEtaleEquivalenceRelation_relation_of_actsFreely`. Surjectivity on
points goes through `AlgebraicGeometry.Space.surjective_pointsMap_of_presheaf_surjective`
applied to `AlgebraicGeometry.Space.surjective_presheaf_freeActionQuotientMap`.

The first condition of the torsor predicate needs nothing further: it is the base change of the
chart along the object in question, which is an object of the site because étaleness is stable
under base change, together with the lifting of points through a fibre product
(`AlgebraicGeometry.Space.exists_point_of_isPullback`) out of surjectivity on points. The
covering sieves are read through
`AlgebraicGeometry.Space.SpacesEtale.mem_topology_iff_sievePointwiseCover`, so the splitting
sieve is shown covering directly rather than through a one-member family refining it.

What this does *not* supply is the action of `G` on the chart read inside the small site, nor
the kernel-pair square there, which the other two conditions need:
`AlgebraicGeometry.Space.isPullback_freeActionQuotientMap` is a pullback of presheaves on the
big fppf site, and the covering sieves of the spaces-étale site of the quotient are a different
topology on a different category.

## References

* [Stacks Project, Tag 071S](https://stacks.math.columbia.edu/tag/071S)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 0727](https://stacks.math.columbia.edu/tag/0727)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (G : Type v) [Group G] [Small.{u} G] (B : BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S) [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
  (V : BigFppfOver B S hS) (a : G →* Aut (underlyingOver B hS V))
  (ha : ActsFreelyOnNonemptyPoints (underlyingOver B hS V) G a)

/-- **The chart of the quotient by a free action is étale.** The chart is the quotient map of
the graph relation of the action, which is an étale equivalence relation, so the chart is étale
after every representable base change by [Stacks, Tag 02WW]; for a morphism out of a
representable that is étaleness as a morphism of algebraic spaces. -/
theorem isEtale_freeActionQuotientMap :
    IsEtale B S hS (freeActionQuotientMap G B S hS V a ha) :=
  have _ := isEtaleEquivalenceRelation_relation_of_actsFreely G B S hS V a ha
  (isEtale_iff_presheaf_of_yoneda B S hS _).2 (quotientMap_etale_unconditional B S hS _ _)

/-- **The chart of the quotient by a free action is surjective on points.** It is surjective
after every representable base change, and surjectivity after every representable base change
of a morphism out of a representable is surjectivity on the points of [Stacks, Tag 03BU]. -/
theorem surjective_pointsMap_freeActionQuotientMap :
    Function.Surjective
      (pointsMap B S hS (yoneda.obj V) (freeActionQuotientMap G B S hS V a ha)) :=
  surjective_pointsMap_of_presheaf_surjective B S hS _
    (surjective_presheaf_freeActionQuotientMap G B S hS V a ha)

/-- The quotient `V/G` of a free action of a group on an object of a big fppf site over `S`, as
an algebraic space over `S`. -/
def actionQuotientSpace : AlgebraicSpaces B S hS :=
  ⟨actionQuotient G B hS V a,
    isAlgebraicSpace_actionQuotient_of_actsFreelyOnNonemptyPoints G B hS V a ha⟩

/-- The object `V`, as an algebraic space over `S`. -/
def siteObjectSpace : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩

/-- The chart `h_V ⟶ V/G` of the quotient by a free action, as a morphism of algebraic spaces
over `S`. -/
def freeActionQuotientSpaceMap :
    siteObjectSpace B S hS V ⟶ actionQuotientSpace G B S hS V a ha :=
  ObjectProperty.homMk (freeActionQuotientMap G B S hS V a ha)

/-- **The chart `h_V ⟶ V/G`, as an object of the spaces-étale site of the quotient.** This is
the shape [Stacks, Tag 0727] asks of the object it calls a torsor: an algebraic space étale
over the quotient. -/
def freeActionQuotientChart : SpacesEtale B S hS (actionQuotientSpace G B S hS V a ha) :=
  ⟨Over.mk (freeActionQuotientSpaceMap G B S hS V a ha),
    isEtale_freeActionQuotientMap G B S hS V a ha⟩

/-- The structure morphism of `freeActionQuotientChart` to the quotient, as a morphism of
presheaves, is `freeActionQuotientMap`. -/
@[simp]
theorem freeActionQuotientChart_hom :
    ((freeActionQuotientChart G B S hS V a ha).1.hom).hom =
      freeActionQuotientMap G B S hS V a ha :=
  rfl

/-- **The chart of the quotient by a free action is étale**, in the form that exhibits it as an
object of the spaces-étale site of the quotient. -/
theorem isEtale_freeActionQuotientChart :
    IsEtaleOver B S hS (actionQuotientSpace G B S hS V a ha)
      (freeActionQuotientChart G B S hS V a ha).1 :=
  (freeActionQuotientChart G B S hS V a ha).2

variable (A : SpacesEtale B S hS (actionQuotientSpace G B S hS V a ha))

/-- The fibre product `A ×_{V/G} h_V` of an object of the spaces-étale site of the quotient
with the chart. -/
def freeActionChartBaseChange : AlgebraicSpaces B S hS :=
  AlgebraicSpaces.fiberProduct B S hS (freeActionQuotientChart G B S hS V a ha).1.hom A.1.hom

/-- The projection of `A ×_{V/G} h_V` to the chart. -/
def freeActionChartBaseChangeFst :
    freeActionChartBaseChange G B S hS V a ha A ⟶
      (freeActionQuotientChart G B S hS V a ha).1.left :=
  ObjectProperty.homMk
    (Limits.pullback.fst (freeActionQuotientChart G B S hS V a ha).1.hom.hom A.1.hom.hom)

/-- The projection of `A ×_{V/G} h_V` to `A`. -/
def freeActionChartBaseChangeSnd : freeActionChartBaseChange G B S hS V a ha A ⟶ A.1.left :=
  ObjectProperty.homMk
    (Limits.pullback.snd (freeActionQuotientChart G B S hS V a ha).1.hom.hom A.1.hom.hom)

/-- `A ×_{V/G} h_V` is the fibre product of `A` and the chart over the quotient. -/
theorem isPullback_freeActionChartBaseChange :
    IsPullback (freeActionChartBaseChangeFst G B S hS V a ha A)
      (freeActionChartBaseChangeSnd G B S hS V a ha A)
      (freeActionQuotientChart G B S hS V a ha).1.hom A.1.hom :=
  AlgebraicSpaces.isPullback_fiberProduct B S hS _ _

/-- The base change of the chart along an object of the spaces-étale site of the quotient, as
an object of that site: a fibre product of algebraic spaces, étale over the quotient because
the chart is. -/
def freeActionQuotientChartPullback :
    SpacesEtale B S hS (actionQuotientSpace G B S hS V a ha) :=
  ⟨Over.mk (freeActionChartBaseChangeSnd G B S hS V a ha A ≫ A.1.hom), by
    refine isEtale_comp B S hS ?_ A.2
    exact isEtale_of_isPullback B S hS _ _ _ _
      (isPullback_freeActionChartBaseChange G B S hS V a ha A)
      (freeActionQuotientChart G B S hS V a ha).2⟩

/-- **The chart covers every object of the spaces-étale site of the quotient**: this is the
first of the three conditions of `CategoryTheory.IsTorsorObject` for the chart, over the
quotient.

A point of an object `A` étale over the quotient has an image in the quotient, which lifts to a
point of the chart because the chart is surjective on points; the two points then lift to a
point of the fibre product `A ×_{V/G} h_V`, which is an object of the site mapping to `A` and
to the chart. -/
theorem splittingSieve_mem_freeActionQuotientChart :
    splittingSieve (freeActionQuotientChart G B S hS V a ha) A ∈
      SpacesEtale.topology B S hS (actionQuotientSpace G B S hS V a ha) A := by
  classical
  rw [SpacesEtale.mem_topology_iff_sievePointwiseCover]
  intro x
  obtain ⟨y, hy⟩ := surjective_pointsMap_freeActionQuotientMap G B S hS V a ha
    (pointsMap B S hS A.1.left.1 A.1.hom.hom x)
  obtain ⟨w, -, hw⟩ :=
    exists_point_of_isPullback B S hS
      (isPullback_freeActionChartBaseChange G B S hS V a ha A) y x hy
  refine ⟨freeActionQuotientChartPullback G B S hS V a ha A,
    ObjectProperty.homMk (Over.homMk (freeActionChartBaseChangeSnd G B S hS V a ha A) rfl),
    ⟨ObjectProperty.homMk (Over.homMk (freeActionChartBaseChangeFst G B S hS V a ha A)
      (isPullback_freeActionChartBaseChange G B S hS V a ha A).w)⟩,
    w, hw⟩

end AlgebraicGeometry.Space

end
