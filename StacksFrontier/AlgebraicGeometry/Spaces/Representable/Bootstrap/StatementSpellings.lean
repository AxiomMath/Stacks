module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSheafSpaceCoverCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleTopologyBootstrap
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.OpenRelationEtaleQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.SeparatedQuasiFiniteDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatPresentationRepresentableDiagonal

/-!
# Equivalent forms of the bootstrap theorem Stacks 04S6

Stacks 04S6, Theorem 80.10.1 of the source's Bootstrap chapter, is stated in this library in
several forms. This module proves that some of them are the same statement.

*The flat-surjection form*: a sheaf receiving a morphism from an algebraic space that is
representable by algebraic spaces, surjective, flat and locally of finite presentation is an
algebraic space. It is stated as
`AlgebraicGeometry.Space.IsBootstrapAlgebraicSpaceAlongFlatSurjection` and as
`AlgebraicGeometry.Stack.Bootstrap04S6Spaces`.

*The quotient form*: the quotient sheaf of a flat, locally finitely presented equivalence
relation of algebraic spaces is an algebraic space. It is stated as
`AlgebraicGeometry.Space.Bootstrap04S6QuotientSheaf`, for a pre-relation, and as
`AlgebraicGeometry.Space.Theorem04S6Quotient`, for a groupoid in algebraic spaces.

The étale topology on the slice category `Sch_α/S` is written both as
`(AlgebraicGeometry.etaleTopology B).over (B.obj hS)` and as
`AlgebraicGeometry.BigEtaleOver.topology (AlgebraicGeometry.associatedBigEtaleSite B) S hS`.
These are not definitionally equal, but they are equal.

## Main results

* `AlgebraicGeometry.etaleTopology_eq_associatedBigEtaleSite_topology` and
  `AlgebraicGeometry.etaleTopology_over_eq_bigEtaleOverTopology`: the étale topology chosen
  inside a big fppf site is the topology of the associated big étale site, and likewise after
  localizing at `S`.
* `AlgebraicGeometry.Space.bootstrap04S6Spaces_iff`: the two statements of the flat-surjection
  form are the same statement.
* `AlgebraicGeometry.Space.theorem04S6Quotient_of_bootstrap04S6QuotientSheaf`: the
  pre-relation statement of the quotient form implies the groupoid statement.

## References

* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 03FF](https://stacks.math.columbia.edu/tag/03FF)
-/

@[expose] public section

open CategoryTheory Stacks.Groupoids

namespace AlgebraicGeometry

universe u

/-! ### The two forms of the étale topology on the common category -/

/-- **The étale topology chosen inside a big fppf site is the topology of the associated big
étale site.** -/
theorem etaleTopology_eq_associatedBigEtaleSite_topology (B : BigFppfSite.{u}) :
    etaleTopology B = (associatedBigEtaleSite B).topology := by
  refine le_antisymm ?_ ?_ <;>
    refine Precoverage.toGrothendieck_mono fun X R ⟨E, hR, hE⟩ => ⟨E, hR, ?_⟩ <;>
    have h := etaleBounded_eq_fppfEtaleBounded B ⟨X, E⟩
  · exact h.mp hE
  · exact h.mpr hE

/-- **The two forms of the big étale topology over `S` agree.**

The localization at `S` of the étale topology chosen inside a big fppf site equals the topology
`AlgebraicGeometry.BigEtaleOver.topology` of the slice over `S` of the associated big étale
site. -/
theorem etaleTopology_over_eq_bigEtaleOverTopology (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    (etaleTopology B).over (B.obj hS) =
      BigEtaleOver.topology (associatedBigEtaleSite B) S hS := by
  rw [bigEtaleOver_topology_eq, etaleTopology_eq_associatedBigEtaleSite_topology]
  rfl

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The two statements of the flat-surjection form of Stacks 04S6 part (3) are the same.**

`AlgebraicGeometry.Stack.Bootstrap04S6Spaces` and
`AlgebraicGeometry.Space.IsBootstrapAlgebraicSpaceAlongFlatSurjection` differ only in the order
of their two implicit object binders: the properties of the morphism are
`AlgebraicGeometry.Space.flatProperty` and
`AlgebraicGeometry.Space.locallyOfFinitePresentationProperty` on one side and their definitional
unfoldings on the other. -/
theorem bootstrap04S6Spaces_iff :
    Stack.Bootstrap04S6Spaces B S hS ↔
      IsBootstrapAlgebraicSpaceAlongFlatSurjection B S hS := by
  constructor
  · intro h X Y f hY hX hf hsurj hflat hlfp
    exact h f hY hX hf hsurj hflat hlfp
  · intro h F G g hF hG hg hsurj hflat hlfp
    exact h g hF hG hg hsurj hflat hlfp

/-- **The groupoid form of the quotient statement of Stacks 04S6 follows from the pre-relation
form.**

`AlgebraicGeometry.Space.Theorem04S6Quotient` asks for the quotient of a groupoid in algebraic
spaces to be an algebraic space, and `AlgebraicGeometry.Space.Bootstrap04S6QuotientSheaf` asks
the same of the quotient of a pre-relation. A groupoid cuts out the pre-relation
`AlgebraicGeometry.Space.groupoidPreRelation`, whose arrow and object presheaves are algebraic
spaces and whose source and target maps are those of the groupoid. -/
theorem theorem04S6Quotient_of_bootstrap04S6QuotientSheaf
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (h : Bootstrap04S6QuotientSheaf B S hS) : Theorem04S6Quotient B S hS := by
  intro Y G hrel hsource htarget hsourceLfp htargetLfp
  rw [← Stack.groupoidPreRelation_target_left G] at htarget htargetLfp
  rw [← Stack.groupoidPreRelation_source_left G] at hsource hsourceLfp
  exact h (groupoidPreRelation G) G.arrows.property G.objects.property hrel htarget htargetLfp
    hsource hsourceLfp

end Space

end AlgebraicGeometry

end
