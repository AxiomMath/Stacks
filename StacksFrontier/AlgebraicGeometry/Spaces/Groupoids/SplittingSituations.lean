module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs

/-!
# Standing hypotheses for the étale localization of a groupoid scheme

Étale localization of a groupoid scheme at a point of its object scheme proceeds under one
of three standing sets of hypotheses.  In all three the source and target of the groupoid
are separated and locally of finite type; they differ in what is required of the
stabilizer of the chosen point and of the source map along it.  The *quasi-splitting*
hypotheses ask only that the source be quasi-finite at the identity arrow of the point; the
*strong splitting* hypotheses ask that the set of arrows from the point to itself be finite
and that the source be quasi-finite at each of them; the *splitting* hypotheses ask the
same of the scheme-theoretic stabilizer.

## Main definitions

* `AlgebraicGeometry.Space.QuasiSplittingSituation` bundles the quasi-splitting hypotheses.
* `AlgebraicGeometry.Space.StrongSplittingSituation` bundles the strong splitting
  hypotheses.
* `AlgebraicGeometry.Space.SplittingSituation` bundles the splitting hypotheses.

## Implementation notes

The structural maps of a `Stacks.Groupoids.GroupoidScheme` are morphisms in a category of
schemes over the base, so the geometric hypotheses are imposed on their underlying scheme
morphisms.  Quasi-finiteness at a point is `AlgebraicGeometry.quasiFiniteAt`, which already
includes the local finite-type condition at that point.  The separatedness and local
finite-type hypotheses are instance-implicit fields and are registered as instances, so
they are found by typeclass synthesis once such a situation is destructured.

The three situations record the stabilizer in the two inequivalent ways the source uses.
`AlgebraicGeometry.Space.StrongSplittingSituation` uses the set of points of the arrow
scheme whose source and target are both the chosen point, while
`AlgebraicGeometry.Space.SplittingSituation` uses the fibre over the chosen point of the
stabilizer group scheme `AlgebraicGeometry.stabilizer`, whose points are recorded through
its structure map and transported to arrows by `AlgebraicGeometry.stabilizerArrow`.

## References

* [Stacks Project, Tag 04RL](https://stacks.math.columbia.edu/tag/04RL)
* [Stacks Project, Tag 04RV](https://stacks.math.columbia.edu/tag/04RV)
* [Stacks Project, Tag 0DTB](https://stacks.math.columbia.edu/tag/0DTB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Stacks.Groupoids

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks Project, Tag 04RV.** The standing quasi-splitting situation: a point `u` of
the object scheme of a groupoid scheme whose source and target are separated and locally of
finite type, with the source quasi-finite at the identity arrow `e(u)`. -/
@[stacks 04RV]
structure QuasiSplittingSituation where
  /-- The base scheme. -/
  S : Scheme.{u}
  /-- The groupoid scheme `(U, R, s, t, c, e, i)` over `S`. -/
  groupoid : GroupoidScheme S
  /-- The chosen point `u` of the object scheme `U`. -/
  u : groupoid.objects.left
  /-- The source map `s : R ⟶ U` is separated. -/
  [sourceSeparated : IsSeparated groupoid.source.left]
  /-- The target map `t : R ⟶ U` is separated. -/
  [targetSeparated : IsSeparated groupoid.target.left]
  /-- The source map `s : R ⟶ U` is locally of finite type. -/
  [sourceLocallyOfFiniteType : LocallyOfFiniteType groupoid.source.left]
  /-- The target map `t : R ⟶ U` is locally of finite type. -/
  [targetLocallyOfFiniteType : LocallyOfFiniteType groupoid.target.left]
  /-- The source map is quasi-finite at the identity arrow `e(u)`. -/
  sourceQuasiFiniteAtIdentity :
    quasiFiniteAt groupoid.source.left (groupoid.identity.left u)

attribute [instance] QuasiSplittingSituation.sourceSeparated
  QuasiSplittingSituation.targetSeparated
  QuasiSplittingSituation.sourceLocallyOfFiniteType
  QuasiSplittingSituation.targetLocallyOfFiniteType

/-- **Stacks Project, Tag 04RL.** The standing strong splitting situation for a groupoid
scheme: a chosen object with finite stabilizer, at whose stabilizer points the source is
quasi-finite. -/
@[stacks 04RL]
structure StrongSplittingSituation where
  /-- The base scheme. -/
  S : Scheme.{u}
  /-- The groupoid scheme `(U, R, s, t, c)` over `S`. -/
  groupoid : GroupoidScheme S
  /-- The chosen point `u` of the object scheme. -/
  u : groupoid.objects.left
  /-- The source map is separated. -/
  [sourceSeparated : IsSeparated groupoid.source.left]
  /-- The target map is separated. -/
  [targetSeparated : IsSeparated groupoid.target.left]
  /-- The source map is locally of finite type. -/
  [sourceLocallyOfFiniteType : LocallyOfFiniteType groupoid.source.left]
  /-- The target map is locally of finite type. -/
  [targetLocallyOfFiniteType : LocallyOfFiniteType groupoid.target.left]
  /-- The stabilizer of `u` is finite as a set of points of the arrow scheme. -/
  stabilizer_finite : Set.Finite {r : groupoid.arrows.left |
    groupoid.source.left r = u ∧ groupoid.target.left r = u}
  /-- The source is quasi-finite at each point of the stabilizer of `u`. -/
  source_quasiFiniteAt : ∀ r : groupoid.arrows.left,
    (groupoid.source.left r = u ∧ groupoid.target.left r = u) →
      quasiFiniteAt groupoid.source.left r

attribute [instance] StrongSplittingSituation.sourceSeparated
  StrongSplittingSituation.targetSeparated
  StrongSplittingSituation.sourceLocallyOfFiniteType
  StrongSplittingSituation.targetLocallyOfFiniteType

/-- **Stacks Project, Tag 0DTB.** The standing splitting situation for a groupoid scheme at
a point of its object scheme. -/
@[stacks 0DTB]
structure SplittingSituation where
  /-- The base scheme. -/
  S : Scheme.{u}
  /-- The groupoid scheme over the base. -/
  groupoid : GroupoidScheme S
  /-- The chosen point of the object scheme. -/
  u : groupoid.objects.left
  /-- The source morphism is separated. -/
  [sourceSeparated : IsSeparated groupoid.source.left]
  /-- The target morphism is separated. -/
  [targetSeparated : IsSeparated groupoid.target.left]
  /-- The source morphism is locally of finite type. -/
  [sourceLocallyOfFiniteType : LocallyOfFiniteType groupoid.source.left]
  /-- The target morphism is locally of finite type. -/
  [targetLocallyOfFiniteType : LocallyOfFiniteType groupoid.target.left]
  /-- Only finitely many points of the stabilizer lie over the chosen point. -/
  stabilizer_finite :
    Set.Finite {g : (stabilizer groupoid).left | (stabilizer groupoid).hom g = u}
  /-- The source is quasi-finite at each corresponding arrow point. -/
  source_quasiFiniteAt : ∀ g : (stabilizer groupoid).left,
    (stabilizer groupoid).hom g = u →
      quasiFiniteAt groupoid.source.left (stabilizerArrow groupoid g)

attribute [instance] SplittingSituation.sourceSeparated
  SplittingSituation.targetSeparated
  SplittingSituation.sourceLocallyOfFiniteType
  SplittingSituation.targetLocallyOfFiniteType

end AlgebraicGeometry.Space

end
