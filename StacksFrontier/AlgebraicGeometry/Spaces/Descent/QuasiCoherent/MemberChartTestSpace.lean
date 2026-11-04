module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.DatumChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure

/-!
# The chart of a member of a family as a test space for a descent datum

Let `X` be an algebraic space over a scheme `S` and let `(f i : Y i ⟶ X)` be a family of
algebraic spaces étale over `X`.  The charts of the members of that family form a site,
`AlgebraicGeometry.Space.QuasiCoherentDescent.MemberSite`: its objects are the pairs `(i, V)` of
a member and a chart of it, and its morphisms are the morphisms of the induced charts of `X`.

A descent datum relative to the family reads its transition on the sections over a chart of a
*test space* mapping compatibly to two members,
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionSect`.  To read it at a morphism
`k : (j, V') ⟶ (i, V)` of the site of the charts of the members one needs a test space built out
of `k`, and this file supplies it: the algebraic space `chartSpace` represented by the chart `V'`,
with its structure morphism to `Y j` and with the composite of `k` with the structure morphism of
`V` to `Y i`.  Both are étale, their composites to `X` agree, and the identity chart of that
space induces `V'` on the nose, so the reading of the transition over it lands on the sections of
`D.F j` over `V'` with nothing to transport.

All names below are in the namespace `AlgebraicGeometry.Space.QuasiCoherentDescent`.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberChartMap` is the morphism from the chart
  space of the source chart of a morphism of the site of the charts of the members to the target
  member, and `.memberChartPair` is the induced morphism to the pairwise fibre product.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.smallEtalePostcomp_chartToSpace_idEtaleChart`:
  **postcomposing the identity chart of the chart space of `V` with the structure morphism of `V`
  gives `V` back**, on the nose.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.chartSpace_smallEtalePostcomp`: the chart space
  of a chart is unchanged when the chart is pushed along an étale morphism.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.isEtale_memberChartMap` and
  `.memberChartMap_comp`: the morphism to the target member is étale, and its composite to `X` is
  the composite of the structure morphism of the source chart.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberChartPair_fst` and `.memberChartPair_snd`:
  the two projections of the induced morphism to the pairwise fibre product.

## Implementation notes

The two chart spaces that a morphism of the site of the charts of the members relates are those
of the *induced charts of `X`*, while the two structure morphisms available are those of the
charts of the members; the two descriptions are the same algebraic space on the nose, by
`.chartSpace_smallEtalePostcomp`, and the identification is performed in the position of the
source and the target of a morphism, where it is free.  That it is free is not automatic — the
same identification asked for inside the type of a morphism of *modules* does not terminate, as
the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/DatumChartBaseChange.lean` record —
so no statement below is phrased with the chart space of an induced chart of `X`.

The canonical morphism of charts of `X` from a chart `A` of the chart space of `V`, read as a
chart of `X`, to `V` itself is `((SmallEtale.chartLocalization B S hS X.1 V).obj A).hom`:
`AlgebraicGeometry.Space.SmallEtale.chartLocalization` read on an object, the equivalence of
Stacks 04M0 between the charts of the chart space of `V` and the charts of `X` over `V` sending a
chart to exactly the induced chart of `X` together with its morphism to `V`, by
`AlgebraicGeometry.Space.chartLocalization_comp_forget`.  It is written out where it is used
rather than named, `AlgebraicGeometry.Space.chartHomOver` of
`StacksFrontier/AlgebraicGeometry/Spaces/IdealPowerSupport.lean` being that morphism already.

No `@[stacks]` attribute is carried: nothing below is an assertion of a numbered result.

## References

* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The chart space of a chart -/

/-- **Postcomposing the identity chart of the chart space of a chart `V` with the structure
morphism of `V` gives `V` back.**  Postcomposition of charts composes the structure morphisms, and
the structure morphism of the identity chart is the identity. -/
theorem smallEtalePostcomp_chartToSpace_idEtaleChart (X : AlgebraicSpaces B S hS)
    (V : SmallEtale B S hS X.1) :
    (smallEtalePostcomp B S hS (chartToSpace B S hS X V)
        (isEtale_chartToSpace B S hS X V)).obj
      (idEtaleChart B S hS ((SmallEtale.toOver B S hS X.1).obj V)) = V :=
  rfl

/-- The chart space of a chart is unchanged when the chart is pushed along an étale morphism:
postcomposition leaves the underlying object of the big fppf site alone. -/
theorem chartSpace_smallEtalePostcomp {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X)
    (hg : IsEtale B S hS g.hom) (V : SmallEtale B S hS Y.1) :
    chartSpace B S hS X ((smallEtalePostcomp B S hS g hg).obj V) = chartSpace B S hS Y V :=
  rfl

/-! ### The test space attached to a morphism of the charts of the members -/

variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)

/-- The morphism from the chart space of the source chart of a morphism of the site of the charts
of the members to the target member: the morphism of chart spaces that the morphism of charts of
`X` represents, followed by the structure morphism of the target chart. -/
def memberChartMap {i j : I} (V : SmallEtale B S hS (Yi i).1)
    (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f j) (hf j)).obj V' ⟶
      (smallEtalePostcomp B S hS (f i) (hf i)).obj V) :
    chartSpace B S hS (Yi j) V' ⟶ Yi i :=
  chartMap B S hS X k ≫ chartToSpace B S hS (Yi i) V

/-- The morphism to the target member of a morphism of the charts of the members is étale: it is
a morphism of chart spaces of `X`, which is étale by cancellation, followed by the structure
morphism of a chart. -/
theorem isEtale_memberChartMap {i j : I} (V : SmallEtale B S hS (Yi i).1)
    (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f j) (hf j)).obj V' ⟶
      (smallEtalePostcomp B S hS (f i) (hf i)).obj V) :
    IsEtale B S hS (memberChartMap B S hS Yi f hf V V' k).hom :=
  isEtale_comp B S hS (isEtale_chartMap B S hS X k) (isEtale_chartToSpace B S hS (Yi i) V)

/-- **The two morphisms out of the chart space of the source chart have equal composites to
`X`.**  Both are the structure morphism of the induced chart of `X` of the source: that is the
commuting triangle over `X` of the morphism of charts. -/
theorem memberChartMap_comp {i j : I} (V : SmallEtale B S hS (Yi i).1)
    (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f j) (hf j)).obj V' ⟶
      (smallEtalePostcomp B S hS (f i) (hf i)).obj V) :
    memberChartMap B S hS Yi f hf V V' k ≫ f i =
      chartToSpace B S hS (Yi j) V' ≫ f j :=
  chartMap_comp_chartToSpace B S hS X k

/-- The morphism from the chart space of the source chart of a morphism of the site of the charts
of the members to the pairwise fibre product `Y i ×_X Y j`, whose two projections are the
morphism to the target member and the structure morphism of the source chart. -/
def memberChartPair {i j : I} (V : SmallEtale B S hS (Yi i).1)
    (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f j) (hf j)).obj V' ⟶
      (smallEtalePostcomp B S hS (f i) (hf i)).obj V) :
    chartSpace B S hS (Yi j) V' ⟶ pair B S hS Yi f i j :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS (f i) (f j)).lift
    (memberChartMap B S hS Yi f hf V V' k) (chartToSpace B S hS (Yi j) V')
    (memberChartMap_comp B S hS Yi f hf V V' k)

/-- The first projection of the morphism to the pairwise fibre product is the morphism to the
target member. -/
theorem memberChartPair_fst {i j : I} (V : SmallEtale B S hS (Yi i).1)
    (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f j) (hf j)).obj V' ⟶
      (smallEtalePostcomp B S hS (f i) (hf i)).obj V) :
    memberChartPair B S hS Yi f hf V V' k ≫ pairFst B S hS Yi f i j =
      memberChartMap B S hS Yi f hf V V' k :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS (f i) (f j)).lift_fst _ _ _

/-- The second projection of the morphism to the pairwise fibre product is the structure morphism
of the source chart. -/
theorem memberChartPair_snd {i j : I} (V : SmallEtale B S hS (Yi i).1)
    (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f j) (hf j)).obj V' ⟶
      (smallEtalePostcomp B S hS (f i) (hf i)).obj V) :
    memberChartPair B S hS Yi f hf V V' k ≫ pairSnd B S hS Yi f i j =
      chartToSpace B S hS (Yi j) V' :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS (f i) (f j)).lift_snd _ _ _

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
