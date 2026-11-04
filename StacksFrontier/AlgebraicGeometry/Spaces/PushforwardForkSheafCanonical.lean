module

public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardForkSheafTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardParallelArrowCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardUnitArrowCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure

/-!
# The sequence of Stacks 03M8 with its canonical arrows is a limiting fork of sheaves

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, let `U` be a surjective étale scheme chart of `X`, let `R = U ×_X U` with its two
projections `t, s : R ⟶ U`, and let `G` be a sheaf of sets on the small étale site of `X` at the
universe of the structure rings.  Writing `τ` and `ρ` for the structure morphisms of `U` and `R`
read as étale morphisms of algebraic spaces and putting `a = τ ≫ f`, `b = ρ ≫ f`, Stacks 03M8
asserts the exactness of

`0 → f_*G → a_*(G|_U) → b_*(G|_R)`.

`AlgebraicGeometry.Space.isLimitForkSheafDirectImage` proves that this is a limiting fork in the
category of sheaves on the small étale site of `Y`, but with the *geometric* arrows: its first
arrow is restriction along the counit of the product comonad of the chart and its parallel
arrows are restriction along `prod.map t (𝟙)` and `prod.map s (𝟙)`, each read in the `a_*`/`b_*`
spelling.  This file replaces those three arrows by the **canonical** ones,
`AlgebraicGeometry.Space.chartDirectImageUnitArrow` and
`AlgebraicGeometry.Space.chartDirectImageParallelArrow`, which are built from the unit of
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` and the composition comparison of
Stacks 03G2, part (3), and in which no geometric spelling is left.

Nothing is reproved: the identification of the first arrow is
`AlgebraicGeometry.Space.chartDirectImageUnitArrow_sectionsIso` and the identification of the
parallel arrows is
`AlgebraicGeometry.Space.directImageEtaleRestrictionParallel_eq_chartDirectImageParallelArrow`,
and the limiting fork is carried across them.

## Main definitions

* `AlgebraicGeometry.Space.isLimitForkSheafChartDirectImageCanonical`: **the canonical-arrow
  form of Stacks 03M8 at the level of sheaves of sets.**

## Main results

* `AlgebraicGeometry.Space.sheafChartDirectImageUnit_eq_chartDirectImageUnitArrow` and
  `AlgebraicGeometry.Space.sheafChartDirectImageParallel_eq_chartDirectImageParallelArrow`: the
  three arrows of `AlgebraicGeometry.Space.isLimitForkSheafDirectImage` *are* the canonical
  arrows, as morphisms of sheaves.
* `AlgebraicGeometry.Space.fork_condition_chartDirectImageCanonical`: the fork condition on the
  canonical arrows, which needs no identification at all — both composites are the canonical
  first arrow attached to `ρ`, by
  `AlgebraicGeometry.Space.chartDirectImageUnitArrow_comp_parallelArrow`.

## Implementation notes

The canonical parallel arrow at a morphism `t` of étale scheme charts of `X` needs the
underlying morphism `R ⟶ U` of algebraic spaces to be étale, while the geometric one does not.
No hypothesis is added for it: a morphism of étale scheme charts represents an étale morphism of
algebraic spaces by `AlgebraicGeometry.Space.isEtale_chartMap`, so the assembled fork is as
unconditional as the geometric one.

The two limiting forks have the same three terms and, by the two identifications, the same three
arrows; but a fork is a cone over `CategoryTheory.Limits.parallelPair` of its two parallel
arrows, so the transport is along equalities of arrows and not along an isomorphism of cones.
It is `CategoryTheory.Limits.isLimitForkOfMap` — the transport the geometric fork was itself
assembled by — at the identity functor and the identity isomorphisms of the middle and right
terms, whose three compatibility hypotheses are then the three arrow equalities with a unit of
composition on one side.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (G : Sheaf (SmallEtale.topology B S hS X.1) (Type u))

/-! ### The arrows of the fork of sheaves are the canonical arrows -/

/-- **The first arrow of the fork of sheaves of Stacks 03M8 is the canonical first arrow.**  The
arrow `AlgebraicGeometry.Space.sheafChartDirectImageUnit` of
`AlgebraicGeometry.Space.isLimitForkSheafDirectImage` is
`AlgebraicGeometry.Space.chartDirectImageUnitArrow`, the direct image along `f` of the unit of
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` at the structure morphism of the
chart followed by the composition comparison of Stacks 03G2, part (3).

Sheaves are a full subcategory of presheaves, so it suffices to compare the morphisms of
presheaves; there the fork's arrow is restriction along the counit of the product comonad read
across the sections identification, which is
`AlgebraicGeometry.Space.chartDirectImageUnitArrow_sectionsIso`. -/
theorem sheafChartDirectImageUnit_eq_chartDirectImageUnitArrow (U : SmallEtale B S hS X.1) :
    sheafChartDirectImageUnit B S hS f G U =
      chartDirectImageUnitArrow B S hS f ((comparisonFunctor B S hS X).obj U).2 G :=
  Sheaf.hom_ext_iff.2
    (show chartDirectImageGeometricUnit B S hS f G U =
        (chartDirectImageUnitArrow B S hS f ((comparisonFunctor B S hS X).obj U).2 G).hom from
      ((Iso.eq_comp_inv (chartDirectImageSectionsIso B S hS f G U)).2
        (chartDirectImageUnitArrow_sectionsIso B S hS
          ((comparisonFunctor B S hS X).obj U).1.hom
          ((comparisonFunctor B S hS X).obj U).2 G f)).symm)

variable {U R : SmallEtale B S hS X.1}

/-- **A parallel arrow of the fork of sheaves of Stacks 03M8 is a canonical parallel arrow.**
The arrow `AlgebraicGeometry.Space.sheafChartDirectImageParallel` at a morphism `t` of étale
scheme charts of `X` is `AlgebraicGeometry.Space.chartDirectImageParallelArrow` at the
factorization of the structure morphism of `R` through that of `U` given by `t`.

With `R = U ×_X U` and `t, s : R ⟶ U` its two projections this says that the source's `t^*` and
`s^*` are the two parallel arrows of the fork.  Sheaves are a full subcategory of presheaves,
and on presheaves this is
`AlgebraicGeometry.Space.directImageEtaleRestrictionParallel_eq_chartDirectImageParallelArrow`;
the étaleness the canonical arrow needs of the morphism `R ⟶ U` of algebraic spaces represented
by `t` is `AlgebraicGeometry.Space.isEtale_chartMap`. -/
theorem sheafChartDirectImageParallel_eq_chartDirectImageParallelArrow (t : R ⟶ U) :
    sheafChartDirectImageParallel B S hS f G t =
      chartDirectImageParallelArrow B S hS f ((comparisonFunctor B S hS X).obj U).2
        (isEtale_chartMap B S hS X t) ((comparisonFunctor B S hS X).obj R).2
        (Over.w ((comparisonFunctor B S hS X).map t).hom) G :=
  Sheaf.hom_ext_iff.2
    (show chartDirectImageGeometricParallel B S hS f G t =
        (chartDirectImageParallelArrow B S hS f ((comparisonFunctor B S hS X).obj U).2
          (isEtale_chartMap B S hS X t) ((comparisonFunctor B S hS X).obj R).2
          (Over.w ((comparisonFunctor B S hS X).map t).hom) G).hom from
      directImageEtaleRestrictionParallel_eq_chartDirectImageParallelArrow B S hS
        ((comparisonFunctor B S hS X).obj U).1.hom ((comparisonFunctor B S hS X).obj U).2
        ((comparisonFunctor B S hS X).map t).hom.left (isEtale_chartMap B S hS X t) f G
        ((comparisonFunctor B S hS X).obj R).2
        (Over.w ((comparisonFunctor B S hS X).map t).hom))

/-! ### The canonical fork -/

/-- **The fork condition on the canonical arrows of Stacks 03M8.**  For two morphisms `t, s` of
étale scheme charts of `X` with the same source and target, the canonical first arrow followed
by the canonical parallel arrow of `t` and followed by that of `s` agree.

No identification is involved: both composites are the canonical first arrow attached to the
structure morphism of `R`, by
`AlgebraicGeometry.Space.chartDirectImageUnitArrow_comp_parallelArrow`, which is the statement
that the composite does not depend on the factorization. -/
theorem fork_condition_chartDirectImageCanonical (t s : R ⟶ U) :
    chartDirectImageUnitArrow B S hS f ((comparisonFunctor B S hS X).obj U).2 G ≫
        chartDirectImageParallelArrow B S hS f ((comparisonFunctor B S hS X).obj U).2
          (isEtale_chartMap B S hS X t) ((comparisonFunctor B S hS X).obj R).2
          (Over.w ((comparisonFunctor B S hS X).map t).hom) G =
      chartDirectImageUnitArrow B S hS f ((comparisonFunctor B S hS X).obj U).2 G ≫
        chartDirectImageParallelArrow B S hS f ((comparisonFunctor B S hS X).obj U).2
          (isEtale_chartMap B S hS X s) ((comparisonFunctor B S hS X).obj R).2
          (Over.w ((comparisonFunctor B S hS X).map s).hom) G :=
  chartDirectImageUnitArrow_comp_parallelArrow_eq B S hS f
    ((comparisonFunctor B S hS X).obj U).2 (isEtale_chartMap B S hS X t)
    (isEtale_chartMap B S hS X s) ((comparisonFunctor B S hS X).obj R).2
    (Over.w ((comparisonFunctor B S hS X).map t).hom)
    (Over.w ((comparisonFunctor B S hS X).map s).hom) G

/-- **Stacks 03M8 with its canonical arrows, as a fork of sheaves on the small étale site of the
target.**  Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`, let `U` be a surjective
étale scheme chart of `X`, let `R = U ×_X U` with its two projections `t, s : R ⟶ U`, and let
`G` be a sheaf of sets on the small étale site of `X` at the universe of the structure rings.
Put `a = τ ≫ f` and `b = ρ ≫ f` for the structure morphisms `τ` of `U` and `ρ` of `R`.  Then

`f_*G → a_*(G|_U) ⇉ b_*(G|_R)`

is a limiting fork in the category of sheaves on the small étale site of `Y`, where the first
arrow is `AlgebraicGeometry.Space.chartDirectImageUnitArrow` and the two parallel arrows are
`AlgebraicGeometry.Space.chartDirectImageParallelArrow` at the two factorizations of `ρ` through
`τ` given by `t` and by `s` — that is, with the canonical arrows of the source's sequence, the
unit of `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` pushed forward and
conjugated by the composition comparisons of Stacks 03G2, part (3), and no geometric spelling
left anywhere in the statement.

`AlgebraicGeometry.Space.isLimitForkSheafDirectImage` is the same fork with the geometric
arrows; this transports it along
`AlgebraicGeometry.Space.sheafChartDirectImageUnit_eq_chartDirectImageUnitArrow` and
`AlgebraicGeometry.Space.sheafChartDirectImageParallel_eq_chartDirectImageParallelArrow`. -/
noncomputable def isLimitForkSheafChartDirectImageCanonical
    (hU : IsSurjective B S hS U.1.hom) {t s : R ⟶ U}
    (hR : IsPullback ((comparisonFunctor B S hS X).map t) ((comparisonFunctor B S hS X).map s)
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))) :
    IsLimit (Fork.ofι
      (chartDirectImageUnitArrow B S hS f ((comparisonFunctor B S hS X).obj U).2 G)
      (fork_condition_chartDirectImageCanonical B S hS f G t s)) :=
  isLimitForkOfMap (𝟭 _) (fork_condition_sheafChartDirectImage B S hS f G t s)
    (isLimitForkSheafDirectImage B S hS f G hU hR) (Iso.refl _) (Iso.refl _)
    ((sheafChartDirectImageUnit_eq_chartDirectImageUnitArrow B S hS f G U).symm.trans
      (Category.comp_id _).symm)
    ((Category.id_comp _).trans
      ((sheafChartDirectImageParallel_eq_chartDirectImageParallelArrow B S hS f G t).symm.trans
        (Category.comp_id _).symm))
    ((Category.id_comp _).trans
      ((sheafChartDirectImageParallel_eq_chartDirectImageParallelArrow B S hS f G s).symm.trans
        (Category.comp_id _).symm))
    (fork_condition_chartDirectImageCanonical B S hS f G t s)

end AlgebraicGeometry.Space

end
