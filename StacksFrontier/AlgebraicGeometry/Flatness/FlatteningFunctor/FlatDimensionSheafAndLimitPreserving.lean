module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.FlatDimensionFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.FlatDimensionLimitPreserving

/-!
# The functor of flatness in dimensions at least `n` is an fpqc sheaf and limit preserving

In the situation of Stacks 05MT — a morphism of schemes `f : X ⟶ S` locally of finite type, a
quasi-coherent `𝒪_X`-module `F` of finite type and a natural number `n`, with `F_n` the functor
on schemes over `S` sending `T` to a singleton if the base change `F_T` is flat over `T` in
dimensions `≥ n` and to the empty set otherwise — the functor `F_n` satisfies the sheaf property
for the fpqc topology, and it is limit preserving as soon as `f` is quasi-compact and locally of
finite presentation and `F` is of finite presentation.

The two assertions have different hypotheses: the sheaf property holds in the ambient situation
alone, while limit preservation needs the three finiteness assumptions.  They are therefore
assembled into a conjunction whose second conjunct is an implication carrying exactly those
three assumptions, so that neither assertion is stated under more than the source grants it.

## Main results

* `AlgebraicGeometry.FlatDimensionSituation.flatDimensionFunctor_isSheaf_fpqc_and_limitPreserving`:
  **Stacks 05MV**, parts (1) and (2) together, under the hypotheses of the source and nothing
  more.  This is the declaration carrying the tag; its two components are
  `AlgebraicGeometry.FlatDimensionSituation.flatDimensionFunctor_isSheaf_fpqc` in
  `StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.FlatDimensionFpqcSheaf` and
  `AlgebraicGeometry.FlatDimensionSituation.flatDimensionFunctor_limitPreserving` in
  `StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.FlatDimensionLimitPreserving`.

## Implementation notes

The index category of the inverse system tested by limit preservation has object and morphism
universes independent of each other, and the universe of the schemes is the maximum of those two
and a third parameter, exactly as in the statement of part (2); the conjunction is stated at the
same universe levels, so it is no less general than its second component.

## References

* [Stacks Project, Tag 05MV](https://stacks.math.columbia.edu/tag/05MV)
* [Stacks Project, Tag 05MT](https://stacks.math.columbia.edu/tag/05MT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.FlatDimensionSituation

/-- **Stacks Project, Tag 05MV.** In Situation 05MT:

1. the functor `F_n` satisfies the sheaf property for the fpqc topology; and
2. if `f` is quasi-compact and locally of finite presentation and `F` is of finite presentation,
   then the functor `F_n` is limit preserving, i.e. it carries a cofiltered inverse limit of
   affine schemes over `S` to a filtered colimit of sets.

The three finiteness assumptions of (2) are hypotheses of (2) only: (1) holds in the ambient
situation alone. -/
@[stacks 05MV "parts (1) and (2)"]
public theorem flatDimensionFunctor_isSheaf_fpqc_and_limitPreserving
    (D : FlatDimensionSituation.{max u v w}) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over D.S) D.flatDimensionFunctor ∧
      (QuasiCompact D.f → LocallyOfFinitePresentation D.f → D.F.IsFinitePresentation →
        LimitPreserving.{max u v w, 0, v, w, max u v w + 1, max u v w}
          (Over.forget D.S) D.flatDimensionFunctor) :=
  ⟨D.flatDimensionFunctor_isSheaf_fpqc,
    fun hqc hfp hFfp ↦ @flatDimensionFunctor_limitPreserving.{u, v, w} D hqc hfp hFfp⟩

end AlgebraicGeometry.FlatDimensionSituation
