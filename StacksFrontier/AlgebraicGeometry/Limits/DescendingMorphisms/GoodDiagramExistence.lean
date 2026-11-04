module

public import StacksFrontier.AlgebraicGeometry.Descent.Finiteness.ClosedImmersionIntoFinitePresentation
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.FiniteTypeModel

/-!
# Existence of a good diagram for a quasi-separated finite-type scheme over a limit

Let `S = lim S_i` be the limit of a directed inverse system of Noetherian schemes with affine
transition morphisms, and let `X ⟶ S` be quasi-separated and of finite type. Then there is a
stage `i`, a scheme `W` of finite type over `S_i` and a morphism `X ⟶ W` making the square with
`X ⟶ S` and `W ⟶ S_i` commute, such that the induced morphism `X ⟶ S ×_{S_i} W` is a closed
immersion. Such a diagram is an
`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram`.

## Main results

* `AlgebraicGeometry.LimitNoetherianSituation.nonempty_goodDiagram`: a good diagram exists.
* `AlgebraicGeometry.LimitNoetherianSituation.nonempty_goodDiagram_of_essentiallySmall`: the
  same for an index type at a universe independent of the universe of the schemes, under
  essential smallness of the index relative to that universe.

## Implementation notes

The two inputs are the factorization of a morphism locally of finite type from a quasi-compact
quasi-separated scheme as a closed immersion followed by a morphism of finite presentation
(`AlgebraicGeometry.exists_finitePresentation_closedImmersion`), and the descent of a scheme of
finite presentation over the limit to a scheme of finite presentation over a stage
(`AlgebraicGeometry.LimitDescent.exists_isPullback_of_finitePresentation_of_essentiallySmall`).
Composing the closed immersion with the comparison isomorphism of the descended model gives a
closed immersion of `X` into a base change of a finite-type model, which is a good diagram by
`AlgebraicGeometry.LimitNoetherianSituation.nonempty_goodDiagram_of_isClosedImmersion`.

Finite presentation of the model is stronger than the finite type the diagram asks for; it is
weakened on the way in. Over the Noetherian `S_i` the two agree, but that equivalence is not
needed.

## Universe situation

The descent of the model is available for an index category whose universes are independent of
the universe of the schemes at the cost of `CategoryTheory.EssentiallySmall.{u}` on the index,
and the three topological facts about the limit taken from
`StacksFrontier/AlgebraicGeometry/Limits/DescendingMorphisms/FiniteTypeModel.lean` carry the same
hypothesis. For an index type in the universe of the schemes, which is the situation of the
source — a directed *set* — essential smallness is automatic, and the statement carrying the tag
assumes nothing beyond the source.

## References

* [Stacks Project, Tag 0CNM](https://stacks.math.columbia.edu/tag/0CNM)
* [Stacks Project, Tag 0CNN](https://stacks.math.columbia.edu/tag/0CNN)
* [Stacks Project, Tag 0CNP](https://stacks.math.columbia.edu/tag/0CNP)
* [Stacks Project, Tag 01ZG](https://stacks.math.columbia.edu/tag/01ZG)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM), part (1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

namespace LimitNoetherianSituation

/-- A quasi-separated morphism of finite type into the limit of a directed inverse system of
Noetherian schemes with affine transition morphisms admits a good diagram, the index type being
essentially small relative to the universe of the schemes. -/
theorem nonempty_goodDiagram_of_essentiallySmall {I : Type v} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] [EssentiallySmall.{u} I] (D : LimitNoetherianSituation.{v, u} I)
    {X : Scheme.{u}} (f : X ⟶ D.limitScheme) [QuasiSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] :
    Nonempty (GoodDiagram D f) := by
  have : QuasiSeparatedSpace D.limitScheme := D.quasiSeparatedSpace_limitScheme
  have : CompactSpace X := D.compactSpace_of_quasiCompact_toLimitScheme f
  have : QuasiSeparatedSpace X := D.quasiSeparatedSpace_of_quasiSeparated_toLimitScheme f
  obtain ⟨X', p, ι, hp, hι, hιp⟩ := exists_finitePresentation_closedImmersion f
  obtain ⟨j, W, w, g, hw, hpb⟩ :=
    LimitDescent.exists_isPullback_of_finitePresentation_of_essentiallySmall
      D.system D.limitCone D.isLimit p hp
  have hw₁ : LocallyOfFiniteType w :=
    have := hw.locallyOfFinitePresentation
    inferInstance
  refine nonempty_goodDiagram_of_isClosedImmersion D j.unop w hw₁ hw.quasiCompact
    (ι ≫ hpb.flip.isoPullback.hom) ?_ ?_
  · have : IsClosedImmersion ι := hι
    have : IsIso hpb.flip.isoPullback.hom := inferInstance
    infer_instance
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => ι ≫ k) hpb.flip.isoPullback_hom_fst).trans hιp)

/-- **Stacks Project, Tag 0CNN.** In the limit situation `S = lim S_i` of a directed inverse
system of Noetherian schemes with affine transition morphisms, a quasi-separated morphism
`X ⟶ S` of finite type fits into a diagram over some stage `S_i` with a model `W` of finite type
over `S_i` whose base change receives `X` as a closed subscheme. -/
@[stacks 0CNN]
theorem nonempty_goodDiagram {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : LimitNoetherianSituation.{u, u} I) {X : Scheme.{u}} (f : X ⟶ D.limitScheme)
    [QuasiSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    Nonempty (GoodDiagram D f) :=
  have : EssentiallySmall.{u} I := ⟨⟨I, inferInstance, ⟨CategoryTheory.Equivalence.refl⟩⟩⟩
  nonempty_goodDiagram_of_essentiallySmall D f

end LimitNoetherianSituation

end AlgebraicGeometry

/-! ### Faithfulness check

The conclusion of Tag 0CNN with the bundle
`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram` unfolded: the stage, the model and its
structure morphism, the horizontal morphism, the commutativity of the square, the finite type of
the model and the closed immersion induced by the square, all spelled out and closed by the
tagged statement.
-/

namespace Tag0CNN

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.LimitNoetherianSituation

example {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : LimitNoetherianSituation.{u, u} I) {X : Scheme.{u}} (f : X ⟶ D.limitScheme)
    [QuasiSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (i : I) (W : Scheme.{u}) (w : W ⟶ D.system.obj (op i)) (g : X ⟶ W)
      (h : f ≫ D.limitCone.π.app (op i) = g ≫ w),
      LocallyOfFiniteType w ∧ QuasiCompact w ∧ IsClosedImmersion (pullback.lift f g h) :=
  let G := (nonempty_goodDiagram D f).some
  ⟨G.index, G.W, G.modelMap, G.toModel, G.commutes,
    G.locallyOfFiniteType, G.quasiCompact, G.isClosedImmersion⟩

end Tag0CNN
