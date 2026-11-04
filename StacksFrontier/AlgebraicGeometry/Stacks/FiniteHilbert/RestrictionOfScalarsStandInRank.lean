module

public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbertRelativeRepresentable
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.SectionSpaceFiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.RestrictionOfScalarsStandIn

/-!
# Stacks 05YF over the covers of the site

For every degree-`d` finite locally free cover `q : Z ⟶ U` of the big fppf site of `S` and every
algebraic space `W` over `Z` presented over the site of `U`, the space of sections of the
presentation is an algebraic space over `U`. This is the shape in which the relative
representability of Stacks 05YJ uses Stacks 05YF;
`StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.RestrictionOfScalarsStandIn` reduced it to
the algebraicity of the corresponding restriction of scalars, and listed what that still owed.

All of it is available. The finite local freeness supplied is that of the morphism of *schemes*
underlying `q`, at the fixed rank `d`, which is exactly the hypothesis of
`AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_of_isFiniteLocallyFreeOfRank`.

## Main results

* `AlgebraicGeometry.Stack.restrictionOfScalarsIsAlgebraicSpace`: the statement above.

## Implementation notes

No property of the presentation `w` is used — not even that it reads off the factorization through
`Z` carried by a section — exactly as in
`Stack.restrictionOfScalarsIsAlgebraicSpace_of_isAlgebraicSpace_restrictionOfScalars`: the space of
sections is an algebraic space for every presentation.

The library's proof of Stacks 05YJ,
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_mapRelative_of_representable`, does not
go through this file: it applies
`AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_of_isFiniteLocallyFree` directly.

## References

* [Stacks Project, Tag 05YF](https://stacks.math.columbia.edu/tag/05YF)
* [Stacks Project, Tag 05YJ](https://stacks.math.columbia.edu/tag/05YJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (d : ℕ)

/-- **Stacks 05YF over the covers of the site.** For every degree-`d` finite locally free cover
`q : Z ⟶ U` of the big fppf site of `S`, every algebraic space `W` over `Z` and every
presentation of `W` over the site of `U`, the space of sections of the presentation is an
algebraic space over `U`.

The relocalization of `W` is an algebraic space over `U` by
`AlgebraicGeometry.Space.isAlgebraicSpace_relocalizePresheaf`, and the space of sections is then
`AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_of_isFiniteLocallyFreeOfRank` at the
structure morphism of the cover, whose finite local freeness of rank `d` is the hypothesis on
`q`. -/
theorem restrictionOfScalarsIsAlgebraicSpace :
    ∀ (U Z : BigFppfOver B S hS) (q : Z ⟶ U),
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) d →
      ∀ (W : (BigFppfOver B (B.inclusion.obj Z.left) Z.left.property)ᵒᵖ ⥤ Type u),
        IsAlgebraicSpace B (B.inclusion.obj Z.left) Z.left.property W →
        ∀ (w : (OverShriek.relocalizePresheafFunctor q.left).obj W ⟶
            yoneda.obj (Over.mk q.left :
              BigFppfOver B (B.inclusion.obj U.left) U.left.property)),
          IsAlgebraicSpace B (B.inclusion.obj U.left) U.left.property
            (Space.sectionSpace B (B.inclusion.obj U.left) U.left.property (Over.mk q.left)
              ((OverShriek.relocalizePresheafFunctor q.left).obj W) w) := by
  intro U Z q hq W hW w
  have hinst : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B (B.inclusion.obj U.left) U.left.property).map
        (Over.mkIdTerminal.from
          (Over.mk q.left : BigFppfOver B (B.inclusion.obj U.left) U.left.property))) d := by
    rw [Space.toScheme_map_from_baseTerminal]
    exact hq
  exact Space.isAlgebraicSpace_sectionSpace_of_isFiniteLocallyFreeOfRank B
    (B.inclusion.obj U.left) U.left.property (Over.mk q.left)
    ((OverShriek.relocalizePresheafFunctor q.left).obj W) w
    (Space.isAlgebraicSpace_relocalizePresheaf B (B.inclusion.obj U.left) U.left.property
      (Over.mk q.left) W hW) d

end AlgebraicGeometry.Stack

end
