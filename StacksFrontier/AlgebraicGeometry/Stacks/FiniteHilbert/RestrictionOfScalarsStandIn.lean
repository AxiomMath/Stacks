module

public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RestrictionOfScalarsSectionSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbertRelativeRepresentable

/-!
# Spaces of sections over finite locally free covers as restrictions of scalars

Let `q : Z ⟶ U` be a degree-`d` finite locally free cover in the big fppf site of `S`, let `W` be
an algebraic space over `Z` and let `w` be a presentation of `W` over the site of `U`. Since `U` is
final in the site of `U`, `AlgebraicGeometry.Space.restrictionOfScalarsIsoSectionSpace` identifies
the space of sections `AlgebraicGeometry.Space.sectionSpace` of `w` with the restriction of scalars
of `w` along the structure morphism of the cover. Hence the space of sections is an algebraic space
over `U` as soon as the restriction of scalars is.

## Main results

* `restrictionOfScalarsIsAlgebraicSpace_of_isAlgebraicSpace_restrictionOfScalars`: the space of
  sections is an algebraic space over `U` whenever the corresponding restriction of scalars is.

## References

* [Stacks Project, Tag 05YF](https://stacks.math.columbia.edu/tag/05YF)
* [Stacks Project, Tag 05YJ](https://stacks.math.columbia.edu/tag/05YJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (d : ℕ)

/-- For every degree-`d` finite locally free cover `q : Z ⟶ U` of the big fppf site of `S`, every
algebraic space `W` over `Z` and every presentation `w` of `W` over the site of `U`, the space of
sections of `w` is an algebraic space over `U` as soon as the restriction of scalars of `w` along
the structure morphism of the cover is. -/
theorem restrictionOfScalarsIsAlgebraicSpace_of_isAlgebraicSpace_restrictionOfScalars
    (h : ∀ (U Z : BigFppfOver B S hS) (q : Z ⟶ U),
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) d →
      ∀ (W : (BigFppfOver B (B.inclusion.obj Z.left) Z.left.property)ᵒᵖ ⥤ Type u)
        (hW : IsAlgebraicSpace B (B.inclusion.obj Z.left) Z.left.property W)
        (w : (OverShriek.relocalizePresheafFunctor q.left).obj W ⟶
          yoneda.obj (Over.mk q.left :
            BigFppfOver B (B.inclusion.obj U.left) U.left.property)),
        IsAlgebraicSpace B (B.inclusion.obj U.left) U.left.property
          (Space.restrictionOfScalars B (B.inclusion.obj U.left) U.left.property
            (Space.SectionSpaceRestriction.toCover B (B.inclusion.obj U.left) U.left.property
              (Over.mk q.left) ((OverShriek.relocalizePresheafFunctor q.left).obj W)
              (Space.isAlgebraicSpace_relocalizePresheaf B (B.inclusion.obj U.left)
                U.left.property (Over.mk q.left) W hW) w)
            (Space.SectionSpaceRestriction.toBase B (B.inclusion.obj U.left) U.left.property
              (Over.mk q.left))).presheaf) :
    ∀ (U Z : BigFppfOver B S hS) (q : Z ⟶ U),
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) d →
      ∀ (W : (BigFppfOver B (B.inclusion.obj Z.left) Z.left.property)ᵒᵖ ⥤ Type u),
        IsAlgebraicSpace B (B.inclusion.obj Z.left) Z.left.property W →
        ∀ (w : (OverShriek.relocalizePresheafFunctor q.left).obj W ⟶
            yoneda.obj (Over.mk q.left :
              BigFppfOver B (B.inclusion.obj U.left) U.left.property)),
          IsAlgebraicSpace B (B.inclusion.obj U.left) U.left.property
            (Space.sectionSpace B (B.inclusion.obj U.left) U.left.property (Over.mk q.left)
              ((OverShriek.relocalizePresheafFunctor q.left).obj W) w) :=
  fun U Z q hq W hW w ↦ Space.isAlgebraicSpace_of_iso B (B.inclusion.obj U.left) U.left.property
    (Space.restrictionOfScalarsIsoSectionSpace B (B.inclusion.obj U.left) U.left.property
      (Over.mk q.left) ((OverShriek.relocalizePresheafFunctor q.left).obj W)
      (Space.isAlgebraicSpace_relocalizePresheaf B (B.inclusion.obj U.left) U.left.property
        (Over.mk q.left) W hW) w)
    (h U Z q hq W hW w)

end AlgebraicGeometry.Stack

end
