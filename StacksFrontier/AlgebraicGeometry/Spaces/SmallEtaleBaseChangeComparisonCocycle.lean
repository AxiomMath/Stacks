module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeComposition

/-!
# The base-change square comparison of Stacks 03G2 is compatible with composition

For a representable morphism `f : X ⟶ Y` of algebraic spaces,
`AlgebraicGeometry.Space.smallBaseChange_comparison` compares base change of étale *scheme*
charts with base change of spaces-étale objects, through the comparison functor of Stacks 03G1.
This file proves the cocycle condition relating the three comparisons attached to `f`, `g` and
`f ≫ g`: pasting the squares of `f` and of `g` gives the square of `f ≫ g`, read through the
composition comparisons `AlgebraicGeometry.Space.smallBaseChange_comp` of Stacks 03G2, part (4)
and `AlgebraicGeometry.Space.spacesBaseChange_comp` of Stacks 03G2, part (2).

## Main results

* `AlgebraicGeometry.Space.smallBaseChange_comparison_comp`: the cocycle, at a single étale
  scheme chart of `Z`.

## Implementation notes

Everything in sight is a morphism into an iterated fibre product, and all five comparisons are
pinned down by their compatibility with the cartesian projections; the proof is therefore two
applications of `CategoryTheory.IsPullback.hom_ext`, one for each of the two cartesian squares
of the iterated base change, followed by the identity
`AlgebraicGeometry.Space.smallBaseChange_comp_inv_projection` of morphisms of the big fppf site.
The compatibility with the structure morphisms over `X` — the second hypothesis of each
`hom_ext` — is `CategoryTheory.Over.w`, since every morphism in sight lies in a slice.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z : AlgebraicSpaces B S hS}

/-- The cartesian projection of small-chart base change, read in the spaces-étale site: it is
the Yoneda image of the projection of `AlgebraicGeometry.Space.smallBaseChangeProjection`. -/
theorem smallBaseChange_projection_app_hom (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    ((smallBaseChange_projection B S hS f hf).app V).hom =
      yoneda.map ((smallBaseChangeProjection B S hS f hf).app V) :=
  rfl

/-- **The projections of the iterated base change compose through the comparison.**  The
underlying morphism of algebraic spaces of the composite of the three comparisons, followed by
the two cartesian projections, is the cartesian projection of base change along the
composite.

This is the Yoneda image of
`AlgebraicGeometry.Space.smallBaseChange_comp_inv_projection`. -/
theorem smallBaseChange_comparison_comp_projection (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable (f ≫ g).hom) (V : SmallEtale B S hS Z.1) :
    ((comparisonFunctor B S hS X).map
            ((smallBaseChange_comp B S hS f g hf hg hfg).inv.app V)).hom.left ≫
          (smallBaseChange_projection B S hS f hf).app
            ((smallBaseChange B S hS g hg).obj V) ≫
        (smallBaseChange_projection B S hS g hg).app V =
      (smallBaseChange_projection B S hS (f ≫ g) hfg).app V := by
  refine ObjectProperty.hom_ext _ ?_
  have h := congrArg (fun q ↦ yoneda.map q)
    (smallBaseChange_comp_inv_projection B S hS f g hf hg hfg V)
  rw [Functor.map_comp, Functor.map_comp] at h
  refine Eq.trans ?_ h
  refine congrArg (fun q ↦ q ≫ yoneda.map ((smallBaseChangeProjection B S hS f hf).app
      ((smallBaseChange B S hS g hg).obj V)) ≫
    yoneda.map ((smallBaseChangeProjection B S hS g hg).app V)) ?_
  exact toSpaces_comparisonFunctor_map_hom B S hS X
    ((smallBaseChange_comp B S hS f g hf hg hfg).inv.app V)

/-- Naturality of the cartesian projection of spaces-étale base change, with the underlying
morphisms of algebraic spaces spelled as `Over.Hom.left` of the slice morphisms, which is the
spelling in which the comparison squares of this file are stated. -/
theorem spacesBaseChange_projection_naturality_left (f : X ⟶ Y)
    {V W : SpacesEtale B S hS Y} (m : V ⟶ W) :
    ((spacesBaseChange B S hS f).functor.map m).hom.left ≫
        (spacesBaseChange B S hS f).projection.app W =
      (spacesBaseChange B S hS f).projection.app V ≫ m.hom.left :=
  (spacesBaseChange B S hS f).projection.naturality m

/-- **Two morphisms into an iterated spaces-étale base change agree as soon as their composites
with the two cartesian projections do.**  Both squares are cartesian and both morphisms lie in
the slice over `X`, so the two applications of `CategoryTheory.IsPullback.hom_ext` need only the
projections; the compatibility with the structure morphisms is `CategoryTheory.Over.w`. -/
theorem spacesEtale_hom_ext_baseChange_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (V' : SpacesEtale B S hS Z) {A : SpacesEtale B S hS X}
    {k l : A ⟶ (spacesBaseChange B S hS f).functor.obj
      ((spacesBaseChange B S hS g).functor.obj V')}
    (h : k.hom.left ≫
          ((spacesBaseChange B S hS f).projection.app
              ((spacesBaseChange B S hS g).functor.obj V') ≫
            (spacesBaseChange B S hS g).projection.app V') =
        l.hom.left ≫
          ((spacesBaseChange B S hS f).projection.app
              ((spacesBaseChange B S hS g).functor.obj V') ≫
            (spacesBaseChange B S hS g).projection.app V')) :
    k = l := by
  have hw := ((spacesBaseChange B S hS f).isPullback
    ((spacesBaseChange B S hS g).functor.obj V')).w
  refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext ?_)
  refine ((spacesBaseChange B S hS f).isPullback
      ((spacesBaseChange B S hS g).functor.obj V')).hom_ext ?_
    ((Over.w k.hom).trans (Over.w l.hom).symm)
  refine ((spacesBaseChange B S hS g).isPullback V').hom_ext
    ((Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)) ?_
  rw [Category.assoc, Category.assoc, hw, ← Category.assoc, ← Category.assoc, Over.w k.hom,
    Over.w l.hom]

/-- **The base-change square comparison of Stacks 03G2 is compatible with composition.**
Pasting the comparison squares of `f` and of `g`, and passing from base change along the
composite to the iterated base change on both the scheme-chart and the spaces-étale side, gives
the comparison square of `f ≫ g`.

Both sides are morphisms into the iterated spaces-étale base change, so the identity is pinned
down by the two cartesian projections, where it is
`AlgebraicGeometry.Space.smallBaseChange_comp_inv_projection`. -/
theorem smallBaseChange_comparison_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable (f ≫ g).hom) (V : SmallEtale B S hS Z.1) :
    (comparisonFunctor B S hS X).map
          ((smallBaseChange_comp B S hS f g hf hg hfg).inv.app V) ≫
        (smallBaseChange_comparison B S hS f hf).hom.app
            ((smallBaseChange B S hS g hg).obj V) ≫
          (spacesBaseChange B S hS f).functor.map
            ((smallBaseChange_comparison B S hS g hg).hom.app V) =
      (smallBaseChange_comparison B S hS (f ≫ g) hfg).hom.app V ≫
        (spacesBaseChange_comp B S hS f g).inv.app ((comparisonFunctor B S hS Z).obj V) := by
  refine spacesEtale_hom_ext_baseChange_comp B S hS f g
    ((comparisonFunctor B S hS Z).obj V) ?_
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.comp_hom, Over.comp_left, Over.comp_left, Over.comp_left]
  simp only [Category.assoc]
  rw [← Category.assoc ((spacesBaseChange B S hS f).functor.map
      ((smallBaseChange_comparison B S hS g hg).hom.app V)).hom.left,
    spacesBaseChange_projection_naturality_left B S hS f
      (V := (comparisonFunctor B S hS Y).obj ((smallBaseChange B S hS g hg).obj V))
      (W := (spacesBaseChange B S hS g).functor.obj ((comparisonFunctor B S hS Z).obj V))
      ((smallBaseChange_comparison B S hS g hg).hom.app V),
    Category.assoc, smallBaseChange_comparison_projection B S hS g hg V,
    ← Category.assoc ((smallBaseChange_comparison B S hS f hf).hom.app
      ((smallBaseChange B S hS g hg).obj V)).hom.left,
    smallBaseChange_comparison_projection B S hS f hf
      ((smallBaseChange B S hS g hg).obj V),
    ← spacesBaseChange_comp_projection B S hS f g ((comparisonFunctor B S hS Z).obj V),
    ← Category.assoc ((spacesBaseChange_comp B S hS f g).inv.app
      ((comparisonFunctor B S hS Z).obj V)).hom.left,
    ← Over.comp_left, ← ObjectProperty.FullSubcategory.comp_hom,
    Iso.inv_hom_id_app, ObjectProperty.FullSubcategory.id_hom, Over.id_left, Category.id_comp,
    smallBaseChange_comparison_projection B S hS (f ≫ g) hfg V]
  exact smallBaseChange_comparison_comp_projection B S hS f g hf hg hfg V

end AlgebraicGeometry.Space

end
