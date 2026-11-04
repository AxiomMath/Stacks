module

public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.InducedCategory
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidRestriction

/-!
# The structure morphisms of the arrow space of a restricted groupoid

Let `G` be a groupoid in algebraic spaces over `B` with object space `U` and arrow space `R`,
and let `g : U' ⟶ U` be an arbitrary morphism of algebraic spaces. The *restriction* of `G`
along `g` has object space `U'` and arrow space `U' ×_{g, U, t} R ×_{s, U, g} U'`: an arrow of
the restriction is an arrow of `G` together with a lift of its target and a lift of its source
along `g`. That arrow space, its three structure morphisms, the two projections
`fiberProductFst` and `fiberProductSnd` of a fibre product of algebraic spaces and the
description of the sections of such a fibre product over a test object are all in
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidRestriction`, which this module imports.
What is proved here is the compatibility of the three structure morphisms with `g`, in the
orientation its consumers rewrite with.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.fiberProduct_app_condition`: on a section of a
  fibre product over a test object the two structure morphisms agree.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionArrowsToArrows_comp_source` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionArrowsToArrows_comp_target`: the
  underlying arrow of an arrow of the restriction has source, respectively target, the image
  under `g` of the chosen source, respectively target, lift.

## References

* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044B](https://stacks.math.columbia.edu/tag/044B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- On a section of a fibre product of algebraic spaces over a test object the two structure
morphisms agree. -/
theorem fiberProduct_app_condition {F G H : AlgebraicSpaces C S hS}
    (f : F ⟶ H) (g : G ⟶ H) (T : (BigFppfOver C S hS)ᵒᵖ)
    (x : (AlgebraicSpaces.fiberProduct C S hS f g).obj.obj T) :
    f.hom.app T ((pullback.fst f.hom g.hom).app T x) =
      g.hom.app T ((pullback.snd f.hom g.hom).app T x) := by
  have h := (Space.fiberProductAtEquiv f g T x).2
  rwa [Space.fiberProductAtEquiv_fst, Space.fiberProductAtEquiv_snd] at h

/-- The underlying arrow of an arrow of the restriction has source the image of the chosen
source lift. -/
theorem restrictionArrowsToArrows_comp_source (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    restrictionArrowsToArrows G g ≫ G.source = restrictionSource G g ≫ g := by
  apply ObjectProperty.hom_ext
  ext T x
  show G.source.hom.app T ((pullback.snd g.hom G.target.hom).app T
      ((pullback.fst (pullback.snd g.hom G.target.hom)
        (pullback.fst G.source.hom g.hom)).app T x)) =
    g.hom.app T ((pullback.snd G.source.hom g.hom).app T
      ((pullback.snd (pullback.snd g.hom G.target.hom)
        (pullback.fst G.source.hom g.hom)).app T x))
  exact (congrArg (G.source.hom.app T) (fiberProduct_app_condition
    (fiberProductSnd g G.target) (fiberProductFst G.source g) T x)).trans
      (fiberProduct_app_condition G.source g T
        ((pullback.snd (pullback.snd g.hom G.target.hom)
          (pullback.fst G.source.hom g.hom)).app T x))

/-- The underlying arrow of an arrow of the restriction has target the image of the chosen
target lift. -/
alias restrictionArrowsToArrows_comp_target := restriction_condition'

end AlgebraicGeometry.GroupoidInAlgebraicSpaces
