module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.ModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackOfAction
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SmoothActionGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.SmoothQuotientStackModel

/-!
# The quotient stack of an action of a smooth group is an algebraic stack

Let `B` be an algebraic space over a scheme `S` of a big fppf site, let `G` be a group object in
the slice of presheaves over `B` whose underlying presheaf is an algebraic space and whose
structure morphism `G ⟶ B` is smooth, and let `G` act on an algebraic space `X` over `B`. Then
the quotient stack `[X/G]` of Stacks 044Q, part (2), is an algebraic stack over `S`.

In particular, for a group scheme `G` of the big fppf site acting on a scheme `Q` of that site, the
group algebraic space `G_B = B ×_S G` acts on `B ×_S Q` over `B`, and the quotient stack `[Q/G_B]`
is algebraic as soon as `B ×_S G ⟶ B` is smooth.

## Main definitions

* `AlgebraicGeometry.Stack.quotientStackOfGroupSchemeInSite`: the quotient stack `[Q/G_B]` of
  the action of a group scheme of the big fppf site on a scheme of that site.
* `AlgebraicGeometry.Stack.quotientStackOfGroupSchemeInSiteOnOver`: the same, for an action
  written in the slice of all schemes over `S`.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStackOfAction_of_isSmooth`: **Stacks 04TK**
  for the quotient stack of a group action.
* `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStackOfGroupSchemeInSite_of_isSmooth`: the
  same for the quotient stack `[Q/G_B]`.
* `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStackOfGroupSchemeInSiteOnOver_of_isSmooth`:
  the same for the slice form.

## References

* [Stacks Project, Tag 0444](https://stacks.math.columbia.edu/tag/0444)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 04TH](https://stacks.math.columbia.edu/tag/04TH)
* [Stacks Project, Tag 04TK](https://stacks.math.columbia.edu/tag/04TK)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Stack

universe u w

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-- **Stacks 04TK** for a group action: if the structure morphism `G ⟶ B` of a group object in
the slice of presheaves over `B` is smooth, then the quotient stack `[X/G]` of Stacks 044Q,
part (2), is an algebraic stack over `S`. -/
@[stacks 04TK "the quotient stack of an action of a smooth group algebraic space"]
theorem isAlgebraicStack_quotientStackOfAction_of_isSmooth
    (B : AlgebraicSpaces C S hS) (G X : Over B.obj) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace C S hS G.left) (hX : IsAlgebraicSpace C S hS X.left)
    (hsm : Space.IsSmooth C S hS G.hom) :
    IsAlgebraicStack.{u, w} C S hS (quotientStackOfAction B G X hG hX) :=
  isAlgebraicStack_quotientStack_of_isSmooth_unconditional.{u, w}
    (Space.isSmooth_groupoidOfAction B G X hG hX hsm)

open Limits CartesianMonoidalCategory

/-- The quotient stack `[Q/G_B]` of the action on `B ×_S Q` of the group algebraic space
`G_B = B ×_S G` attached to a group scheme `G` of the big fppf site acting on a scheme `Q` of
that site. -/
noncomputable def quotientStackOfGroupSchemeInSite (B : AlgebraicSpaces C S hS)
    (G : BigFppfOver C S hS) (hG : GrpObj ((Space.toSchemeOver C S hS).obj G))
    (Q : BigFppfOver C S hS)
    (hQ : letI := hG;
      ModObj ((Space.toSchemeOver C S hS).obj G) ((Space.toSchemeOver C S hS).obj Q)) :
    BasedCategory (BigFppfOver C S hS) :=
  letI := Space.pointsOnSiteModObj C S hS G hG ((Space.toSchemeOver C S hS).obj Q) hQ
  quotientStackOfAction B
    (Over.mk (prod.fst : B.obj ⨯ (Space.pointsOnSite C S hS G hG ⋙ forget GrpCat) ⟶ B.obj))
    (Over.mk (prod.fst :
      B.obj ⨯ ((Space.toSchemeOver C S hS).op ⋙
        yoneda.obj ((Space.toSchemeOver C S hS).obj Q)) ⟶ B.obj))
    (Space.isAlgebraicSpace_prod_compForget_of_representableBy C S hS B.obj B.property _
      (Space.pointsOnSiteRepresentableBy C S hS G hG))
    (Space.isAlgebraicSpace_prod_toSchemeOverYoneda C S hS B.obj B.property Q)

/-- **Stacks 04TK** for the action of a group scheme of the big fppf site on a scheme of that
site: the quotient stack `[Q/G_B]` is an algebraic stack over `S` as soon as the structure
morphism `B ×_S G ⟶ B` of the group algebraic space is smooth. -/
theorem isAlgebraicStack_quotientStackOfGroupSchemeInSite_of_isSmooth
    (B : AlgebraicSpaces C S hS)
    (G : BigFppfOver C S hS) (hG : GrpObj ((Space.toSchemeOver C S hS).obj G))
    (Q : BigFppfOver C S hS)
    (hQ : letI := hG;
      ModObj ((Space.toSchemeOver C S hS).obj G) ((Space.toSchemeOver C S hS).obj Q))
    (hsm : Space.IsSmooth C S hS
      (prod.fst : B.obj ⨯ (Space.pointsOnSite C S hS G hG ⋙ forget GrpCat) ⟶ B.obj)) :
    IsAlgebraicStack.{u, w} C S hS (quotientStackOfGroupSchemeInSite B G hG Q hQ) :=
  let := Space.pointsOnSiteModObj C S hS G hG ((Space.toSchemeOver C S hS).obj Q) hQ
  isAlgebraicStack_quotientStackOfAction_of_isSmooth.{u, w} B _ _ _ _ hsm

/-- The quotient stack `[X/G_B]` of an action of a group scheme `G` of the big fppf site on a
scheme `X` over `S` whose underlying scheme belongs to the site, with the action written in the
slice of all schemes over `S`. -/
noncomputable def quotientStackOfGroupSchemeInSiteOnOver (B : AlgebraicSpaces C S hS)
    (G : BigFppfOver C S hS) (hG : GrpObj ((Space.toSchemeOver C S hS).obj G))
    {X : Over S} (hX : letI := hG; ModObj ((Space.toSchemeOver C S hS).obj G) X)
    (hXc : C.Contains X.left) :
    BasedCategory (BigFppfOver C S hS) :=
  quotientStackOfGroupSchemeInSite B G hG (siteObject C S hS hXc X.hom) hX

/-- **Stacks 04TK** for an action of a group scheme of the big fppf site written in the slice of
all schemes over `S`: the quotient stack
`AlgebraicGeometry.Stack.quotientStackOfGroupSchemeInSiteOnOver` is an algebraic stack over `S`
as soon as the structure morphism `B ×_S G ⟶ B` of the group algebraic space is smooth. -/
theorem isAlgebraicStack_quotientStackOfGroupSchemeInSiteOnOver_of_isSmooth
    (B : AlgebraicSpaces C S hS)
    (G : BigFppfOver C S hS) (hG : GrpObj ((Space.toSchemeOver C S hS).obj G))
    {X : Over S} (hX : letI := hG; ModObj ((Space.toSchemeOver C S hS).obj G) X)
    (hXc : C.Contains X.left)
    (hsm : Space.IsSmooth C S hS
      (prod.fst : B.obj ⨯ (Space.pointsOnSite C S hS G hG ⋙ forget GrpCat) ⟶ B.obj)) :
    IsAlgebraicStack.{u, w} C S hS
      (quotientStackOfGroupSchemeInSiteOnOver B G hG hX hXc) :=
  isAlgebraicStack_quotientStackOfGroupSchemeInSite_of_isSmooth.{u, w} B G hG
    (siteObject C S hS hXc X.hom) hX hsm

end AlgebraicGeometry.Stack

end
