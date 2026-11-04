module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.ActionInSitePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackOfAction

/-!
# The action groupoid of an action on the site, over the base itself

Let `F` be a presheaf of groups acting on a presheaf `P` over the big fppf site over `S`. Over an
algebraic space `B` the action becomes an action of `B ×_S G` on `B ×_S X` in the slice of
presheaves over `B` (`AlgebraicGeometry.Space.objectOverStarModObj`), and Stacks 0444 attaches to
it the action groupoid in algebraic spaces whose quotient stack is `[X/G]`.

When `B` is **the base itself** — `AlgebraicGeometry.Space.terminalSpace`, whose presheaf is the
final presheaf on the site — the two factors `B ×_S G` and `B ×_S X` carry no more information
than `G` and `X`, and this file identifies the object and the arrow presheaves of that action
groupoid with `P` and with `G ⊗ X`, compatibly with the source and the target. The identifications
are:

* on objects, the second projection `B ⨯ P ⟶ P`, an isomorphism because `B` is terminal;
* on arrows, the lax monoidal comparison of `B ⨯ -` followed by that same projection, an
  isomorphism because a monoidal functor's comparison is one.

Under them the source of the action groupoid is the second projection of `G ⊗ X` and its target is
the action morphism — which is what it is to be the action groupoid of `G` acting on `X`.

This is what identifies the pointwise groupoid fibration of the action groupoid with a presheaf of
groupoids described directly by the action, which is the shape Stacks 05YQ compares with the
presheaf `FA_d` of free rank-`d` algebra structures.

## Main definitions

* `AlgebraicGeometry.Space.objectsTerminalIso` and
  `AlgebraicGeometry.Space.arrowsTerminalIso`: the two identifications.

## Main results

* `AlgebraicGeometry.Space.groupoidOfAction_terminal_source` and
  `AlgebraicGeometry.Space.groupoidOfAction_terminal_target`: the source and the target of the
  action groupoid, read through the two identifications.
* `AlgebraicGeometry.Space.arrowsTerminalIso_hom`: the arrow identification, written out as the
  pair of the group component of the first factor and the object component of the second.

## Implementation notes

The source needs no computation at all: `AlgebraicGeometry.Space.groupoidOfAction_source` says the
source of the action groupoid is the second projection of the tensor product in the slice, which
by `CategoryTheory.Over.snd_left` is the second projection of the pullback, so the statement below
holds by `rfl`. The target is the transported action, and that is
`AlgebraicGeometry.Space.smul_objectOverStar_left_comp_snd`.

Both squares are stated by composing with the object identification rather than by conjugating with
it, because the two sides then have the shape the two lemmas of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/GroupSpaces/ActionInSitePoints.lean` already
produce; the identification is an isomorphism, so nothing is lost.

## References

* [Stacks Project, Tag 043Q](https://stacks.math.columbia.edu/tag/043Q)
* [Stacks Project, Tag 0444](https://stacks.math.columbia.edu/tag/0444)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Space

variable (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S)
  (F : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ GrpCat.{u})
  (P : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) [ModObj (F ⋙ forget GrpCat) P]

/-! ### The two identifications -/

/-- The objects of the action groupoid over the base itself are the points of the acted-on
presheaf: the second projection out of the product with the final presheaf. -/
noncomputable abbrev objectsTerminalIso :
    (objectOverStar 𝒞 S hS (terminalSpace 𝒞 S hS).obj P).left ≅ P :=
  terminalSpaceProdIso 𝒞 S hS P

/-- **The arrows of the action groupoid over the base itself are the points of `G ⊗ X`**: the lax
monoidal comparison of `B ⨯ -`, which is an isomorphism because `B ⨯ -` is monoidal, followed by
the second projection out of the product with the final presheaf. -/
noncomputable def arrowsTerminalIso :
    (groupOverStar 𝒞 S hS (terminalSpace 𝒞 S hS).obj F ⊗
        objectOverStar 𝒞 S hS (terminalSpace 𝒞 S hS).obj P).left ≅
      (F ⋙ forget GrpCat) ⊗ P :=
  (Over.forget (terminalSpace 𝒞 S hS).obj).mapIso
      (Functor.Monoidal.μIso (overStar 𝒞 S hS (terminalSpace 𝒞 S hS).obj)
        (F ⋙ forget GrpCat) P) ≪≫
    terminalSpaceProdIso 𝒞 S hS ((F ⋙ forget GrpCat) ⊗ P)

omit [ModObj (F ⋙ forget GrpCat) P] in
/-- **The arrow identification, written out.** It pairs the group component of the first factor of
the pullback with the object component of the second. -/
theorem arrowsTerminalIso_hom :
    (arrowsTerminalIso 𝒞 S hS F P).hom =
      lift (pullback.fst
            ((overStar 𝒞 S hS (terminalSpace 𝒞 S hS).obj).obj (F ⋙ forget GrpCat)).hom
            ((overStar 𝒞 S hS (terminalSpace 𝒞 S hS).obj).obj P).hom ≫ prod.snd)
        (pullback.snd
            ((overStar 𝒞 S hS (terminalSpace 𝒞 S hS).obj).obj (F ⋙ forget GrpCat)).hom
            ((overStar 𝒞 S hS (terminalSpace 𝒞 S hS).obj).obj P).hom ≫ prod.snd) :=
  mu_overStar_left_comp_snd 𝒞 S hS (terminalSpace 𝒞 S hS).obj (F ⋙ forget GrpCat) P

variable (hG : IsAlgebraicSpace 𝒞 S hS
    (groupOverStar 𝒞 S hS (terminalSpace 𝒞 S hS).obj F).left)
  (hX : IsAlgebraicSpace 𝒞 S hS
    (objectOverStar 𝒞 S hS (terminalSpace 𝒞 S hS).obj P).left)

/-! ### Source and target -/

/-- The source of the action groupoid over the base itself is the second projection of the
pullback. -/
theorem groupoidOfAction_terminal_source_eq :
    (groupoidOfAction (terminalSpace 𝒞 S hS)
        (groupOverStar 𝒞 S hS (terminalSpace 𝒞 S hS).obj F)
        (objectOverStar 𝒞 S hS (terminalSpace 𝒞 S hS).obj P)
        hG hX).groupoid.toGroupoidInFunctors.source =
      pullback.snd
        ((overStar 𝒞 S hS (terminalSpace 𝒞 S hS).obj).obj (F ⋙ forget GrpCat)).hom
        ((overStar 𝒞 S hS (terminalSpace 𝒞 S hS).obj).obj P).hom := rfl

/-- The target of the action groupoid over the base itself is the transported action. -/
theorem groupoidOfAction_terminal_target_eq :
    (groupoidOfAction (terminalSpace 𝒞 S hS)
        (groupOverStar 𝒞 S hS (terminalSpace 𝒞 S hS).obj F)
        (objectOverStar 𝒞 S hS (terminalSpace 𝒞 S hS).obj P)
        hG hX).groupoid.toGroupoidInFunctors.target =
      γ[groupOverStar 𝒞 S hS (terminalSpace 𝒞 S hS).obj F,
        objectOverStar 𝒞 S hS (terminalSpace 𝒞 S hS).obj P].left := rfl

/-- **The source of the action groupoid over the base itself is the second projection of
`G ⊗ X`**, read through the two identifications. -/
theorem groupoidOfAction_terminal_source :
    (groupoidOfAction (terminalSpace 𝒞 S hS)
          (groupOverStar 𝒞 S hS (terminalSpace 𝒞 S hS).obj F)
          (objectOverStar 𝒞 S hS (terminalSpace 𝒞 S hS).obj P)
          hG hX).groupoid.toGroupoidInFunctors.source ≫
        (objectsTerminalIso 𝒞 S hS P).hom =
      (arrowsTerminalIso 𝒞 S hS F P).hom ≫ snd (F ⋙ forget GrpCat) P :=
  ((congrArg (fun z : _ ⟶ (F ⋙ forget GrpCat) ⊗ P => z ≫ snd (F ⋙ forget GrpCat) P)
      (arrowsTerminalIso_hom 𝒞 S hS F P)).trans (lift_snd _ _)).symm

/-- **The target of the action groupoid over the base itself is the action morphism**, read
through the two identifications. -/
theorem groupoidOfAction_terminal_target :
    (groupoidOfAction (terminalSpace 𝒞 S hS)
          (groupOverStar 𝒞 S hS (terminalSpace 𝒞 S hS).obj F)
          (objectOverStar 𝒞 S hS (terminalSpace 𝒞 S hS).obj P)
          hG hX).groupoid.toGroupoidInFunctors.target ≫
        (objectsTerminalIso 𝒞 S hS P).hom =
      (arrowsTerminalIso 𝒞 S hS F P).hom ≫ γ[F ⋙ forget GrpCat, P] :=
  (smul_objectOverStar_left_comp_snd 𝒞 S hS (terminalSpace 𝒞 S hS).obj F P).trans
    (congrArg (fun z : _ ⟶ (F ⋙ forget GrpCat) ⊗ P => z ≫ γ[F ⋙ forget GrpCat, P])
      (arrowsTerminalIso_hom 𝒞 S hS F P).symm)

end AlgebraicGeometry.Space

end
