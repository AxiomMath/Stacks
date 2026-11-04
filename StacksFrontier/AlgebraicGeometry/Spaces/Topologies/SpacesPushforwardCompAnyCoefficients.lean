module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmallEtaleBaseChangeMate
public import StacksFrontier.CategoryTheory.Sites.PushforwardContinuousCalculus

/-!
# Composition comparisons of spaces-étale direct images, for sheaves in any category

`AlgebraicGeometry.Space.spacesBaseChange_pushforward_comp` compares the composite of two
spaces-étale direct images with the direct image along the composite, and
`AlgebraicGeometry.Space.spacesPushforwardCompSquare` compares the two composite direct images
around a commuting square; both are stated for sheaves of sets. This file states them for sheaves
with values in an arbitrary category `A`, by the same formulas. At `A = Type (u + 1)` they are the
set-valued comparisons by definition.

## Main definitions

* `AlgebraicGeometry.Space.spacesBaseChange_pushforward_comp_anyCoefficients`: the composition
  comparison of direct images.
* `AlgebraicGeometry.Space.spacesPushforwardCompSquare_anyCoefficients`: the comparison of the two
  composite direct images around a commuting square, and
  `AlgebraicGeometry.Space.spacesPushforwardCompSquare_anyCoefficients_eq`, its description as
  restriction along the comparison of the two composites of base change on the sites.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The comparison between the composite of two spaces-étale direct images and the direct image
along the composite, for sheaves with values in any category `A`, induced by the
projection-compatible base-change isomorphism of Stacks 03G2, part (2). -/
def spacesBaseChange_pushforward_comp_anyCoefficients {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) (A : Type*) [Category* A] :
    ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous A
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)) ⋙
      ((spacesBaseChange B S hS g).functor.sheafPushforwardContinuous A
        (SpacesEtale.topology B S hS Z) (SpacesEtale.topology B S hS Y)) ≅
      (spacesBaseChange B S hS (f ≫ g)).functor.sheafPushforwardContinuous A
        (SpacesEtale.topology B S hS Z) (SpacesEtale.topology B S hS X) :=
  Functor.sheafPushforwardContinuousComp' (spacesBaseChange_comp B S hS f g) A
    (SpacesEtale.topology B S hS Z) (SpacesEtale.topology B S hS Y)
    (SpacesEtale.topology B S hS X)

variable {X Y X' Y' : AlgebraicSpaces B S hS}
  (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- The comparison of the two composite direct images of a commuting square on the spaces-étale
topoi, for sheaves with values in any category `A`, assembled from the composition comparisons of
direct images on the two diagonals. -/
def spacesPushforwardCompSquare_anyCoefficients (w : i ≫ f = f' ≫ g) (A : Type*) [Category* A] :
    (spacesBaseChange B S hS i).functor.sheafPushforwardContinuous A
        (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS X') ⋙
      (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous A
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⟶
    (spacesBaseChange B S hS f').functor.sheafPushforwardContinuous A
        (SpacesEtale.topology B S hS Y') (SpacesEtale.topology B S hS X') ⋙
      (spacesBaseChange B S hS g).functor.sheafPushforwardContinuous A
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS Y') :=
  (spacesBaseChange_pushforward_comp_anyCoefficients B S hS i f A).hom ≫
    eqToHom (congrArg (fun k : X' ⟶ Y =>
      (spacesBaseChange B S hS k).functor.sheafPushforwardContinuous A
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X')) w) ≫
    (spacesBaseChange_pushforward_comp_anyCoefficients B S hS f' g A).inv

/-- At sheaves of sets, the comparison of the two composite direct images is
`AlgebraicGeometry.Space.spacesPushforwardCompSquare`. -/
theorem spacesPushforwardCompSquare_anyCoefficients_type (w : i ≫ f = f' ≫ g) :
    spacesPushforwardCompSquare_anyCoefficients B S hS i f' f g w (Type (u + 1)) =
      spacesPushforwardCompSquare B S hS i f' f g w :=
  rfl

/-- The comparison of the two composite direct images is the restriction to sheaves of the
comparison of the two composites of base change on the sites, for sheaves with values in any
category. -/
theorem spacesPushforwardCompSquare_anyCoefficients_eq (w : i ≫ f = f' ≫ g) (A : Type*)
    [Category* A] :
    letI := Functor.isContinuous_comp (spacesBaseChange B S hS g).functor
      (spacesBaseChange B S hS f').functor
      (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS Y')
      (SpacesEtale.topology B S hS X')
    letI := Functor.isContinuous_comp (spacesBaseChange B S hS f).functor
      (spacesBaseChange B S hS i).functor
      (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)
      (SpacesEtale.topology B S hS X')
    spacesPushforwardCompSquare_anyCoefficients B S hS i f' f g w A =
      Functor.sheafPushforwardContinuousNatTrans
        (spacesBaseChangeCompSquare B S hS i f' f g w) A
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X') := by
  let := Functor.isContinuous_comp (spacesBaseChange B S hS g).functor
    (spacesBaseChange B S hS f').functor
    (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS Y')
    (SpacesEtale.topology B S hS X')
  let := Functor.isContinuous_comp (spacesBaseChange B S hS f).functor
    (spacesBaseChange B S hS i).functor
    (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)
    (SpacesEtale.topology B S hS X')
  rw [spacesPushforwardCompSquare_anyCoefficients,
    spacesBaseChange_pushforward_comp_anyCoefficients,
    spacesBaseChange_pushforward_comp_anyCoefficients,
    Functor.sheafPushforwardContinuousComp'_hom_eq,
    Functor.sheafPushforwardContinuousComp'_inv_eq, spacesBaseChangeCompSquare,
    Functor.sheafPushforwardContinuousNatTrans_comp,
    Functor.sheafPushforwardContinuousNatTrans_comp,
    Functor.sheafPushforwardContinuousNatTrans_eqToHom, Category.assoc]
  rfl

end AlgebraicGeometry.Space

end
