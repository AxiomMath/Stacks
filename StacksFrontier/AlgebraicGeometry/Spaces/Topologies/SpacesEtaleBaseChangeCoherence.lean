module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposMorphism
public import StacksFrontier.CategoryTheory.Bicategory.LeftAdjointPseudofunctor
public import StacksFrontier.CategoryTheory.Bicategory.OverPullbackPseudofunctor
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi

/-!
# Coherence of spaces-étale base change: the pentagon, over all algebraic spaces

Stacks 03G2 attaches to a morphism `f : X ⟶ Y` of algebraic spaces over `S` a base-change
functor on the spaces-étale sites (part (1)), a composition isomorphism for it (part (2)), and
hence a morphism of the spaces-étale topoi. Parts (1) and (2) are the object and arrow data of
a pseudofunctor on the category of all algebraic spaces over `S`; what they do not include is
the coherence between the composition isomorphisms of three composable morphisms. This file
proves that coherence — the pentagon — at all three levels where it is needed: on the sites,
on the direct images of sheaves, and on the inverse images.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleInverseImage`: the inverse image of spaces-étale sheaves
  along a morphism of algebraic spaces, i.e. the inverse image of the morphism of topoi of
  Stacks 03G2 part (3) at the level of the spaces-étale sites;
* `AlgebraicGeometry.Space.spacesEtaleInverseImage_comp`: its composition isomorphism, the
  adjoint mate of the direct-image one.

## Main results

* `AlgebraicGeometry.Space.spacesBaseChange_comp_pentagon`: the pentagon on the sites;
* `AlgebraicGeometry.Space.spacesBaseChange_pushforward_comp_assoc`: the pentagon on direct
  images of sheaves;
* `AlgebraicGeometry.Space.spacesEtaleInverseImage_comp_assoc`: the pentagon on inverse images.

## Implementation notes

Nothing here is tagged: the pentagon is not among the assertions of Stacks 03G2.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The pentagon for the base-change functors of Stacks 03G2 part (1) on the spaces-étale
sites: the two ways of comparing base change along `f ≫ g ≫ h` with the threefold iterated
base change agree. -/
theorem spacesBaseChange_comp_pentagon {X Y Z W : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    (spacesBaseChange_comp B S hS f (g ≫ h)).inv ≫
        Functor.whiskerRight (spacesBaseChange_comp B S hS g h).inv
            (spacesBaseChange B S hS f).functor ≫
          (Functor.associator (spacesBaseChange B S hS h).functor
              (spacesBaseChange B S hS g).functor (spacesBaseChange B S hS f).functor).hom ≫
            Functor.whiskerLeft (spacesBaseChange B S hS h).functor
                (spacesBaseChange_comp B S hS f g).hom ≫
              (spacesBaseChange_comp B S hS (f ≫ g) h).hom =
      eqToHom (congrArg (fun k : X ⟶ W => (spacesBaseChange B S hS k).functor)
        (Category.assoc f g h).symm) := by
  refine NatTrans.ext (funext fun V => ?_)
  apply ObjectProperty.hom_ext
  have key := NatTrans.congr_app (Over.pullbackComp_assoc h g f) V.obj
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, eqToHom_app] at key
  dsimp only [spacesBaseChange_comp]
  exact key

/-- The category of sheaves of sets on the spaces-étale site of an algebraic space, as an
object of `Cat`. -/
noncomputable abbrev spacesEtaleSheafCat (X : AlgebraicSpaces B S hS) : Cat :=
  Cat.of (Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1)))

/-- The direct image of spaces-étale sheaves along a morphism of algebraic spaces, covariant
in the morphism. -/
noncomputable abbrev spacesEtaleSheafPushforward {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    spacesEtaleSheafCat B S hS X ⥤ spacesEtaleSheafCat B S hS Y :=
  letI := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
  (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous
    (Type (u + 1)) (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)

/-- The inverse image of spaces-étale sheaves along a morphism of algebraic spaces,
contravariant in the morphism: the inverse image of the morphism of topoi of Stacks 03G2
part (3), before the comparison of Stacks 03G1 with the small étale site. -/
noncomputable abbrev spacesEtaleInverseImage {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    spacesEtaleSheafCat B S hS Y ⥤ spacesEtaleSheafCat B S hS X :=
  (spacesBaseChange_isMorphismOfSites B S hS f).morphismOfTopoi.inverseImage

/-- The adjunction between the spaces-étale inverse and direct images. -/
noncomputable abbrev spacesEtaleAdjunction {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    spacesEtaleInverseImage B S hS f ⊣ spacesEtaleSheafPushforward B S hS f :=
  (spacesBaseChange_isMorphismOfSites B S hS f).morphismOfTopoi.adj

/-- The composition isomorphism on direct images of spaces-étale sheaves, from the direct image
along `f ≫ g` to the composite of the direct images along `f` and `g`. -/
noncomputable abbrev spacesEtaleSheafPushforwardComp {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    spacesEtaleSheafPushforward B S hS (f ≫ g) ≅
      spacesEtaleSheafPushforward B S hS f ⋙ spacesEtaleSheafPushforward B S hS g :=
  (spacesBaseChange_pushforward_comp B S hS f g).symm

/-- The sheaf-level composition comparison is precomposition with the site-level one. -/
theorem spacesBaseChange_pushforward_comp_hom_app_hom_app
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : spacesEtaleSheafCat B S hS X) (V : (SpacesEtale B S hS Z)ᵒᵖ) :
    ((spacesEtaleSheafPushforwardComp B S hS f g).hom.app M).hom.app V =
      M.obj.map ((spacesBaseChange_comp B S hS f g).hom.app V.unop).op :=
  rfl

/-- The inverse of the sheaf-level composition comparison is precomposition with the inverse
of the site-level one. -/
theorem spacesBaseChange_pushforward_comp_inv_app_hom_app
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : spacesEtaleSheafCat B S hS X) (V : (SpacesEtale B S hS Z)ᵒᵖ) :
    ((spacesEtaleSheafPushforwardComp B S hS f g).inv.app M).hom.app V =
      M.obj.map ((spacesBaseChange_comp B S hS f g).inv.app V.unop).op :=
  rfl

/-- The pentagon for the composition comparison on direct images of spaces-étale sheaves. -/
theorem spacesBaseChange_pushforward_comp_assoc {X Y Z W : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    (spacesEtaleSheafPushforwardComp B S hS (f ≫ g) h).hom ≫
        Functor.whiskerRight (spacesEtaleSheafPushforwardComp B S hS f g).hom
            (spacesEtaleSheafPushforward B S hS h) ≫
          (Functor.associator (spacesEtaleSheafPushforward B S hS f)
              (spacesEtaleSheafPushforward B S hS g)
              (spacesEtaleSheafPushforward B S hS h)).hom ≫
            Functor.whiskerLeft (spacesEtaleSheafPushforward B S hS f)
                (spacesEtaleSheafPushforwardComp B S hS g h).inv ≫
              (spacesEtaleSheafPushforwardComp B S hS f (g ≫ h)).inv =
      eqToHom (congrArg (fun k : X ⟶ W => spacesEtaleSheafPushforward B S hS k)
        (Category.assoc f g h)) := by
  refine NatTrans.ext (funext fun M => ?_)
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun V => ?_)
  have key := NatTrans.congr_app (spacesBaseChange_comp_pentagon B S hS f g h) V.unop
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, eqToHom_app, Category.id_comp] at key ⊢
  have h2 := (congrArg (fun t => M.obj.map (Quiver.Hom.op t)) key).trans (M.obj.map_id _)
  simp only [op_comp, CategoryTheory.Functor.map_comp, Category.assoc] at h2
  exact h2

/-- The composition comparison on the spaces-étale inverse images: the adjoint mate of the
one for the direct images. -/
noncomputable abbrev spacesEtaleInverseImage_comp {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    spacesEtaleInverseImage B S hS (f ≫ g) ≅
      spacesEtaleInverseImage B S hS g ⋙ spacesEtaleInverseImage B S hS f :=
  LocallyDiscrete.lComp (spacesEtaleSheafCat B S hS)
    (fun {_ _} f => spacesEtaleInverseImage B S hS f)
    (fun {_ _} f => spacesEtaleSheafPushforward B S hS f)
    (fun {_ _} f => spacesEtaleAdjunction B S hS f)
    (fun {_ _ _} f g => spacesEtaleSheafPushforwardComp B S hS f g) f g

/-- **The pentagon for the inverse images of spaces-étale sheaves**, over all algebraic spaces
over `S`: the two ways of comparing the inverse image along `f ≫ g ≫ h` with the threefold
iterated inverse image agree. -/
theorem spacesEtaleInverseImage_comp_assoc {X Y Z W : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    (spacesEtaleInverseImage_comp B S hS f (g ≫ h)).hom ≫
        Functor.whiskerRight (spacesEtaleInverseImage_comp B S hS g h).hom
            (spacesEtaleInverseImage B S hS f) ≫
          (Functor.associator (spacesEtaleInverseImage B S hS h)
              (spacesEtaleInverseImage B S hS g)
              (spacesEtaleInverseImage B S hS f)).hom ≫
            Functor.whiskerLeft (spacesEtaleInverseImage B S hS h)
                (spacesEtaleInverseImage_comp B S hS f g).inv ≫
              (spacesEtaleInverseImage_comp B S hS (f ≫ g) h).inv =
      eqToHom (congrArg (fun k : X ⟶ W => spacesEtaleInverseImage B S hS k)
        (Category.assoc f g h).symm) :=
  LocallyDiscrete.lComp_assoc (spacesEtaleSheafCat B S hS)
    (fun {_ _} f => spacesEtaleInverseImage B S hS f)
    (fun {_ _} f => spacesEtaleSheafPushforward B S hS f)
    (fun {_ _} f => spacesEtaleAdjunction B S hS f)
    (fun {_ _ _} f g => spacesEtaleSheafPushforwardComp B S hS f g)
    (fun {_ _ _ _} f g h => spacesBaseChange_pushforward_comp_assoc B S hS f g h) f g h

end AlgebraicGeometry.Space

end
