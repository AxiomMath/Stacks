module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleBaseChangeCoherence
public import StacksFrontier.CategoryTheory.Bicategory.ConjugateCompPentagon

/-!
# Coherence of the small étale topos morphisms

A morphism `f : X ⟶ Y` of algebraic spaces over `S` has a morphism of small étale topoi, together
with an isomorphism comparing the morphism attached to a composite with the composite of the
morphisms attached to the factors (Stacks 03G2, part (3)). For three composable morphisms these
comparison isomorphisms satisfy the pentagon, both on direct images and on inverse images.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleSheafPushforward` and
  `AlgebraicGeometry.Space.smallEtaleSheafInverseImage`: the direct and inverse images of small
  étale sheaves along a morphism of algebraic spaces, i.e. the two halves of the morphism of
  topoi of Stacks 03G2 part (3);
* `AlgebraicGeometry.Space.smallEtaleComparison`: the comparison of Stacks 03G1 on sheaves.

## Main results

* `AlgebraicGeometry.Space.smallToposMorphism_pushforward_comp_assoc`: the pentagon on direct
  images of small étale sheaves;
* `AlgebraicGeometry.Space.smallToposMorphism_comp_inverseImage_assoc`: the pentagon on inverse
  images;
* `AlgebraicGeometry.Space.smallToposMorphism_comp_inverseImage_eq_lComp`: the inverse-image
  comparison of part (3) is the adjoint mate of the direct-image one.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The category of sheaves of sets on the small étale site of an algebraic space, as an object
of `Cat`. -/
noncomputable abbrev smallEtaleSheafCat (X : AlgebraicSpaces B S hS) : Cat :=
  Cat.of (Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)))

/-- The comparison of Stacks 03G1 on sheaves: it identifies the spaces-étale topos of an
algebraic space with its small étale topos. -/
noncomputable abbrev smallEtaleComparison (X : AlgebraicSpaces B S hS) :
    Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1)) ⥤
      Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)) :=
  (comparisonFunctor B S hS X).sheafPushforwardContinuous
    (Type (u + 1)) (SmallEtale.topology B S hS X.1)
    (SpacesEtale.topology B S hS X)

/-- The direct image of small étale sheaves along a morphism of algebraic spaces: the direct
image of the morphism of topoi of Stacks 03G2 part (3). -/
noncomputable abbrev smallEtaleSheafPushforward {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    smallEtaleSheafCat B S hS X ⥤ smallEtaleSheafCat B S hS Y :=
  (smallToposMorphism B S hS f).pushforward

/-- The inverse image of small étale sheaves along a morphism of algebraic spaces: the inverse
image of the morphism of topoi of Stacks 03G2 part (3). -/
noncomputable abbrev smallEtaleSheafInverseImage {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    smallEtaleSheafCat B S hS Y ⥤ smallEtaleSheafCat B S hS X :=
  (smallToposMorphism B S hS f).inverseImage

/-- The adjunction between the small étale inverse and direct images. -/
noncomputable abbrev smallEtaleSheafAdjunction {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    smallEtaleSheafInverseImage B S hS f ⊣ smallEtaleSheafPushforward B S hS f :=
  (smallToposMorphism B S hS f).adj

/-- The composition comparison of Stacks 03G2 part (3) on direct images, from the direct image
along `f ≫ g` to the composite of the direct images along `f` and `g`. -/
noncomputable abbrev smallEtaleSheafPushforwardComp {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallEtaleSheafPushforward B S hS (f ≫ g) ≅
      smallEtaleSheafPushforward B S hS f ⋙ smallEtaleSheafPushforward B S hS g :=
  (smallToposMorphism_comp B S hS f g).symm

/-- The pentagon for the composition comparison on direct images of small étale sheaves: the two
ways of comparing the direct image along `f ≫ g ≫ h` with the threefold iterated direct image
agree. -/
theorem smallToposMorphism_pushforward_comp_assoc {X Y Z W : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    (smallEtaleSheafPushforwardComp B S hS (f ≫ g) h).hom ≫
        Functor.whiskerRight (smallEtaleSheafPushforwardComp B S hS f g).hom
            (smallEtaleSheafPushforward B S hS h) ≫
          (Functor.associator (smallEtaleSheafPushforward B S hS f)
              (smallEtaleSheafPushforward B S hS g)
              (smallEtaleSheafPushforward B S hS h)).hom ≫
            Functor.whiskerLeft (smallEtaleSheafPushforward B S hS f)
                (smallEtaleSheafPushforwardComp B S hS g h).inv ≫
              (smallEtaleSheafPushforwardComp B S hS f (g ≫ h)).inv =
      eqToHom (congrArg (fun k : X ⟶ W => smallEtaleSheafPushforward B S hS k)
        (Category.assoc f g h)) := by
  have key := pentagon_of_conjugateComp
    (fun X : AlgebraicSpaces B S hS =>
      Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1)))
    (fun X : AlgebraicSpaces B S hS =>
      Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)))
    (fun {_ _} f => spacesEtaleSheafPushforward B S hS f)
    (fun {_ _} f => smallEtaleSheafPushforward B S hS f)
    (fun X => smallEtaleComparison B S hS X)
    (fun {_ _} f => smallToposMorphism_comparison B S hS f)
    (fun {_ _ _} f g => spacesEtaleSheafPushforwardComp B S hS f g)
    (fun {_ _ _} f g => smallEtaleSheafPushforwardComp B S hS f g)
    (fun {_ _ _} f g F => smallToposMorphism_comp_comparison B S hS f g F)
    (fun {_ _ _ _} f g h => spacesBaseChange_pushforward_comp_assoc B S hS f g h)
    f g h
  apply ((Functor.whiskeringLeft
    (Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1)))
    (Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)))
    (Sheaf (SmallEtale.topology B S hS W.1) (Type (u + 1)))).obj
      (smallEtaleComparison B S hS X)).map_injective
  exact NatTrans.ext (funext key)

/-- The inverse-image composition isomorphism of Stacks 03G2 part (3) is the adjoint mate of
the direct-image one, i.e. it is `CategoryTheory.LocallyDiscrete.lComp` for the system of small
étale direct images. -/
theorem smallToposMorphism_comp_inverseImage_eq_lComp {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    LocallyDiscrete.lComp (smallEtaleSheafCat B S hS)
        (fun {_ _} f => smallEtaleSheafInverseImage B S hS f)
        (fun {_ _} f => smallEtaleSheafPushforward B S hS f)
        (fun {_ _} f => smallEtaleSheafAdjunction B S hS f)
        (fun {_ _ _} f g => smallEtaleSheafPushforwardComp B S hS f g) f g =
      smallToposMorphism_comp_inverseImage B S hS f g := by
  refine Iso.ext ?_
  rw [LocallyDiscrete.lComp_hom]
  exact (leftAdjointUniq_ofNatIsoRight_eq
    ((smallToposMorphism B S hS g).comp (smallToposMorphism B S hS f)).adj
    (smallToposMorphism B S hS (f ≫ g)).adj
    (smallToposMorphism_comp B S hS f g)).symm

/-- The pentagon for the composition comparison on inverse images of small étale sheaves: the two
ways of comparing the inverse image along `f ≫ g ≫ h` with the threefold iterated inverse image
agree. -/
theorem smallToposMorphism_comp_inverseImage_assoc {X Y Z W : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    (smallToposMorphism_comp_inverseImage B S hS f (g ≫ h)).hom ≫
        Functor.whiskerRight (smallToposMorphism_comp_inverseImage B S hS g h).hom
            (smallEtaleSheafInverseImage B S hS f) ≫
          (Functor.associator (smallEtaleSheafInverseImage B S hS h)
              (smallEtaleSheafInverseImage B S hS g)
              (smallEtaleSheafInverseImage B S hS f)).hom ≫
            Functor.whiskerLeft (smallEtaleSheafInverseImage B S hS h)
                (smallToposMorphism_comp_inverseImage B S hS f g).inv ≫
              (smallToposMorphism_comp_inverseImage B S hS (f ≫ g) h).inv =
      eqToHom (congrArg (fun k : X ⟶ W => smallEtaleSheafInverseImage B S hS k)
        (Category.assoc f g h).symm) := by
  rw [← smallToposMorphism_comp_inverseImage_eq_lComp B S hS f (g ≫ h),
    ← smallToposMorphism_comp_inverseImage_eq_lComp B S hS g h,
    ← smallToposMorphism_comp_inverseImage_eq_lComp B S hS f g,
    ← smallToposMorphism_comp_inverseImage_eq_lComp B S hS (f ≫ g) h]
  exact LocallyDiscrete.lComp_assoc (smallEtaleSheafCat B S hS)
    (fun {_ _} f => smallEtaleSheafInverseImage B S hS f)
    (fun {_ _} f => smallEtaleSheafPushforward B S hS f)
    (fun {_ _} f => smallEtaleSheafAdjunction B S hS f)
    (fun {_ _ _} f g => smallEtaleSheafPushforwardComp B S hS f g)
    (fun {_ _ _ _} f g h => smallToposMorphism_pushforward_comp_assoc B S hS f g h) f g h

end AlgebraicGeometry.Space

end
