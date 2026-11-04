module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleBaseChange
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi

/-!
# The morphism of small étale topoi induced by a morphism of algebraic spaces

A morphism `f : X ⟶ Y` of algebraic spaces over `S` induces a morphism of sites by base change
on the spaces-étale sites, hence a morphism of the spaces-étale topoi. The comparison functor
identifies the spaces-étale topos of an algebraic space with its *small* étale topos, the topos of
sheaves on the site of étale scheme charts. Transporting the spaces-étale morphism of topoi along
those two identifications gives the morphism of small étale topoi. Both étale sites of an
algebraic space over a scheme of universe `u` have their objects in `Type (u + 1)`, so the topoi
are those of sheaves of sets valued in `Type (u + 1)`.

## Main definitions

* `MorphismOfTopoi.transport` transports a morphism of topoi along equivalences of its source
  and target.
* `AlgebraicGeometry.Space.smallEtaleToposEquiv` is the equivalence between the spaces-étale
  topos of an algebraic space and its small étale topos, for sheaves of sets in the universe of
  the sites.
* `AlgebraicGeometry.Space.smallToposMorphism` is the induced morphism of small étale topoi.

## Main results

* `AlgebraicGeometry.Space.smallToposMorphism_comparison`: the direct image of
  `AlgebraicGeometry.Space.smallToposMorphism` agrees, through the comparison equivalences, with
  the direct image of the spaces-étale morphism of sites.
* `AlgebraicGeometry.Space.spacesBaseChange_pushforward_comp` and
  `AlgebraicGeometry.Space.smallToposMorphism_comp`: the direct images are compatible with
  composition, and `AlgebraicGeometry.Space.smallToposMorphism_comp_inverseImage` is the
  adjoint mate of the latter, oriented for inverse images.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ v₅ u₅ v₆ u₆

namespace MorphismOfTopoi

variable {E : Type u₁} [Category.{v₁} E] {F : Type u₂} [Category.{v₂} F]
  {G : Type u₃} [Category.{v₃} G] {E' : Type u₄} [Category.{v₄} E']
  {F' : Type u₅} [Category.{v₅} F'] {G' : Type u₆} [Category.{v₆} G']

/-- Transport a morphism of topoi `φ : E → F` along equivalences `E ≌ E'` and `F ≌ F'`: the
direct image is conjugated by the two equivalences and the inverse image by their inverses. -/
noncomputable def transport (φ : MorphismOfTopoi E F) (eE : E ≌ E') (eF : F ≌ F') :
    MorphismOfTopoi E' F' where
  pushforward := eE.inverse ⋙ φ.pushforward ⋙ eF.functor
  inverseImage := eF.inverse ⋙ φ.inverseImage ⋙ eE.functor
  adj := (eF.symm.toAdjunction.comp φ.adj).comp eE.toAdjunction
  preservesFiniteLimits :=
    have := φ.preservesFiniteLimits
    haveI : PreservesFiniteLimits (φ.inverseImage ⋙ eE.functor) :=
      comp_preservesFiniteLimits _ _
    comp_preservesFiniteLimits _ _

/-- The direct image of a transported morphism of topoi agrees with the original one after the
two equivalences. -/
noncomputable def transport_pushforward_comparison (φ : MorphismOfTopoi E F) (eE : E ≌ E')
    (eF : F ≌ F') :
    eE.functor ⋙ (φ.transport eE eF).pushforward ≅ φ.pushforward ⋙ eF.functor :=
  Functor.isoWhiskerRight eE.unitIso.symm (φ.pushforward ⋙ eF.functor) ≪≫
    Functor.leftUnitor _

/-- Transport along equivalences is compatible with composition of morphisms of topoi: the
direct image of the composite of two transports is the direct image of the transport of the
composite. -/
noncomputable def transport_comp_pushforward (φ : MorphismOfTopoi E F)
    (ψ : MorphismOfTopoi F G) (eE : E ≌ E') (eF : F ≌ F') (eG : G ≌ G') :
    (MorphismOfTopoi.comp (ψ.transport eF eG) (φ.transport eE eF)).pushforward ≅
      ((MorphismOfTopoi.comp ψ φ).transport eE eG).pushforward :=
  Functor.isoWhiskerLeft (eE.inverse ⋙ φ.pushforward)
    (Functor.isoWhiskerRight eF.unitIso.symm (ψ.pushforward ⋙ eG.functor))

end MorphismOfTopoi

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The comparison equivalence between the spaces-étale topos of an algebraic space and its small
étale topos, given by restriction along `AlgebraicGeometry.Space.comparisonFunctor`. -/
noncomputable def smallEtaleToposEquiv (X : AlgebraicSpaces B S hS) :
    Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1)) ≌
      Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)) :=
  ((comparisonFunctor B S hS X).sheafPushforwardContinuous (Type (u + 1))
    (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).asEquivalence

/-- The morphism of small étale topoi induced by a morphism `f : X ⟶ Y` of algebraic spaces: the
morphism of spaces-étale topoi of the base-change morphism of sites, transported along the
comparison equivalences `AlgebraicGeometry.Space.smallEtaleToposEquiv`. -/
@[stacks 03G2 "part (3), morphism of small étale topoi"]
noncomputable def smallToposMorphism {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    MorphismOfTopoi
      (Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)))
      (Sheaf (SmallEtale.topology B S hS Y.1) (Type (u + 1))) :=
  ((spacesBaseChange_isMorphismOfSites B S hS f).morphismOfTopoi).transport
    (smallEtaleToposEquiv B S hS X) (smallEtaleToposEquiv B S hS Y)

/-- The small étale direct image agrees, through the comparison equivalences, with the direct
image of the spaces-étale morphism of sites. -/
@[stacks 03G2 "part (3), comparison with the spaces-étale topoi"]
noncomputable def smallToposMorphism_comparison {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    ((comparisonFunctor B S hS X).sheafPushforwardContinuous (Type (u + 1))
          (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)) ⋙
        (smallToposMorphism B S hS f).pushforward ≅
      ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type (u + 1))
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)) ⋙
        (comparisonFunctor B S hS Y).sheafPushforwardContinuous (Type (u + 1))
          (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y) :=
  MorphismOfTopoi.transport_pushforward_comparison _ _ _

/-- The canonical comparison between the composite of the spaces-étale direct images and the
direct image along the composite, induced by the base-change isomorphism
`AlgebraicGeometry.Space.spacesBaseChange_comp`. -/
noncomputable def spacesBaseChange_pushforward_comp {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type (u + 1))
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)) ⋙
      ((spacesBaseChange B S hS g).functor.sheafPushforwardContinuous (Type (u + 1))
        (SpacesEtale.topology B S hS Z) (SpacesEtale.topology B S hS Y)) ≅
      (spacesBaseChange B S hS (f ≫ g)).functor.sheafPushforwardContinuous (Type (u + 1))
        (SpacesEtale.topology B S hS Z) (SpacesEtale.topology B S hS X) :=
  Functor.sheafPushforwardContinuousComp' (spacesBaseChange_comp B S hS f g) (Type (u + 1))
    (SpacesEtale.topology B S hS Z) (SpacesEtale.topology B S hS Y)
    (SpacesEtale.topology B S hS X)

/-- The small étale direct image is compatible with composition: the composite of the morphisms
of topoi of `f` and `g` has the same direct image as the morphism of topoi of `f ≫ g`. -/
@[stacks 03G2 "part (3), compatibility with composition"]
noncomputable def smallToposMorphism_comp {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    (MorphismOfTopoi.comp (smallToposMorphism B S hS g)
        (smallToposMorphism B S hS f)).pushforward ≅
      (smallToposMorphism B S hS (f ≫ g)).pushforward :=
  MorphismOfTopoi.transport_comp_pushforward _ _ (smallEtaleToposEquiv B S hS X)
      (smallEtaleToposEquiv B S hS Y) (smallEtaleToposEquiv B S hS Z) ≪≫
    Functor.isoWhiskerLeft (smallEtaleToposEquiv B S hS X).inverse
      (Functor.isoWhiskerRight (spacesBaseChange_pushforward_comp B S hS f g)
        (smallEtaleToposEquiv B S hS Z).functor)

/-- The inverse-image composition isomorphism, oriented for pullback of sheaves:
`(f ≫ g)⁻¹ ≅ g⁻¹ ⋙ f⁻¹`. It is the adjoint mate of
`AlgebraicGeometry.Space.smallToposMorphism_comp`. -/
@[stacks 03G2 "part (3), inverse-image composition"]
noncomputable def smallToposMorphism_comp_inverseImage {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (smallToposMorphism B S hS (f ≫ g)).inverseImage ≅
      (smallToposMorphism B S hS g).inverseImage ⋙
        (smallToposMorphism B S hS f).inverseImage :=
  Adjunction.leftAdjointUniq (smallToposMorphism B S hS (f ≫ g)).adj
    ((MorphismOfTopoi.comp (smallToposMorphism B S hS g)
      (smallToposMorphism B S hS f)).adj.ofNatIsoRight (smallToposMorphism_comp B S hS f g))

end AlgebraicGeometry.Space

end
