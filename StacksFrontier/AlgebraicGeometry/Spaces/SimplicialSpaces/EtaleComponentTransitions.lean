module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleComponentSheaves
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleBaseChangeCoherence

/-!
# The transitions of the small étale topos of a simplicial algebraic space

Under the identification `AlgebraicGeometry.Space.EtaleComponent.sheafEquiv` of the sheaves on
the component of degree `n` of `U_étale` with the sheaves on `U_{n, spaces, étale}`, the inverse
image along the transition `f_ψ` of the simplicial site is the spaces-étale inverse image along
`U(ψ) : U_k → U_n` of Stacks 03G2, part (3), as Section 0DE7 of the Stacks project prescribes.

## Main results

* `AlgebraicGeometry.Space.EtaleComponent.transitionPushforwardIso`: the direct images agree.
* `AlgebraicGeometry.Space.EtaleComponent.transitionInverseImageIso`: the inverse images agree.

## References

* [Stacks Project, Tag 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.EtaleComponent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : SimplicialObject.Augmented (AlgebraicSpaces B S hS)}

/-- The identification of sheaves on the component of degree `n` with sheaves on
`U_{n, spaces, étale}`, for sheaves of sets. -/
abbrev sheafEquivType (n : SimplexCategory) :
    Sheaf (precoverage (A := A) n).toGrothendieck (Type (u + 1)) ≌
      Sheaf (SpacesEtale.topology B S hS (A.left.obj (op n))) (Type (u + 1)) :=
  sheafEquiv n (Type (u + 1))

/-- **Section 0DE7.** Under the identifications of the component sheaves with spaces-étale
sheaves, the direct image along the transition `f_ψ` is the spaces-étale direct image along
`U(ψ) : U_k → U_n`. -/
def transitionPushforwardIso {n k : SimplexCategory} (ψ : n ⟶ k) :
    (sheafEquivType (A := A) k).inverse ⋙
        (transition_isMorphismOfSites (A := A) ψ).morphismOfTopoi.pushforward ≅
      spacesEtaleSheafPushforward B S hS (A.left.map ψ.op) ⋙ (sheafEquivType n).inverse :=
  haveI := (transition_isMorphismOfSites (A := A) ψ).isContinuous
  haveI := (spacesBaseChange_isMorphismOfSites B S hS (A.left.map ψ.op)).isContinuous
  haveI : (realizeFunctor (A := A) n ⋙
      (spacesBaseChange B S hS (A.left.map ψ.op)).functor).IsContinuous
      (precoverage n).toGrothendieck (SpacesEtale.topology B S hS (A.left.obj (op k))) :=
    Functor.isContinuous_comp _ _ _ (SpacesEtale.topology B S hS (A.left.obj (op n))) _
  Functor.sheafPushforwardContinuousComp' (transitionRealizeIso ψ) (Type (u + 1)) _ _ _ ≪≫
    (Functor.sheafPushforwardContinuousComp _ _ (Type (u + 1)) _
      (SpacesEtale.topology B S hS (A.left.obj (op n))) _).symm

/-- **Section 0DE7.** Under the identifications of the component sheaves with spaces-étale
sheaves, the inverse image along the transition `f_ψ` of the simplicial site is the spaces-étale
inverse image along `U(ψ) : U_k → U_n` of Stacks 03G2, part (3). -/
def transitionInverseImageIso {n k : SimplexCategory} (ψ : n ⟶ k) :
    (transition_isMorphismOfSites (A := A) ψ).morphismOfTopoi.inverseImage ⋙
        (sheafEquivType k).functor ≅
      (sheafEquivType n).functor ⋙ spacesEtaleInverseImage B S hS (A.left.map ψ.op) :=
  Adjunction.leftAdjointUniq
    ((transition_isMorphismOfSites (A := A) ψ).morphismOfTopoi.adj.comp
      (sheafEquivType k).toAdjunction)
    (((sheafEquivType n).toAdjunction.comp
      (spacesBaseChange_isMorphismOfSites B S hS
        (A.left.map ψ.op)).morphismOfTopoi.adj).ofNatIsoRight
        (transitionPushforwardIso ψ).symm)

/-- The augmentation functor followed by the transition along a vertex `[0] → [n]` and by
realization is base change along `a_n : U_n → X`. -/
def augmentationRealizeIso (n : SimplexCategory) :
    augmentationFunctor (A := A) ⋙ transition (SimplexCategory.const (SimplexCategory.mk 0) n 0) ⋙
        realizeFunctor n ≅ (spacesBaseChange B S hS (A.hom.app (op n))).functor :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {V W} f ↦ by
    have h := congrArg (fun g ↦ g.hom)
      (transition_map_augmentationFunctor (A := A) (SimplexCategory.const _ n 0) f)
    simp only [Functor.comp_map, Iso.refl_hom]
    exact h)

/-- **Section 0DE7.** Under the identification of the component sheaves with spaces-étale
sheaves, the direct image along the augmentation of degree `n` (Stacks 0D70, part (1)) is the
spaces-étale direct image along `a_n : U_n → X`. -/
def componentAugmentationPushforwardIso (n : SimplexCategory) :
    (sheafEquivType (A := A) n).inverse ⋙
        (SimplicialSiteSituation.Augmentation.componentAugmentation
          (etaleSimplicialSite A).situation _ _ (etaleAugmentation A) n).pushforward ≅
      spacesEtaleSheafPushforward B S hS (A.hom.app (op n)) :=
  haveI : (transition (A := A) (SimplexCategory.const (SimplexCategory.mk 0) n 0)).IsContinuous
      (precoverage (SimplexCategory.mk 0)).toGrothendieck (precoverage n).toGrothendieck :=
    (transition_isMorphismOfSites (A := A) (SimplexCategory.const _ n 0)).isContinuous
  haveI : (augmentationFunctor (A := A)).IsContinuous (SpacesEtale.topology B S hS A.right)
      (precoverage (SimplexCategory.mk 0)).toGrothendieck :=
    (augmentationFunctor_isMorphismOfSites (A := A)).isContinuous
  haveI : (spacesBaseChange B S hS (A.hom.app (op n))).functor.IsContinuous
      (SpacesEtale.topology B S hS A.right) (SpacesEtale.topology B S hS (A.left.obj (op n))) :=
    (spacesBaseChange_isMorphismOfSites B S hS (A.hom.app (op n))).isContinuous
  haveI : (transition (A := A) (SimplexCategory.const (SimplexCategory.mk 0) n 0) ⋙
      realizeFunctor n).IsContinuous (precoverage (SimplexCategory.mk 0)).toGrothendieck
      (SpacesEtale.topology B S hS (A.left.obj (op n))) :=
    Functor.isContinuous_comp _ _ (precoverage (SimplexCategory.mk 0)).toGrothendieck
      (precoverage (A := A) n).toGrothendieck _
  haveI : (augmentationFunctor (A := A) ⋙
      transition (SimplexCategory.const (SimplexCategory.mk 0) n 0) ⋙ realizeFunctor n).IsContinuous
      (SpacesEtale.topology B S hS A.right) (SpacesEtale.topology B S hS (A.left.obj (op n))) :=
    Functor.isContinuous_comp _ _ (SpacesEtale.topology B S hS A.right)
      (precoverage (A := A) (SimplexCategory.mk 0)).toGrothendieck _
  Functor.sheafPushforwardContinuousIso (augmentationRealizeIso n) (Type (u + 1))
    (SpacesEtale.topology B S hS A.right) (SpacesEtale.topology B S hS (A.left.obj (op n)))

/-- **Section 0DE7.** Under the identification of the component sheaves with spaces-étale
sheaves, the inverse image along the augmentation of degree `n` (Stacks 0D70, part (1)) is the
spaces-étale inverse image along `a_n : U_n → X` of Stacks 03G2, part (3). -/
def componentAugmentationInverseImageIso (n : SimplexCategory) :
    (SimplicialSiteSituation.Augmentation.componentAugmentation
          (etaleSimplicialSite A).situation _ _ (etaleAugmentation A) n).inverseImage ⋙
        (sheafEquivType n).functor ≅
      spacesEtaleInverseImage B S hS (A.hom.app (op n)) :=
  Adjunction.leftAdjointUniq
    ((SimplicialSiteSituation.Augmentation.componentAugmentation
      (etaleSimplicialSite A).situation _ _ (etaleAugmentation A) n).adj.comp
        (sheafEquivType n).toAdjunction)
    ((spacesBaseChange_isMorphismOfSites B S hS
      (A.hom.app (op n))).morphismOfTopoi.adj.ofNatIsoRight
        (componentAugmentationPushforwardIso n).symm)

end AlgebraicGeometry.Space.EtaleComponent

end
