module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleComponentTransitions
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheaf

/-!
# The topoi of the components of the small étale site of a simplicial algebraic space

Let `a : U → X` be an augmented simplicial algebraic space over a scheme `S`, and let
`U_étale` be its small étale site, the total site of the simplicial site
`n ↦ U_{n, spaces, étale}` (Section 0DE7). The site in degree `n` is a strict model of the
spaces-étale site of `U_n`, whose topos is the spaces-étale topos of `U_n`
(`AlgebraicGeometry.Space.EtaleComponent.sheafEquiv`); through these equivalences the transition
`f_φ` attached to `φ : [m] → [n]` is the morphism of topoi of base change along
`U(φ) : U_n → U_m` (Stacks 03G2), and the augmentation `a_n : Sh(U_{n, étale}) → Sh(X_étale)` of
degree `n` is the morphism of topoi of base change along `a_n : U_n → X`.

This file records the simplicial-site situation of `U_étale` and computes the components of the
inverse image `a⁻¹G` of a sheaf `G` on `X_{spaces, étale}`: they are the pullbacks `a_n⁻¹G`.

## Main definitions

* `AlgebraicGeometry.Space.etaleSituation`: the simplicial-site situation (Stacks 09WE) of the
  small étale site of `U`.
* `AlgebraicGeometry.Space.etaleAugmentationRestrictInverseImageIso`: `a⁻¹G` has components
  `a_n⁻¹G`.

## References

* [Stacks Project, Tag 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (A : SimplicialObject.Augmented (AlgebraicSpaces B S hS))


/-- **Section 0DE7.** The simplicial-site situation of Stacks 09WE given by the small étale site
of an augmented simplicial algebraic space: case (A), the transitions being the base-change
morphisms of sites. Its total site is the site `X_{spaces, étale}` of Lemma 09WC and its topos is
the small étale topos of the simplicial algebraic space. -/
abbrev etaleSituation : SimplicialSiteSituation.{u + 1} :=
  ⟨Sum.inl (etaleSimplicialSite A)⟩


namespace EtaleComponent

variable {A}

/-- Realization is continuous for the topology of the degree-`n` site. -/
instance realizeFunctor_isContinuous (n : SimplexCategory) :
    (realizeFunctor (A := A) n).IsContinuous (precoverage (A := A) n).toGrothendieck
      (SpacesEtale.topology B S hS (A.left.obj (op n))) :=
  Stacks.Sites.isContinuous_toGrothendieck_of_le_comap _ _ _
    (Precoverage.comap_monotone (Precoverage.le_toPrecoverage_toGrothendieck _))

/-- The inverse of `sheafEquiv` is restriction along the realization. -/
lemma sheafEquiv_inverse (n : SimplexCategory) (C : Type*) [Category C]
    [∀ X, HasLimitsOfShape (StructuredArrow X (realizeFunctor (A := A) n).op) C] :
    (sheafEquiv n C).inverse = (realizeFunctor (A := A) n).sheafPushforwardContinuous C
      (precoverage (A := A) n).toGrothendieck
      (SpacesEtale.topology B S hS (A.left.obj (op n))) :=
  rfl

end EtaleComponent

open EtaleComponent in
/-- **The components of `a⁻¹G`.** For a sheaf `G` on `X_{spaces, étale}`, the restriction of
`a⁻¹G` to the degree-`n` site is, through `sheafEquiv`, the inverse image `a_n⁻¹G` along the
morphism of topoi of base change by `a_n : U_n → X`. -/
def etaleAugmentationRestrictInverseImageIso (n : SimplexCategory) :
    (etaleAugmentationMorphism A).inverseImage ⋙ (etaleSituation A).restrict n ≅
      (spacesBaseChange_isMorphismOfSites B S hS (A.hom.app (op n))).morphismOfTopoi.inverseImage ⋙
        (sheafEquiv (A := A) n (Type (u + 1))).inverse :=
  SimplicialSiteSituation.Augmentation.restrictCompInverseImageIso (etaleSituation A)
      (Cat.of (SpacesEtale B S hS A.right)) (SpacesEtale.topology B S hS A.right)
      (etaleAugmentation A) n ≪≫
    Adjunction.leftAdjointUniq
      (SimplicialSiteSituation.Augmentation.componentAugmentation (etaleSituation A)
        (Cat.of (SpacesEtale B S hS A.right)) (SpacesEtale.topology B S hS A.right)
        (etaleAugmentation A) n).adj
      (((spacesBaseChange_isMorphismOfSites B S hS (A.hom.app (op n))).morphismOfTopoi.adj.comp
        (sheafEquiv (A := A) n (Type (u + 1))).symm.toAdjunction).ofNatIsoRight
        ((Functor.isoWhiskerLeft (sheafEquiv (A := A) n (Type (u + 1))).functor
            (componentAugmentationPushforwardIso (A := A) n).symm) ≪≫
          (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (sheafEquiv (A := A) n (Type (u + 1))).unitIso.symm _ ≪≫
          Functor.leftUnitor _))

end AlgebraicGeometry.Space

end
