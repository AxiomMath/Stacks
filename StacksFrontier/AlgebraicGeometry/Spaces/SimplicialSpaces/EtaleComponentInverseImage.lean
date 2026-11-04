module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleSiteTopoi
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAbelianInverseImageSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DenseSubsiteCohomology
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationComponentInverseImageAb
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringSituationDescentAb

/-!
# Abelian sheaves and cohomology on the components of the small étale site of `U`

Let `a : U → X` be an augmented simplicial algebraic space over a scheme `S`, and let
`a_n : U_n → X` be its augmentation in simplicial degree `n`. The component of degree `n` of the
small étale site `U_étale` of Section 0DE7 is a strict model of `U_{n, spaces, étale}`, and
through the comparison equivalence `AlgebraicGeometry.Space.EtaleComponent.sheafEquiv` the
augmentation of degree `n` is base change along `a_n`
(`AlgebraicGeometry.Space.etaleAugmentationRestrictInverseImageIso`, for sheaves of sets).

This file carries that identification over to abelian sheaves and to cohomology: the abelian
inverse image along the augmentation of degree `n` of an abelian sheaf `𝓕` on `X_étale` is the
pullback `a_n⁻¹𝓕` to `U_{n, étale}`, read on the strict model, and the cohomology of the strict
model of `U_{n, spaces, étale}` is the cohomology of `U_{n, étale}`.

## Main definitions

* `AlgebraicGeometry.Space.EtaleComponent.baseChangeMorphism`: the morphism of topoi
  `Sh(U_{n, étale}) → Sh(X_étale)` of Stacks 03G2 induced by `a_n`.
* `AlgebraicGeometry.Space.EtaleComponent.realizeMorphism`: the comparison equivalence of the
  topos of the component of degree `n` with the spaces-étale topos of `U_n`, as a morphism of
  topoi.

## Main results

* `AlgebraicGeometry.Space.EtaleComponent.componentAugmentationInverseImageRestrictIso`: the
  inverse image along the augmentation of degree `n` is the inverse image along base change by
  `a_n`, followed by restriction along the realization.
* `AlgebraicGeometry.Space.EtaleComponent.componentInverseImageAbIso`: the same identification
  for abelian sheaves.
* `AlgebraicGeometry.Space.EtaleComponent.realizeCohomologyIso`: the cohomology of the component
  of degree `n` of the restriction of an abelian sheaf `𝓖` on `U_{n, spaces, étale}` is
  `H^q(U_{n, étale}, 𝓖)`.

## References

* [Stacks Project, Tag 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.EtaleComponent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : SimplicialObject.Augmented (AlgebraicSpaces B S hS)}

/-- The morphism of topoi `Sh(U_{n, étale}) → Sh(X_étale)` of Stacks 03G2 induced by the
augmentation `a_n : U_n → X`: base change along `a_n` on the spaces-étale sites. -/
abbrev baseChangeMorphism (n : SimplexCategory) :
    MorphismOfTopoi (Sheaf (SpacesEtale.topology B S hS (A.left.obj (op n))) (Type (u + 1)))
      (Sheaf (SpacesEtale.topology B S hS A.right) (Type (u + 1))) :=
  (spacesBaseChange_isMorphismOfSites B S hS (A.hom.app (op n))).morphismOfTopoi

/-- **The inverse image along the augmentation of degree `n` is the pullback along
`a_n : U_n → X`**, read on the strict model of `U_{n, spaces, étale}`: it is the inverse image
along base change by `a_n` followed by restriction along the realization. -/
def componentAugmentationInverseImageRestrictIso (n : SimplexCategory) :
    (SimplicialSiteSituation.Augmentation.componentAugmentation (etaleSituation A)
        (Cat.of (SpacesEtale B S hS A.right)) (SpacesEtale.topology B S hS A.right)
        (etaleAugmentation A) n).inverseImage ≅
      (baseChangeMorphism (A := A) n).inverseImage ⋙
        (sheafEquiv (A := A) n (Type (u + 1))).inverse :=
  (SimplicialSiteSituation.Augmentation.restrictCompInverseImageIso (etaleSituation A)
      (Cat.of (SpacesEtale B S hS A.right)) (SpacesEtale.topology B S hS A.right)
      (etaleAugmentation A) n).symm ≪≫
    etaleAugmentationRestrictInverseImageIso A n

/-- The comparison equivalence of the topos of the component of degree `n` with the
spaces-étale topos of `U_n`, as a morphism of topoi: its inverse image is restriction along the
realization. -/
def realizeMorphism (n : SimplexCategory) :
    MorphismOfTopoi (Sheaf ((etaleSituation A).componentTopology n) (Type (u + 1)))
      (Sheaf (SpacesEtale.topology B S hS (A.left.obj (op n))) (Type (u + 1))) where
  pushforward := (sheafEquiv (A := A) n (Type (u + 1))).functor
  inverseImage := (sheafEquiv (A := A) n (Type (u + 1))).inverse
  adj := (sheafEquiv (A := A) n (Type (u + 1))).symm.toAdjunction
  preservesFiniteLimits := @PreservesLimitsOfSize.preservesFiniteLimits _ _ _ _ _
    (sheafEquiv (A := A) n (Type (u + 1))).toAdjunction.rightAdjoint_preservesLimits.{0, 0}

/-- **The abelian inverse image along the augmentation of degree `n` is the pullback along
`a_n : U_n → X`**, read on the strict model of `U_{n, spaces, étale}`: the abelian inverse image
along base change by `a_n` followed by restriction of abelian sheaves along the realization. -/
def componentInverseImageAbIso (n : SimplexCategory) :
    SimplicialSiteSituation.Augmentation.componentInverseImageAb (etaleSituation A)
        (Cat.of (SpacesEtale B S hS A.right)) (SpacesEtale.topology B S hS A.right)
        (etaleAugmentation A) n ≅
      Sites.abelianInverseImage (baseChangeMorphism (A := A) n) ⋙
        (sheafEquiv (A := A) n AddCommGrpCat.{u + 1}).inverse :=
  StacksTag03LR.abelianInverseImageCompIso (baseChangeMorphism (A := A) n) (realizeMorphism n)
      (SimplicialSiteSituation.Augmentation.componentAugmentation (etaleSituation A)
        (Cat.of (SpacesEtale B S hS A.right)) (SpacesEtale.topology B S hS A.right)
        (etaleAugmentation A) n)
      (componentAugmentationInverseImageRestrictIso n) ≪≫
    Functor.isoWhiskerLeft (Sites.abelianInverseImage (baseChangeMorphism (A := A) n))
      (Sites.abelianInverseImageIsoSheafPushforwardContinuous (realizeFunctor n)
        (precoverage (A := A) n).toGrothendieck
        (SpacesEtale.topology B S hS (A.left.obj (op n))) (realizeMorphism n) (Iso.refl _))

/-- Sheaf cohomology on `U_{n, spaces, étale}` is sheaf cohomology on the strict model of
`U_{n, spaces, étale}` of the restriction along the realization. -/
def realizeHAddEquiv (n : SimplexCategory) (q : ℕ)
    (G : Sheaf (SpacesEtale.topology B S hS (A.left.obj (op n))) AddCommGrpCat.{u + 1}) :
    Sheaf.H.{u + 1} G q ≃+
      Sheaf.H.{u + 1} ((sheafEquiv (A := A) n AddCommGrpCat.{u + 1}).inverse.obj G) q :=
  Stacks.Cohomology.DenseSubsite.hAddEquiv.{u + 1, u + 1} (precoverage (A := A) n).toGrothendieck
    (SpacesEtale.topology B S hS (A.left.obj (op n))) (realizeFunctor n) G q

/-- `realizeHAddEquiv` is natural in the abelian sheaf. -/
theorem realizeHAddEquiv_map (n : SimplexCategory) (q : ℕ)
    {G G' : Sheaf (SpacesEtale.topology B S hS (A.left.obj (op n))) AddCommGrpCat.{u + 1}}
    (f : G ⟶ G') (x : Sheaf.H.{u + 1} G q) :
    realizeHAddEquiv n q G' (Sheaf.H.map f q x) =
      Sheaf.H.map ((sheafEquiv (A := A) n AddCommGrpCat.{u + 1}).inverse.map f) q
        (realizeHAddEquiv n q G x) :=
  Stacks.Cohomology.DenseSubsite.hAddEquiv_map _ _ (realizeFunctor n) f q x

/-- Global sections of abelian sheaves on the component of degree `n` are additive, preserving
binary products. -/
local instance additive_sheafΓ_component (n : SimplexCategory) :
    (Sheaf.Γ ((etaleSituation A).componentTopology n) AddCommGrpCat.{u + 1}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **The cohomology of the component of degree `n` is the cohomology of `U_{n, étale}`**: for an
abelian sheaf `𝓖` on `U_{n, spaces, étale}`, the right derived functors of global sections on
the strict model of `U_{n, spaces, étale}` at the restriction of `𝓖` along the realization are
the sheaf cohomology groups `H^q(U_{n, étale}, 𝓖)`, naturally in `𝓖`. -/
def realizeCohomologyIso (n : SimplexCategory) (q : ℕ) :
    (sheafEquiv (A := A) n AddCommGrpCat.{u + 1}).inverse ⋙
        (Sheaf.Γ ((etaleSituation A).componentTopology n) AddCommGrpCat.{u + 1}).rightDerived q ≅
      Sheaf.functorH.{u + 1, u + 1} (SpacesEtale.topology B S hS (A.left.obj (op n))) q :=
  Functor.isoWhiskerLeft (sheafEquiv (A := A) n AddCommGrpCat.{u + 1}).inverse
      (Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{u + 1, u + 1, u + 1}
        ((etaleSituation A).componentTopology n) q) ≪≫
    NatIso.ofComponents (fun G => (realizeHAddEquiv n q G).symm.toAddCommGrpIso)
      (fun {G G'} f => by
        refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
        change (realizeHAddEquiv n q G').symm
            (Sheaf.H.map.{u + 1} ((sheafEquiv (A := A) n AddCommGrpCat.{u + 1}).inverse.map f)
              q x) =
          Sheaf.H.map.{u + 1} f q ((realizeHAddEquiv n q G).symm x)
        refine (realizeHAddEquiv n q G').injective ?_
        rw [AddEquiv.apply_symm_apply, realizeHAddEquiv_map]
        exact congrArg _ ((realizeHAddEquiv n q G).apply_symm_apply x).symm)

end AlgebraicGeometry.Space.EtaleComponent

end
