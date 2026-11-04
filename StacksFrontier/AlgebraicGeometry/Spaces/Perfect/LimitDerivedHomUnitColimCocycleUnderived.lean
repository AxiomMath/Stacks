module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelPushforwardComparison

/-!
# The underived comparison of inverse images on the models is an adjoint mate

`AlgebraicGeometry.Space.spacesEtaleModelModulesPullbackIso` identifies the inverse image of
`𝒪`-modules along the morphism of models of the ringed spaces-étale sites with the inverse image
along the morphism of small étale ringed topoi of Stacks 03G8, under the equivalences of
Stacks 03G1.  This file records that its component-wise inverse is the **adjoint mate** of the
corresponding comparison `AlgebraicGeometry.Space.spacesEtaleModelModulesPushforwardIso` of the
direct images, as an equation of natural transformations.

## Main results

* `AlgebraicGeometry.Space.spacesEtaleModelModulesPullbackHom_eq`: the comparison of the inverse
  images is the mate of the comparison of the direct images, by its definition.

## Implementation notes

The result is stated as an equation of natural transformations rather than of components, since
unfolding the definitions inside `CategoryTheory.NatTrans.app` is far more expensive; to obtain
the component at an object, rewrite with this equation first.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The comparison of the inverse images of `𝒪`-modules on the spaces-étale models and on the
small étale sites is the adjoint mate of the comparison of the direct images**, by its
definition: `AlgebraicGeometry.Space.spacesEtaleModelModulesPullbackHom` is
`CategoryTheory.Adjunction.mateOfRightIso` of
`AlgebraicGeometry.Space.spacesEtaleModelModulesPushforwardIso` for the adjunction between the
inverse and the direct image on the models and the one on the small étale sites. -/
theorem spacesEtaleModelModulesPullbackHom_eq {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    spacesEtaleModelModulesPullbackHom B S hS f =
      Adjunction.mateOfRightIso (spacesEtaleModelHom B S hS f).pullbackPushforwardAdjunctionTopos
        (smallEtaleModulePullbackModulesAdjunction B S hS f)
        (spacesEtaleModelModulesPushforwardIso B S hS f) :=
  rfl

end AlgebraicGeometry.Space

end
