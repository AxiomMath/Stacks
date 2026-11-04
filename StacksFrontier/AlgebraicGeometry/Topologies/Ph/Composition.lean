module

public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.MorphismOfTopoi
public import StacksCore.Tactic.StacksAttribute

/-!
# Composition of morphisms of big ph topoi

For composable morphisms in a big ph site, the direct and inverse images of the morphism of
topoi attached to the composite are naturally isomorphic to the composites of the
respective images.

## Main definitions

* `AlgebraicGeometry.bigPHMorphism_comp_pushforwardIso`: the comparison of direct images.
* `AlgebraicGeometry.bigPHMorphism_comp_inverseImageIso`: the comparison of inverse images.

## Implementation notes

Both comparisons are assembled from the two image formulas of Stacks 0DBR together with
the compositors `CategoryTheory.Over.pullbackComp` and `CategoryTheory.Over.mapComp` for
base change and postcomposition on slices.  Writing each image as a restriction functor
turns the comparison into the general composition isomorphism for restriction along
continuous site functors.

## References

* [Stacks Project, Tag 0DBS](https://stacks.math.columbia.edu/tag/0DBS)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable (B : BigPHSite.{u}) (X Y Z : B.Schemes)
  (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **Stacks 0DBS.** Direct image for the composite morphism of big ph topoi is naturally
isomorphic to the composite of the direct-image functors. -/
@[stacks 0DBS "direct-image composition"]
public noncomputable def bigPHMorphism_comp_pushforwardIso :
    (bigPHMorphism B X Z (f ≫ g)).pushforward ≅
      (bigPHMorphism B X Y f).pushforward ⋙
      (bigPHMorphism B Y Z g).pushforward := by
  exact
    bigPHMorphismPushforwardIso B X Z (f ≫ g) ≪≫
      (Functor.sheafPushforwardContinuousComp'
        (Over.pullbackComp f g).symm (Type (u + 1))
        (BigPHOver.topology B Z.obj Z.property)
        (BigPHOver.topology B Y.obj Y.property)
        (BigPHOver.topology B X.obj X.property)).symm ≪≫
      Functor.isoWhiskerRight
        (bigPHMorphismPushforwardIso B X Y f).symm
        ((Over.pullback g).sheafPushforwardContinuous (Type (u + 1))
          (BigPHOver.topology B Z.obj Z.property)
          (BigPHOver.topology B Y.obj Y.property)) ≪≫
      Functor.isoWhiskerLeft (bigPHMorphism B X Y f).pushforward
        (bigPHMorphismPushforwardIso B Y Z g).symm

/-- **Stacks 0DBS.** Inverse image for the composite morphism of big ph topoi is naturally
isomorphic to the composite of the inverse-image functors. -/
@[stacks 0DBS "inverse-image composition"]
public noncomputable def bigPHMorphism_comp_inverseImageIso :
    (bigPHMorphism B X Z (f ≫ g)).inverseImage ≅
      (bigPHMorphism B Y Z g).inverseImage ⋙
        (bigPHMorphism B X Y f).inverseImage := by
  exact
    bigPHMorphismInverseImageIso B X Z (f ≫ g) ≪≫
      (Functor.sheafPushforwardContinuousComp'
        (Over.mapComp f g).symm (Type (u + 1))
        (BigPHOver.topology B X.obj X.property)
        (BigPHOver.topology B Y.obj Y.property)
        (BigPHOver.topology B Z.obj Z.property)).symm ≪≫
      Functor.isoWhiskerRight
        (bigPHMorphismInverseImageIso B Y Z g).symm
        ((Over.map f).sheafPushforwardContinuous (Type (u + 1))
          (BigPHOver.topology B X.obj X.property)
          (BigPHOver.topology B Y.obj Y.property)) ≪≫
      Functor.isoWhiskerLeft (bigPHMorphism B Y Z g).inverseImage
        (bigPHMorphismInverseImageIso B X Y f).symm

end AlgebraicGeometry
