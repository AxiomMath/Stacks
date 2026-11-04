module
import StacksCore.Tactic.StacksAttribute

public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationForkLimit
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationMorphism

/-!
# The direct image of the total augmentation is an equalizer

Let `S` be a simplicial-site situation, in either of its two cases, and `a` an augmentation of
`S` towards a site `(D, K)`. For a sheaf `F` on the total site write `F_n` for its restriction to
the component of simplicial degree `n` and `a_n` for the morphism of topoi of that degree. Each
map `φ : [0] ⟶ [1]` gives a map `a_{0,*} F_0 ⟶ a_{1,*} F_1`: the direct image along `a_0` of the
transition `F_0 ⟶ f_{φ,*} F_1` of `F`, followed by the identification
`a_{0,*} f_{φ,*} = a_{1,*}`. This file shows that the direct image `a_* F` along the total
augmentation is the equalizer of the two maps so obtained.

The direct image of the total augmentation is the limit over the simplex category of the
cosimplicial sheaf `n ↦ a_{n,*} F_n`, and the limit of any cosimplicial object is the equalizer of
its two maps in degrees `0 ⇉ 1`, because any two vertices of a simplex are the two ends of an
edge.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.Augmentation.vertexPushforwardMap`: the map
  `a_{0,*} F_0 ⟶ a_{1,*} F_1` attached to a vertex of the one-simplex.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.totalPushforwardFork`: the fork of `a_* F`
  over the two such maps.

## Main results

* `CategoryTheory.SimplicialSiteSituation.Augmentation.totalPushforwardForkIsLimit`: **Stacks
  0D70, compatibility (3).** That fork is a limit fork.

## References

* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory

namespace SimplicialSiteSituation

namespace Augmentation

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K)

/-- The map `a_{0,*} F_0 ⟶ a_{1,*} F_1` attached to the vertex `i` of the one-simplex: the direct
image along the augmentation of degree zero of the transition of `F` along the map
`[0] ⟶ [1]` with value `i`, followed by the identification of the direct images of the
augmentations of the two degrees. -/
def vertexPushforwardMap (F : Sheaf S.totalTopology (Type u)) (i : Fin 2) :
    (componentAugmentation S D K a (SimplexCategory.mk 0)).pushforward.obj
        ((S.restrict (SimplexCategory.mk 0)).obj F) ⟶
      (componentAugmentation S D K a (SimplexCategory.mk 1)).pushforward.obj
        ((S.restrict (SimplexCategory.mk 1)).obj F) :=
  (componentPushforwardTransition S D K a
    (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) i)).app F

/-- The map attached to a vertex of the one-simplex is the direct image of the transition of `F`
followed by the identification of the direct images of the augmentations of the two degrees. -/
theorem vertexPushforwardMap_eq (F : Sheaf S.totalTopology (Type u)) (i : Fin 2) :
    vertexPushforwardMap S D K a F i =
      (componentAugmentation S D K a (SimplexCategory.mk 0)).pushforward.map
          ((S.restrictTransition
            (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) i)).app F) ≫
        (transitionPushforwardIso S D K a
          (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) i)).hom.app
          ((S.restrict (SimplexCategory.mk 1)).obj F) :=
  rfl

/-- The fork of the direct image `a_* F` along the total augmentation over the two maps
`a_{0,*} F_0 ⟶ a_{1,*} F_1`; its leg is the projection of the limit onto degree zero. -/
def totalPushforwardFork (F : Sheaf S.totalTopology (Type u)) :
    Fork (vertexPushforwardMap S D K a F 0) (vertexPushforwardMap S D K a F 1) :=
  Fork.ofι (P := (totalMorphismOfTopoi S D K a).pushforward.obj F)
    (pushforwardProjection S D K a F (SimplexCategory.mk 0))
    (CosimplicialObject.cone_condition (pushforwardDiagram S D K a F)
      (limit.cone (pushforwardDiagram S D K a F)))

/-- **Stacks 0D70, compatibility (3).** For a sheaf `F` on the total site, the direct image
`a_* F` along the total augmentation is the equalizer of the two maps
`a_{0,*} F_0 ⟶ a_{1,*} F_1` attached to the two maps `[0] ⟶ [1]`. -/
@[stacks 0D70 "compatibility (3): the total direct image is the equalizer"]
def totalPushforwardForkIsLimit (F : Sheaf S.totalTopology (Type u)) :
    IsLimit (totalPushforwardFork S D K a F) :=
  CosimplicialObject.isLimitForkOfIsLimit (pushforwardDiagram S D K a F)
    (limit.cone (pushforwardDiagram S D K a F)) (limit.isLimit _)

end Augmentation

end SimplicialSiteSituation

end CategoryTheory

end
