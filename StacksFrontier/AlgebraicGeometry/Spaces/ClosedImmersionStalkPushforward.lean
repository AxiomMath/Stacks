module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionChartCoverDensity
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionChartLocalFullness
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDirectImageFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkPullback

/-!
# Stalks of the small étale direct image along a closed immersion

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S` and let `z` be a
geometric point of `Z` with image `x` in `X`. The stalk at `x` of the small étale direct image
of a sheaf of sets on `Z` is the stalk of that sheaf at `z`, naturally in the sheaf.

## Main results

* `AlgebraicGeometry.Space.fullyFaithfulPushforwardOfChartConditions`: the small étale direct
  image along a representable morphism is fully faithful as soon as chart base change is cover
  dense and locally full.
* `AlgebraicGeometry.Space.inverseImageCompPushforwardIsoOfChartConditions`: under the same
  conditions the inverse image is a left inverse of the direct image.
* `AlgebraicGeometry.Space.stalkPushforwardIsoOfChartConditions`: under the same conditions the
  stalk at the image point of a direct image is the stalk of the sheaf itself.
* `AlgebraicGeometry.Space.stalkPushforwardIsoOfIsClosedImmersion`: **Stacks 0DK1**, the same for
  a closed immersion.

## Implementation notes

The two chart conditions are stated for `AlgebraicGeometry.Space.smallBaseChange`, the
base-change functor on étale scheme charts of Stacks 03G2, part (4), with respect to the small
étale topology of the source. They are taken as explicit arguments rather than as instances: at
a concrete site neither is going to be found by instance search.

Sheaves of sets are valued in `Type (u + 1)`, the universe in which the objects of the small
étale site of an algebraic space over `Scheme.{u}` live; that is the universe of the morphism of
small étale topoi of Stacks 03G2, part (3), and of the set-valued stalk functor of Stacks 04JY.

## References

* [Stacks Project, Tag 0DK1](https://stacks.math.columbia.edu/tag/0DK1)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicSpaces B S hS} (i : Z ⟶ X)
    (hi : yoneda.relativelyRepresentable i.hom)

/-- **Full faithfulness of the small étale direct image**, from the two chart conditions. For a
representable morphism `i : Z ⟶ X` of algebraic spaces whose chart base-change functor
`AlgebraicGeometry.Space.smallBaseChange` is cover dense and locally full for the small étale
topology of `Z`, the direct image of sheaves of sets along the morphism of small étale topoi of
Stacks 03G2, part (3), is fully faithful. -/
def fullyFaithfulPushforwardOfChartConditions
    (hcd : (smallBaseChange B S hS i hi).IsCoverDense (SmallEtale.topology B S hS Z.1))
    (hlf : (smallBaseChange B S hS i hi).IsLocallyFull (SmallEtale.topology B S hS Z.1)) :
    (smallToposMorphism B S hS i).pushforward.FullyFaithful :=
  have := hcd
  have := hlf
  have := isContinuous_smallBaseChange B S hS i hi
  Functor.FullyFaithful.ofIso
    (Functor.FullyFaithful.ofFullyFaithful
      ((smallBaseChange B S hS i hi).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Z.1)))
    (smallBaseChange_topos B S hS i hi).symm

/-- **The inverse image is a left inverse of the direct image.** Under the two chart conditions
the adjunction map `i⁻¹i_*G → G` is an isomorphism, naturally in the sheaf `G` on the small
étale site of `Z`. -/
def inverseImageCompPushforwardIsoOfChartConditions
    (hcd : (smallBaseChange B S hS i hi).IsCoverDense (SmallEtale.topology B S hS Z.1))
    (hlf : (smallBaseChange B S hS i hi).IsLocallyFull (SmallEtale.topology B S hS Z.1)) :
    (smallToposMorphism B S hS i).pushforward ⋙
        (smallToposMorphism B S hS i).inverseImage ≅ 𝟭 _ :=
  have hff := fullyFaithfulPushforwardOfChartConditions B S hS i hi hcd hlf
  haveI := hff.full
  haveI := hff.faithful
  haveI : ∀ G, IsIso ((smallToposMorphism B S hS i).adj.counit.app G) := fun _ => inferInstance
  haveI : IsIso (smallToposMorphism B S hS i).adj.counit := NatIso.isIso_of_isIso_app _
  asIso (smallToposMorphism B S hS i).adj.counit

/-- **The stalk of a direct image at the image point.** Under the two chart conditions, for a
geometric point `z` of `Z` the stalk at its image in `X` of the small étale direct image of a
sheaf of sets on `Z` is the stalk of that sheaf at `z`, naturally in the sheaf. -/
def stalkPushforwardIsoOfChartConditions
    (hcd : (smallBaseChange B S hS i hi).IsCoverDense (SmallEtale.topology B S hS Z.1))
    (hlf : (smallBaseChange B S hS i hi).IsLocallyFull (SmallEtale.topology B S hS Z.1))
    (z : GeometricPoint B S hS Z.1) :
    (smallToposMorphism B S hS i).pushforward ⋙
        sheafToPresheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)) ⋙
          stalkSetFunctor (geometricPointMap i.hom z) ≅
      sheafToPresheaf (SmallEtale.topology B S hS Z.1) (Type (u + 1)) ⋙
        stalkSetFunctor z :=
  let T := sheafToPresheaf (SmallEtale.topology B S hS Z.1) (Type (u + 1)) ⋙ stalkSetFunctor z
  Functor.isoWhiskerLeft (smallToposMorphism B S hS i).pushforward
      (stalkInverseImageIso B S hS i hi z).symm ≪≫
    Functor.isoWhiskerRight
      (inverseImageCompPushforwardIsoOfChartConditions B S hS i hi hcd hlf) T ≪≫
    Functor.leftUnitor T

/-- **Stacks 0DK1.** Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S`
and let `z` be a geometric point of `Z` with image `x` in `X`. Then `(i_*F)_x = F_z` for every
sheaf of sets `F` on the small étale site of `Z`, naturally in `F`. -/
@[stacks 0DK1]
def stalkPushforwardIsoOfIsClosedImmersion (hci : IsClosedImmersion B S hS i.hom)
    (z : GeometricPoint B S hS Z.1) :
    (smallToposMorphism B S hS i).pushforward ⋙
        sheafToPresheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)) ⋙
          stalkSetFunctor (geometricPointMap i.hom z) ≅
      sheafToPresheaf (SmallEtale.topology B S hS Z.1) (Type (u + 1)) ⋙
        stalkSetFunctor z :=
  stalkPushforwardIsoOfChartConditions B S hS i hci.rep
    (smallBaseChange_isCoverDense_of_isClosedImmersion B S hS i hci)
    (smallBaseChange_isLocallyFull_of_isClosedImmersion B S hS i hci) z

end AlgebraicGeometry.Space

end
