module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcomp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcompCocontinuous
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtalePostcomp
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleLocalization

/-!
# Restriction of small étale sheaves along an étale morphism

Let `f : X ⟶ Y` be an *étale* morphism of algebraic spaces over a scheme `S`. Postcomposition
with `f` carries an étale scheme chart of `X` to an étale scheme chart of `Y`; that is the
functor `AlgebraicGeometry.Space.smallEtalePostcomp`. For an étale morphism this functor is
continuous and cocontinuous, and the morphism of small étale topoi attached to `f` has the
restriction of sheaves along it as inverse image and its right adjoint as direct image. In
particular a section of `f⁻¹G` over a chart `U ⟶ X` is a section of `G` over the composite chart
`U ⟶ Y`.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtalePostcompAdjunction`: spaces-étale postcomposition along an
  étale morphism is left adjoint to base change along it.
* `AlgebraicGeometry.Space.smallToposMorphism_pushforwardIso`: the small étale direct image of an
  étale morphism is the direct image of the cocontinuous postcomposition functor.
* `AlgebraicGeometry.Space.smallToposMorphism_inverseImageObjObjIso`: sections of the small étale
  inverse image over a chart `U ⟶ X` are sections over the composite chart `U ⟶ Y`.

## Main results

* `AlgebraicGeometry.Space.spacesEtalePostcomp_isCocontinuous`: spaces-étale postcomposition
  along an étale morphism is cocontinuous.

## References

* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 04LY](https://stacks.math.columbia.edu/tag/04LY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

attribute [local instance] comparisonFunctor_full comparisonFunctor_faithful

/-! ### Postcomposition on the spaces-étale site -/

/-- Spaces-étale postcomposition along an étale morphism is left adjoint to the base-change
functor: an arrow over `X` from `U` into the base change of `V` is the same as an arrow over `Y`
from `U` into `V`. -/
def spacesEtalePostcompAdjunction (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    spacesEtalePostcomp B S hS f hf ⊣ (spacesBaseChange B S hS f).functor :=
  (Over.mapPullbackAdj f).restrictFullyFaithful
    (IsEtaleOver B S hS X).fullyFaithfulι (IsEtaleOver B S hS Y).fullyFaithfulι
    ((IsEtaleOver B S hS Y).liftCompιIso _ _).symm
    ((IsEtaleOver B S hS X).liftCompιIso _ _).symm

/-- Under the localization equivalence of Stacks 04LY, spaces-étale postcomposition along an
étale morphism is the forgetful functor of the slice at that morphism. -/
def spacesEtalePostcompLocalizationIso (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    (spacesEtaleLocalization B S hS f hf).functor ⋙ Over.forget (etaleObject B S hS f hf) ≅
      spacesEtalePostcomp B S hS f hf :=
  Functor.fullyFaithfulCancelRight (SpacesEtale.inclusion B S hS Y)
    (eqToIso (spacesEtaleLocalization_forget B S hS f hf))

/-- Spaces-étale postcomposition along an étale morphism is cocontinuous. -/
instance spacesEtalePostcomp_isCocontinuous (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    (spacesEtalePostcomp B S hS f hf).IsCocontinuous
      (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y) :=
  ((spacesEtalePostcompAdjunction B S hS f hf).isCocontinuous_iff_coverPreserving _ _).2
    (CoverPreserving.of_isContinuous _ _ _)

/-! ### Postcomposition on the small étale site -/

/-- The comparison functor turns postcomposition of étale scheme charts into
postcomposition of algebraic spaces étale over the base. -/
theorem comparisonFunctor_smallEtalePostcomp (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    smallEtalePostcomp B S hS f hf ⋙ comparisonFunctor B S hS Y =
      comparisonFunctor B S hS X ⋙ spacesEtalePostcomp B S hS f hf := rfl

/-- Restricting a sheaf on the spaces-étale site of `Y` to the étale charts of `X` is the same
whether the restriction to charts is done before or after restricting along postcomposition. -/
def smallEtalePostcompComparisonSquare (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    (smallEtaleToposEquiv B S hS Y).functor ⋙
        (smallEtalePostcomp B S hS f hf).sheafPushforwardContinuous (Type (u + 1))
          (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1) ≅
      (spacesEtalePostcomp B S hS f hf).sheafPushforwardContinuous (Type (u + 1))
          (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y) ⋙
        (smallEtaleToposEquiv B S hS X).functor :=
  have : (comparisonFunctor B S hS X ⋙ spacesEtalePostcomp B S hS f hf).IsContinuous
      (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS Y) :=
    Functor.isContinuous_comp _ _ _ (SpacesEtale.topology B S hS X) _
  Functor.sheafPushforwardContinuousComp'
      (eqToIso (comparisonFunctor_smallEtalePostcomp B S hS f hf)) (Type (u + 1))
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1)
      (SpacesEtale.topology B S hS Y) ≪≫
    (Functor.sheafPushforwardContinuousComp (comparisonFunctor B S hS X)
      (spacesEtalePostcomp B S hS f hf) (Type (u + 1)) (SmallEtale.topology B S hS X.1)
      (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y)).symm

/-- Restriction of sheaves along postcomposition of charts is a left adjoint of the small étale
direct image of `f`. -/
def smallEtalePostcompAdjunctionPushforward (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    (smallEtalePostcomp B S hS f hf).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1) ⊣
      (smallToposMorphism B S hS f).pushforward :=
  ((((smallEtaleToposEquiv B S hS Y).symm.toAdjunction.comp
        ((spacesEtalePostcompAdjunction B S hS f hf).sheafPushforwardContinuous
          (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y))).comp
      (smallEtaleToposEquiv B S hS X).toAdjunction).ofNatIsoLeft
    (Iso.inverseCompIso (G := smallEtaleToposEquiv B S hS Y)
      (smallEtalePostcompComparisonSquare B S hS f hf).symm)).ofNatIsoRight
    (Iso.inverseCompIso (G := smallEtaleToposEquiv B S hS X)
      (smallToposMorphism_comparison B S hS f).symm)

/-- For an étale morphism of algebraic spaces the small étale direct image is the direct image
attached to the cocontinuous postcomposition functor on charts. -/
@[stacks 03LP "the associated morphism of topoi"]
def smallToposMorphism_pushforwardIso (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    (smallToposMorphism B S hS f).pushforward ≅
      (smallEtalePostcomp B S hS f hf).sheafPushforwardCocontinuous (Type (u + 1))
        (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1) :=
  (smallEtalePostcompAdjunctionPushforward B S hS f hf).rightAdjointUniq
    ((smallEtalePostcomp B S hS f hf).sheafAdjunctionCocontinuous (Type (u + 1))
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1))

/-- Sections of the small étale inverse image along an étale morphism over a chart `U ⟶ X` are
the sections of the original sheaf over the composite chart `U ⟶ Y`. -/
@[stacks 03LP "the formula on sections"]
def smallToposMorphism_inverseImageObjObjIso (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (G : Sheaf (SmallEtale.topology B S hS Y.1) (Type (u + 1)))
    (U : SmallEtale B S hS X.1) :
    ((smallToposMorphism B S hS f).inverseImage.obj G).obj.obj (Opposite.op U) ≅
      G.obj.obj (Opposite.op ((smallEtalePostcomp B S hS f hf).obj U)) :=
  (sheafToPresheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)) ⋙
    (evaluation _ (Type (u + 1))).obj (Opposite.op U)).mapIso
      ((smallToposMorphism_inverseImageIso B S hS f hf).app G)

end AlgebraicGeometry.Space

end
