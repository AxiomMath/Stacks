module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange

/-!
# Direct image on a big étale site and restriction to the small étale sites

Let `B` be a big étale site, let `T` and `S` be objects of it and let `f : T ⟶ S`. Restricting
the direct image along `f_big` of a sheaf on the big étale site over `T` to the small étale site
of `S` gives the same sheaf as taking the direct image along `f_small` of its restriction to the
small étale site of `T`:
`(f_{big, *}ℱ)|_{S_étale} = f_{small, *}(ℱ|_{T_étale})`.

Restriction to the small étale site of `S` is the direct image `π_{S, *}` along the projection
from the big étale topos over `S` to the small étale topos of `S`, that is the sheaf pushforward
along the inclusion of the small étale category. Both composites in the displayed formula are
therefore the sheaf pushforward along one composite of site functors, and no hypothesis beyond
`f` being a morphism of the site is needed.

## Main results

* `AlgebraicGeometry.smallEtaleRestrictionPushforwardIso` — the comparison for sheaves with
  values in an arbitrary category, so in particular for sheaves of sets and for abelian sheaves.
* `AlgebraicGeometry.bigEtaleRestrictionPushforwardIso` — the comparison between the direct
  images of the morphisms of topoi `f_big`, `π_S`, `π_T` and `f_small`.

## Implementation notes

The equality of sheaves asserted by the source is a natural isomorphism of the two composite
direct-image functors here. It comes from the equality of site functors
`AlgebraicGeometry.smallEtaleBaseChange_comp_inclusion`: small étale base change along `f`
followed by the inclusion of the small étale category of `T` is the inclusion of the small étale
category of `S` followed by pullback along `f`.

## References

* [Stacks Project, Tag 0759](https://stacks.math.columbia.edu/tag/0759)
-/

@[expose] public section

open CategoryTheory

universe w w' u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (T S : B.Scheme) (f : T ⟶ S)

/-- The inclusion of the small étale category of an object of a big étale site into the big
étale category over it is a continuous functor of sites. -/
private instance smallEtaleInclusion_isContinuousOfObj (X : B.Scheme) :
    (SmallEtale.inclusion B X.obj X.property).IsContinuous
      (SmallEtale.topology B X.obj X.property)
      (BigEtaleOver.topology B X.obj X.property) :=
  (smallEtaleInclusion_isMorphismOfSites B X.obj X.property).toIsContinuous

include f

/-- For a sheaf `ℱ` on the big étale site over `T` with values in any category, the restriction
`(f_{big, *}ℱ)|_{S_étale}` of its direct image along `f` agrees naturally with the direct image
`f_{small, *}(ℱ|_{T_étale})` of its restriction. -/
@[stacks 0759 "arbitrary_coefficients"]
public noncomputable def smallEtaleRestrictionPushforwardIso (A : Type w) [Category.{w'} A] :
    (Over.pullback f).sheafPushforwardContinuous A
        (BigEtaleOver.topology B S.obj S.property)
        (BigEtaleOver.topology B T.obj T.property) ⋙
      (SmallEtale.inclusion B S.obj S.property).sheafPushforwardContinuous A
        (SmallEtale.topology B S.obj S.property)
        (BigEtaleOver.topology B S.obj S.property) ≅
    (SmallEtale.inclusion B T.obj T.property).sheafPushforwardContinuous A
        (SmallEtale.topology B T.obj T.property)
        (BigEtaleOver.topology B T.obj T.property) ⋙
      (smallEtaleBaseChange B f).sheafPushforwardContinuous A
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property) := by
  letI : (SmallEtale.inclusion B S.obj S.property ⋙ Over.pullback f).IsContinuous
      (SmallEtale.topology B S.obj S.property)
      (BigEtaleOver.topology B T.obj T.property) :=
    Functor.isContinuous_comp (SmallEtale.inclusion B S.obj S.property) (Over.pullback f)
      (SmallEtale.topology B S.obj S.property)
      (BigEtaleOver.topology B S.obj S.property)
      (BigEtaleOver.topology B T.obj T.property)
  letI : (smallEtaleBaseChange B f ⋙ SmallEtale.inclusion B T.obj T.property).IsContinuous
      (SmallEtale.topology B S.obj S.property)
      (BigEtaleOver.topology B T.obj T.property) :=
    Functor.isContinuous_comp (smallEtaleBaseChange B f)
      (SmallEtale.inclusion B T.obj T.property)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)
      (BigEtaleOver.topology B T.obj T.property)
  exact (SmallEtale.inclusion B S.obj S.property).sheafPushforwardContinuousComp
      (Over.pullback f) A
      (SmallEtale.topology B S.obj S.property)
      (BigEtaleOver.topology B S.obj S.property)
      (BigEtaleOver.topology B T.obj T.property) ≪≫
    Functor.sheafPushforwardContinuousIso
      (eqToIso (smallEtaleBaseChange_comp_inclusion B f).symm) A
      (SmallEtale.topology B S.obj S.property)
      (BigEtaleOver.topology B T.obj T.property) ≪≫
    ((smallEtaleBaseChange B f).sheafPushforwardContinuousComp
      (SmallEtale.inclusion B T.obj T.property) A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)
      (BigEtaleOver.topology B T.obj T.property)).symm

/-- The direct image along the morphism of topoi `f_big` followed by restriction along the
projection `π_S` agrees naturally with restriction along `π_T` followed by the direct image along
`f_small`. -/
@[stacks 0759 "direct_images_of_topoi"]
public noncomputable def bigEtaleRestrictionPushforwardIso :
    (bigEtaleMorphism B T S f).pushforward ⋙
        (bigEtaleToSmallEtaleMorphism B S.obj S.property).pushforward ≅
      (bigEtaleToSmallEtaleMorphism B T.obj T.property).pushforward ⋙
        (smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
          (SmallEtale.topology B S.obj S.property)
          (SmallEtale.topology B T.obj T.property) :=
  (bigSmallEtalePushforwardCommIso B T S f).symm

end AlgebraicGeometry
