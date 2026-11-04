module

public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BaseChangeCommutation
public import StacksCore.Tactic.StacksAttribute

/-!
# Direct image across a cartesian square of pro-étale sites

For a cartesian square

```
T' --g'--> T
|          |
f'         f
v          v
S' --g---> S
```

in a chosen big pro-étale site, direct image along `f` commutes with restriction to the small
pro-étale site at `S'`, and likewise with inverse image on the big sites.

## Main results

* `AlgebraicGeometry.ProEtale.smallProetaleBaseChangePushforwardIso`: restriction of a big
  direct image to the small site of `S'` is the small direct image of the restriction.
* `AlgebraicGeometry.ProEtale.bigProetaleBaseChangePushforwardIso`: the analogous base-change
  isomorphism entirely on big sites.

## References

* [Stacks Project, Tag 0F61](https://stacks.math.columbia.edu/tag/0F61)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProEtale

variable (B : BigProetaleSite.{u})
variable {T' T S' S : B.Scheme}
variable (g' : T' ⟶ T) (f' : T' ⟶ S') (f : T ⟶ S) (g : S' ⟶ S)

/-- For a cartesian square in a chosen big pro-étale site, restriction to the small pro-étale
site of `S'` followed by base change along `f` is base change along `f'` followed by
restriction to the small pro-étale site of `T'`. -/
public noncomputable def smallProetaleCartesianIndexIso
    (B : BigProetaleSite.{u}) {T' T S' S : B.Scheme}
    (g' : T' ⟶ T) (f' : T' ⟶ S') (f : T ⟶ S) (g : S' ⟶ S)
    (h : IsPullback g' f' f g) :
    (smallProetaleToBigProetaleFunctor B S' S g) ⋙ Over.pullback f ≅
      (smallProetaleBaseChange B T' S' f') ⋙
        smallProetaleToBigProetaleFunctor B T' T g' := by
  dsimp [smallProetaleToBigProetaleFunctor]
  calc
    _ ≅ SmallProetale.inclusion B S'.obj S'.property ⋙
        (Over.map g ⋙ Over.pullback f) := Functor.associator _ _ _
    _ ≅ SmallProetale.inclusion B S'.obj S'.property ⋙
        (Over.pullback f' ⋙ Over.map g') :=
      Functor.isoWhiskerLeft _ (overPullbackBaseChangeIso g' f' f g h)
    _ ≅ (SmallProetale.inclusion B S'.obj S'.property ⋙ Over.pullback f') ⋙
        Over.map g' := (Functor.associator _ _ _).symm
    _ = (smallProetaleBaseChange B T' S' f' ⋙
          SmallProetale.inclusion B T'.obj T'.property) ⋙ Over.map g' := by
      rw [← smallProetaleBaseChange_comp_inclusion B T' S' f']
    _ ≅ smallProetaleBaseChange B T' S' f' ⋙
        (SmallProetale.inclusion B T'.obj T'.property ⋙ Over.map g') :=
      Functor.associator _ _ _

/-- Restriction of a big pro-étale direct image to the small site of `S'`
agrees naturally with small direct image after restriction to `T'`. -/
@[stacks 0F61 "small-site base change"]
public noncomputable def smallProetaleBaseChangePushforwardIso
    (h : IsPullback g' f' f g) :
    (bigProetaleMorphism B T S f).pushforward ⋙
      (smallProetaleToBigProetaleMorphism B S' S g).inverseImage ≅
    (smallProetaleToBigProetaleMorphism B T' T g').inverseImage ⋙
      (smallProetaleMorphism B T' S' f').pushforward := by
  let : (smallProetaleToBigProetaleFunctor B S' S g).IsContinuous
      (SmallProetale.topology B S'.obj S'.property)
      (BigProetaleOver.topology B S.obj S.property) :=
    smallProetaleToBigProetaleFunctor_isContinuous B S' S g
  let : (smallProetaleBaseChange B T' S' f').IsContinuous
      (SmallProetale.topology B S'.obj S'.property)
      (SmallProetale.topology B T'.obj T'.property) :=
    (smallProetaleBaseChange_isMorphismOfSites B T' S' f').toIsContinuous
  let : (smallProetaleToBigProetaleFunctor B T' T g').IsContinuous
      (SmallProetale.topology B T'.obj T'.property)
      (BigProetaleOver.topology B T.obj T.property) :=
    smallProetaleToBigProetaleFunctor_isContinuous B T' T g'
  let := Functor.isContinuous_comp
    (smallProetaleToBigProetaleFunctor B S' S g) (Over.pullback f)
    (SmallProetale.topology B S'.obj S'.property)
    (BigProetaleOver.topology B S.obj S.property)
    (BigProetaleOver.topology B T.obj T.property)
  let := Functor.isContinuous_comp
    (smallProetaleBaseChange B T' S' f')
    (smallProetaleToBigProetaleFunctor B T' T g')
    (SmallProetale.topology B S'.obj S'.property)
    (SmallProetale.topology B T'.obj T'.property)
    (BigProetaleOver.topology B T.obj T.property)
  let smallInverseImageIso (X Y : B.Scheme) (q : X ⟶ Y) :=
    Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous
      (smallProetaleToBigProetaleFunctor B X Y q) (Type (u + 1))
      (SmallProetale.topology B X.obj X.property)
      (BigProetaleOver.topology B Y.obj Y.property)
  calc
    _ ≅
        (Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
          (BigProetaleOver.topology B S.obj S.property)
          (BigProetaleOver.topology B T.obj T.property) ⋙
        (smallProetaleToBigProetaleFunctor B S' S g).sheafPushforwardContinuous
          (Type (u + 1)) (SmallProetale.topology B S'.obj S'.property)
          (BigProetaleOver.topology B S.obj S.property) := by
      have hpush :
          (bigProetaleMorphism B T S f).pushforward ≅
            (Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
              (BigProetaleOver.topology B S.obj S.property)
              (BigProetaleOver.topology B T.obj T.property) := by
        change (Over.map f).sheafPushforwardCocontinuous (Type (u + 1))
            (BigProetaleOver.topology B T.obj T.property)
            (BigProetaleOver.topology B S.obj S.property) ≅ _
        exact (Over.mapPullbackAdj f).sheafPushforwardCocontinuousIso (Type (u + 1))
      exact Functor.isoWhiskerRight hpush _ ≪≫
        Functor.isoWhiskerLeft _ (smallInverseImageIso S' S g)
    _ ≅ (smallProetaleToBigProetaleFunctor B S' S g ⋙
          Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
        (SmallProetale.topology B S'.obj S'.property)
        (BigProetaleOver.topology B T.obj T.property) :=
      Functor.sheafPushforwardContinuousComp
        (smallProetaleToBigProetaleFunctor B S' S g) (Over.pullback f)
        (Type (u + 1)) (SmallProetale.topology B S'.obj S'.property)
        (BigProetaleOver.topology B S.obj S.property)
        (BigProetaleOver.topology B T.obj T.property)
    _ ≅ ((smallProetaleBaseChange B T' S' f') ⋙
          smallProetaleToBigProetaleFunctor B T' T g').sheafPushforwardContinuous
        (Type (u + 1)) (SmallProetale.topology B S'.obj S'.property)
        (BigProetaleOver.topology B T.obj T.property) :=
      Functor.sheafPushforwardContinuousIso
        (smallProetaleCartesianIndexIso B g' f' f g h) (Type (u + 1))
        (SmallProetale.topology B S'.obj S'.property)
        (BigProetaleOver.topology B T.obj T.property)
    _ ≅ (smallProetaleToBigProetaleFunctor B T' T g').sheafPushforwardContinuous
          (Type (u + 1)) (SmallProetale.topology B T'.obj T'.property)
          (BigProetaleOver.topology B T.obj T.property) ⋙
        (smallProetaleBaseChange B T' S' f').sheafPushforwardContinuous
          (Type (u + 1)) (SmallProetale.topology B S'.obj S'.property)
          (SmallProetale.topology B T'.obj T'.property) :=
      (Functor.sheafPushforwardContinuousComp
        (smallProetaleBaseChange B T' S' f')
        (smallProetaleToBigProetaleFunctor B T' T g')
        (Type (u + 1)) (SmallProetale.topology B S'.obj S'.property)
        (SmallProetale.topology B T'.obj T'.property)
        (BigProetaleOver.topology B T.obj T.property)).symm
    _ ≅ (smallProetaleToBigProetaleMorphism B T' T g').inverseImage ⋙
        (smallProetaleMorphism B T' S' f').pushforward :=
      Functor.isoWhiskerRight (smallInverseImageIso T' T g').symm _

/-- Big pro-étale direct image commutes naturally with inverse image along
the horizontal arrows of a cartesian square. -/
@[stacks 0F61 "big-site base change"]
public noncomputable def bigProetaleBaseChangePushforwardIso
    (h : IsPullback g' f' f g) :
    (bigProetaleMorphism B T S f).pushforward ⋙
      (bigProetaleMorphism B S' S g).inverseImage ≅
    (bigProetaleMorphism B T' T g').inverseImage ⋙
      (bigProetaleMorphism B T' S' f').pushforward := by
  let := Functor.isContinuous_comp (Over.map g) (Over.pullback f)
    (BigProetaleOver.topology B S'.obj S'.property)
    (BigProetaleOver.topology B S.obj S.property)
    (BigProetaleOver.topology B T.obj T.property)
  let := Functor.isContinuous_comp (Over.pullback f') (Over.map g')
    (BigProetaleOver.topology B S'.obj S'.property)
    (BigProetaleOver.topology B T'.obj T'.property)
    (BigProetaleOver.topology B T.obj T.property)
  have hBigPushforward (X Y : B.Scheme) (q : X ⟶ Y) :
      (bigProetaleMorphism B X Y q).pushforward ≅
        (Over.pullback q).sheafPushforwardContinuous (Type (u + 1))
          (BigProetaleOver.topology B Y.obj Y.property)
          (BigProetaleOver.topology B X.obj X.property) := by
    change (Over.map q).sheafPushforwardCocontinuous (Type (u + 1))
        (BigProetaleOver.topology B X.obj X.property)
        (BigProetaleOver.topology B Y.obj Y.property) ≅ _
    exact (Over.mapPullbackAdj q).sheafPushforwardCocontinuousIso (Type (u + 1))
  have hBigInverseImage (X Y : B.Scheme) (q : X ⟶ Y) :
      (bigProetaleMorphism B X Y q).inverseImage ≅
        (Over.map q).sheafPushforwardContinuous (Type (u + 1))
          (BigProetaleOver.topology B X.obj X.property)
          (BigProetaleOver.topology B Y.obj Y.property) := by
    change (Over.map q).sheafPullbackCocontinuous (Type (u + 1))
        (BigProetaleOver.topology B X.obj X.property)
        (BigProetaleOver.topology B Y.obj Y.property) ≅ _
    exact (Over.map q).sheafPullbackCocontinuousIsoSheafPushforwardContinuous
      (Type (u + 1)) (BigProetaleOver.topology B X.obj X.property)
      (BigProetaleOver.topology B Y.obj Y.property)
  calc
    _ ≅ (Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
          (BigProetaleOver.topology B S.obj S.property)
          (BigProetaleOver.topology B T.obj T.property) ⋙
        (Over.map g).sheafPushforwardContinuous (Type (u + 1))
          (BigProetaleOver.topology B S'.obj S'.property)
          (BigProetaleOver.topology B S.obj S.property) :=
      Functor.isoWhiskerRight (hBigPushforward T S f) _ ≪≫
        Functor.isoWhiskerLeft _ (hBigInverseImage S' S g)
    _ ≅ (Over.map g ⋙ Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
        (BigProetaleOver.topology B S'.obj S'.property)
        (BigProetaleOver.topology B T.obj T.property) :=
      Functor.sheafPushforwardContinuousComp (Over.map g) (Over.pullback f)
        (Type (u + 1)) (BigProetaleOver.topology B S'.obj S'.property)
        (BigProetaleOver.topology B S.obj S.property)
        (BigProetaleOver.topology B T.obj T.property)
    _ ≅ (Over.pullback f' ⋙ Over.map g').sheafPushforwardContinuous (Type (u + 1))
        (BigProetaleOver.topology B S'.obj S'.property)
        (BigProetaleOver.topology B T.obj T.property) :=
      Functor.sheafPushforwardContinuousIso
        (overPullbackBaseChangeIso g' f' f g h) (Type (u + 1))
        (BigProetaleOver.topology B S'.obj S'.property)
        (BigProetaleOver.topology B T.obj T.property)
    _ ≅ (Over.map g').sheafPushforwardContinuous (Type (u + 1))
          (BigProetaleOver.topology B T'.obj T'.property)
          (BigProetaleOver.topology B T.obj T.property) ⋙
        (Over.pullback f').sheafPushforwardContinuous (Type (u + 1))
          (BigProetaleOver.topology B S'.obj S'.property)
          (BigProetaleOver.topology B T'.obj T'.property) :=
      (Functor.sheafPushforwardContinuousComp (Over.pullback f') (Over.map g')
        (Type (u + 1)) (BigProetaleOver.topology B S'.obj S'.property)
        (BigProetaleOver.topology B T'.obj T'.property)
        (BigProetaleOver.topology B T.obj T.property)).symm
    _ ≅ (bigProetaleMorphism B T' T g').inverseImage ⋙
        (bigProetaleMorphism B T' S' f').pushforward :=
      Functor.isoWhiskerRight (hBigInverseImage T' T g').symm _ ≪≫
        Functor.isoWhiskerLeft _ (hBigPushforward T' S' f').symm

end AlgebraicGeometry.ProEtale

end
