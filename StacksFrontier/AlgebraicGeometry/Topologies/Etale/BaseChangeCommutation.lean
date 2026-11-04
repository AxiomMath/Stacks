module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange

/-!
# Base change for direct images on the big and small étale sites

Let `B` be a big étale site and let

```
T' --g'--> T
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square in it. Direct image along `f` then commutes with inverse image along
`g`, both when the inverse image lands in the small étale topos of `S'` and when it lands in
the big étale topos over `S'`.

## Main definitions

* `CategoryTheory.overPullbackBaseChangeIso` — for a cartesian square in any category with
  fibre products, composition along `g` followed by base change along `f` is base change along
  `f'` followed by composition along `g'`.
* `AlgebraicGeometry.smallEtaleCartesianIndexIso` — for a cartesian square in a big étale site,
  restriction to the small étale site of `S'` followed by base change along `f` is base change
  along `f'` followed by restriction to the small étale site of `T'`.

## Main results

* `AlgebraicGeometry.smallEtalePushforwardBaseChangeIso` — the two functors from big étale
  sheaves on `T` to small étale sheaves on `S'` agree.
* `AlgebraicGeometry.bigEtalePushforwardBaseChangeIso` — the two functors from big étale
  sheaves on `T` to big étale sheaves over `S'` agree.

## References

* [Stacks Project, Tag 0DDA](https://stacks.math.columbia.edu/tag/0DDA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory

/-- For a cartesian square with vertical maps `f`, `f'` and horizontal maps `g`, `g'`,
composition along `g` followed by base change along `f` agrees with base change along `f'`
followed by composition along `g'`. -/
public noncomputable def overPullbackBaseChangeIso
    {C : Type*} [Category C] [HasPullbacks C]
    {T' T S' S : C} (g' : T' ⟶ T) (f' : T' ⟶ S') (f : T ⟶ S) (g : S' ⟶ S)
    (h : IsPullback g' f' f g) :
    Over.map g ⋙ Over.pullback f ≅ Over.pullback f' ⋙ Over.map g' := by
  refine NatIso.ofComponents (fun X => ?_) ?_
  · let hX : IsPullback
        (pullback.fst X.hom f')
        (pullback.snd X.hom f' ≫ g')
        (X.hom ≫ g) f :=
      (IsPullback.of_hasPullback X.hom f').paste_vert h.flip
    let hL : IsPullback (pullback.fst (X.hom ≫ g) f)
        (pullback.snd (X.hom ≫ g) f) (X.hom ≫ g) f :=
      IsPullback.of_hasPullback _ _
    exact Over.isoMk (IsPullback.isoIsPullback _ _ hL hX) (by
      change (IsPullback.isoIsPullback _ _ hL hX).hom ≫
          (pullback.snd X.hom f' ≫ g') = pullback.snd (X.hom ≫ g) f
      simpa only [Category.assoc] using IsPullback.isoIsPullback_hom_snd _ _ hL hX)
  · intro X Y k
    apply Over.OverMorphism.ext
    let hX : IsPullback
        (pullback.fst X.hom f')
        (pullback.snd X.hom f' ≫ g')
        (X.hom ≫ g) f :=
      (IsPullback.of_hasPullback X.hom f').paste_vert h.flip
    let hY : IsPullback
        (pullback.fst Y.hom f')
        (pullback.snd Y.hom f' ≫ g')
        (Y.hom ≫ g) f :=
      (IsPullback.of_hasPullback Y.hom f').paste_vert h.flip
    let hLX : IsPullback (pullback.fst (X.hom ≫ g) f)
        (pullback.snd (X.hom ≫ g) f) (X.hom ≫ g) f :=
      IsPullback.of_hasPullback _ _
    let hLY : IsPullback (pullback.fst (Y.hom ≫ g) f)
        (pullback.snd (Y.hom ≫ g) f) (Y.hom ≫ g) f :=
      IsPullback.of_hasPullback _ _
    let eX := IsPullback.isoIsPullback _ _ hLX hX
    let eY := IsPullback.isoIsPullback _ _ hLY hY
    have hLk : (pullback.fst (X.hom ≫ g) f ≫ k.left) ≫ (Y.hom ≫ g) =
        pullback.snd (X.hom ≫ g) f ≫ f := by
      rw [Category.assoc, Over.w_assoc, pullback.condition]
    have hRk : (pullback.fst X.hom f' ≫ k.left) ≫ Y.hom =
        pullback.snd X.hom f' ≫ f' := by
      rw [Category.assoc, Over.w k, pullback.condition]
    change
      (pullback.lift (pullback.fst (X.hom ≫ g) f ≫ k.left)
        (pullback.snd (X.hom ≫ g) f) hLk ≫ eY.hom) =
      (eX.hom ≫ pullback.lift (pullback.fst X.hom f' ≫ k.left)
        (pullback.snd X.hom f') hRk)
    apply hY.hom_ext
    · rw [Category.assoc, Category.assoc, IsPullback.isoIsPullback_hom_fst _ _ hLY hY,
        pullback.lift_fst, pullback.lift_fst, ← Category.assoc,
        IsPullback.isoIsPullback_hom_fst _ _ hLX hX]
    · rw [Category.assoc, Category.assoc, IsPullback.isoIsPullback_hom_snd _ _ hLY hY,
        pullback.lift_snd, pullback.lift_snd_assoc, IsPullback.isoIsPullback_hom_snd _ _ hLX hX]

end CategoryTheory

namespace AlgebraicGeometry

/-- For a cartesian square in a big étale site, restriction to the small étale site of `S'`
followed by base change along `f` is base change along `f'` followed by restriction to the
small étale site of `T'`. -/
public noncomputable def smallEtaleCartesianIndexIso
    (B : AlgebraicGeometry.BigEtaleSite.{u}) {T' T S' S : B.Scheme}
    (g' : T' ⟶ T) (f' : T' ⟶ S') (f : T ⟶ S) (g : S' ⟶ S)
    (h : IsPullback g' f' f g) :
    smallEtaleToBigEtaleFunctor B S' S g ⋙ Over.pullback f ≅
      smallEtaleBaseChange B f' ⋙ smallEtaleToBigEtaleFunctor B T' T g' := by
  dsimp [smallEtaleToBigEtaleFunctor]
  calc
    _ ≅ SmallEtale.inclusion B S'.obj S'.property ⋙
        (Over.map g ⋙ Over.pullback f) := Functor.associator _ _ _
    _ ≅ SmallEtale.inclusion B S'.obj S'.property ⋙
        (Over.pullback f' ⋙ Over.map g') :=
      Functor.isoWhiskerLeft _ (overPullbackBaseChangeIso g' f' f g h)
    _ ≅ (SmallEtale.inclusion B S'.obj S'.property ⋙ Over.pullback f') ⋙
        Over.map g' := (Functor.associator _ _ _).symm
    _ = (smallEtaleBaseChange B f' ⋙
          SmallEtale.inclusion B T'.obj T'.property) ⋙ Over.map g' := by
      rw [← smallEtaleBaseChange_comp_inclusion B f']
    _ ≅ smallEtaleBaseChange B f' ⋙
        (SmallEtale.inclusion B T'.obj T'.property ⋙ Over.map g') :=
      Functor.associator _ _ _

/-- On a cartesian square, restriction to the small étale site commutes canonically with
big-site direct image. -/
@[stacks 0DDA "small-site base change"]
public noncomputable def smallEtalePushforwardBaseChangeIso
    (B : AlgebraicGeometry.BigEtaleSite.{u}) {T' T S' S : B.Scheme}
    (g' : T' ⟶ T) (f' : T' ⟶ S') (f : T ⟶ S) (g : S' ⟶ S)
    (h : IsPullback g' f' f g) :
    (bigEtaleMorphism B T S f).pushforward ⋙
      (smallEtaleToBigEtaleMorphism B S' S g).inverseImage ≅
    (smallEtaleToBigEtaleMorphism B T' T g').inverseImage ⋙
      (smallEtaleBaseChange B f').sheafPushforwardContinuous
        (Type (u + 1)) (SmallEtale.topology B S'.obj S'.property)
          (SmallEtale.topology B T'.obj T'.property) := by
  have := bigEtalePullback_isContinuous B T S f
  have := smallEtaleToBigEtaleFunctor_isContinuous B S' S g
  have := smallEtaleBaseChange_isContinuous B f'
  have := smallEtaleToBigEtaleFunctor_isContinuous B T' T g'
  have := Functor.isContinuous_comp
    (smallEtaleToBigEtaleFunctor B S' S g) (Over.pullback f)
    (SmallEtale.topology B S'.obj S'.property)
    (BigEtaleOver.topology B S.obj S.property)
    (BigEtaleOver.topology B T.obj T.property)
  have := Functor.isContinuous_comp
    (smallEtaleBaseChange B f')
    (smallEtaleToBigEtaleFunctor B T' T g')
    (SmallEtale.topology B S'.obj S'.property)
    (SmallEtale.topology B T'.obj T'.property)
    (BigEtaleOver.topology B T.obj T.property)
  let smallInverseImageIso (P Q : B.Scheme) (q : P ⟶ Q) :=
    Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous
      (smallEtaleToBigEtaleFunctor B P Q q) (Type (u + 1))
      (SmallEtale.topology B P.obj P.property)
      (BigEtaleOver.topology B Q.obj Q.property)
  calc
    _ ≅
        (Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
            (BigEtaleOver.topology B S.obj S.property)
            (BigEtaleOver.topology B T.obj T.property) ⋙
          (smallEtaleToBigEtaleFunctor B S' S g).sheafPushforwardContinuous
            (Type (u + 1)) (SmallEtale.topology B S'.obj S'.property)
            (BigEtaleOver.topology B S.obj S.property) :=
      Functor.isoWhiskerRight (bigEtaleMorphismPushforwardIso B T S f) _ ≪≫
        Functor.isoWhiskerLeft _ (smallInverseImageIso S' S g)
    _ ≅ (smallEtaleToBigEtaleFunctor B S' S g ⋙
          Over.pullback f).sheafPushforwardContinuous
          (Type (u + 1)) (SmallEtale.topology B S'.obj S'.property)
            (BigEtaleOver.topology B T.obj T.property) :=
      Functor.sheafPushforwardContinuousComp
        (smallEtaleToBigEtaleFunctor B S' S g) (Over.pullback f)
        (Type (u + 1)) (SmallEtale.topology B S'.obj S'.property)
          (BigEtaleOver.topology B S.obj S.property)
          (BigEtaleOver.topology B T.obj T.property)
    _ ≅ (smallEtaleBaseChange B f' ⋙
            smallEtaleToBigEtaleFunctor B T' T g').sheafPushforwardContinuous
          (Type (u + 1)) (SmallEtale.topology B S'.obj S'.property)
            (BigEtaleOver.topology B T.obj T.property) :=
      Functor.sheafPushforwardContinuousIso
        (smallEtaleCartesianIndexIso B g' f' f g h) (Type (u + 1))
          (SmallEtale.topology B S'.obj S'.property)
          (BigEtaleOver.topology B T.obj T.property)
    _ ≅
        (smallEtaleToBigEtaleFunctor B T' T g').sheafPushforwardContinuous
            (Type (u + 1)) (SmallEtale.topology B T'.obj T'.property)
            (BigEtaleOver.topology B T.obj T.property) ⋙
          (smallEtaleBaseChange B f').sheafPushforwardContinuous
            (Type (u + 1)) (SmallEtale.topology B S'.obj S'.property)
            (SmallEtale.topology B T'.obj T'.property) :=
      (Functor.sheafPushforwardContinuousComp
        (smallEtaleBaseChange B f')
        (smallEtaleToBigEtaleFunctor B T' T g')
        (Type (u + 1)) (SmallEtale.topology B S'.obj S'.property)
          (SmallEtale.topology B T'.obj T'.property)
          (BigEtaleOver.topology B T.obj T.property)).symm
    _ ≅
        (smallEtaleToBigEtaleMorphism B T' T g').inverseImage ⋙
          (smallEtaleBaseChange B f').sheafPushforwardContinuous
            (Type (u + 1)) (SmallEtale.topology B S'.obj S'.property)
            (SmallEtale.topology B T'.obj T'.property) :=
      Functor.isoWhiskerRight (smallInverseImageIso T' T g').symm _

/-- On a cartesian square, big étale direct image commutes canonically with big étale inverse
image. -/
@[stacks 0DDA "big-site base change"]
public noncomputable def bigEtalePushforwardBaseChangeIso
    (B : AlgebraicGeometry.BigEtaleSite.{u}) {T' T S' S : B.Scheme}
    (g' : T' ⟶ T) (f' : T' ⟶ S') (f : T ⟶ S) (g : S' ⟶ S)
    (h : IsPullback g' f' f g) :
    (bigEtaleMorphism B T S f).pushforward ⋙
      (bigEtaleMorphism B S' S g).inverseImage ≅
    (bigEtaleMorphism B T' T g').inverseImage ⋙
      (bigEtaleMorphism B T' S' f').pushforward := by
  have := bigEtalePullback_isContinuous B T S f
  have := bigEtaleMap_isContinuous B S' S g
  have := bigEtaleMap_isContinuous B T' T g'
  have := bigEtalePullback_isContinuous B T' S' f'
  have := Functor.isContinuous_comp (Over.map g) (Over.pullback f)
    (BigEtaleOver.topology B S'.obj S'.property)
    (BigEtaleOver.topology B S.obj S.property)
    (BigEtaleOver.topology B T.obj T.property)
  have := Functor.isContinuous_comp (Over.pullback f') (Over.map g')
    (BigEtaleOver.topology B S'.obj S'.property)
    (BigEtaleOver.topology B T'.obj T'.property)
    (BigEtaleOver.topology B T.obj T.property)
  calc
    _ ≅
        (Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
            (BigEtaleOver.topology B S.obj S.property)
            (BigEtaleOver.topology B T.obj T.property) ⋙
          (Over.map g).sheafPushforwardContinuous (Type (u + 1))
            (BigEtaleOver.topology B S'.obj S'.property)
            (BigEtaleOver.topology B S.obj S.property) :=
      Functor.isoWhiskerRight (bigEtaleMorphismPushforwardIso B T S f) _ ≪≫
        Functor.isoWhiskerLeft _ (bigEtaleMorphismInverseImageIso B S' S g)
    _ ≅ (Over.map g ⋙ Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
          (BigEtaleOver.topology B S'.obj S'.property)
            (BigEtaleOver.topology B T.obj T.property) :=
      Functor.sheafPushforwardContinuousComp (Over.map g) (Over.pullback f)
        (Type (u + 1)) (BigEtaleOver.topology B S'.obj S'.property)
          (BigEtaleOver.topology B S.obj S.property)
          (BigEtaleOver.topology B T.obj T.property)
    _ ≅ (Over.pullback f' ⋙ Over.map g').sheafPushforwardContinuous (Type (u + 1))
          (BigEtaleOver.topology B S'.obj S'.property)
            (BigEtaleOver.topology B T.obj T.property) :=
      Functor.sheafPushforwardContinuousIso
        (overPullbackBaseChangeIso g' f' f g h) (Type (u + 1))
          (BigEtaleOver.topology B S'.obj S'.property)
          (BigEtaleOver.topology B T.obj T.property)
    _ ≅ (Over.map g').sheafPushforwardContinuous (Type (u + 1))
          (BigEtaleOver.topology B T'.obj T'.property)
            (BigEtaleOver.topology B T.obj T.property) ⋙
        (Over.pullback f').sheafPushforwardContinuous (Type (u + 1))
          (BigEtaleOver.topology B S'.obj S'.property)
            (BigEtaleOver.topology B T'.obj T'.property) :=
      (Functor.sheafPushforwardContinuousComp (Over.pullback f') (Over.map g')
        (Type (u + 1)) (BigEtaleOver.topology B S'.obj S'.property)
          (BigEtaleOver.topology B T'.obj T'.property)
          (BigEtaleOver.topology B T.obj T.property)).symm
    _ ≅ (bigEtaleMorphism B T' T g').inverseImage ⋙
        (bigEtaleMorphism B T' S' f').pushforward :=
      Functor.isoWhiskerRight (bigEtaleMorphismInverseImageIso B T' T g').symm _ ≪≫
        Functor.isoWhiskerLeft _ (bigEtaleMorphismPushforwardIso B T' S' f').symm

end AlgebraicGeometry
