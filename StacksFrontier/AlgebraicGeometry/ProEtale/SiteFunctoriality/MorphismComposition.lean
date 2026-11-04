module

public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallBaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# Composition of pro-étale morphisms of topoi

For composable morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of a chosen big pro-étale site, the
morphism of topoi attached to `f ≫ g` agrees with the composite of those attached to `f` and to
`g`, both on the big slices and on the small pro-étale sites.

## Main definitions

* `AlgebraicGeometry.ProEtale.bigProetalePushforwardIsoRestriction` — the big direct image is
  restriction along base change.
* `AlgebraicGeometry.ProEtale.smallProetaleBaseChangeComp` — base change on small pro-étale
  sites is multiplicative in the morphism.

## Main results

* `AlgebraicGeometry.ProEtale.bigProetaleMorphismCompPushforwardIso` and
  `AlgebraicGeometry.ProEtale.smallProetaleMorphismCompPushforwardIso` — the two comparisons of
  direct images.
* `AlgebraicGeometry.ProEtale.proetaleMorphismCompPushforwardIso` — both together.

## Implementation notes

The site convention is the one fixed by the rest of the chapter: `X`, `Y`, `Z` are objects of a
*chosen* big pro-étale site `B`, whose coverings are the pro-étale ones, `f_big` is the morphism
of topoi of the big slice `B/X` with the localized topology, and `f_small` is the morphism of
topoi of the small pro-étale site, the full subcategory of `B/X` on the objects with *weakly
étale* structure morphism. So the small site is weakly étale over the base while coverings are
pro-étale, which is the definition the chapter uses throughout.

Equalities of morphisms of topoi are expressed, as elsewhere in the chapter, as canonical
natural isomorphisms of their direct-image functors; the inverse images are then isomorphic as
adjunction mates. Composition of base-change functors is canonical only up to isomorphism,
because an iterated fibre product is only canonically isomorphic to a single one, so both
comparisons are induced by `CategoryTheory.Over.pullbackComp` through
`CategoryTheory.Functor.sheafPushforwardContinuousComp'`. On the big slices the direct image is
defined by cocontinuity of composition, so it is first identified with restriction along base
change; on the small sites base change is the lift of slice pullback to the weakly étale
objects, so the comparison is obtained by cancelling the fully faithful inclusion.

## References

* [Stacks Project, Tag 098U](https://stacks.math.columbia.edu/tag/098U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProEtale

variable (B : BigProetaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The direct image of the big pro-étale morphism attached to `f` is restriction along base
change along `f`. -/
public noncomputable def bigProetalePushforwardIsoRestriction {T S : B.Scheme} (f : T ⟶ S) :
    (bigProetaleMorphism B T S f).pushforward ≅
      (Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
        (BigProetaleOver.topology B S.obj S.property)
        (BigProetaleOver.topology B T.obj T.property) :=
  (Over.mapPullbackAdj f).sheafPushforwardCocontinuousIso
    (J := BigProetaleOver.topology B T.obj T.property)
    (K := BigProetaleOver.topology B S.obj S.property) (Type (u + 1))

/-- The direct image of the big pro-étale morphism attached to `f ≫ g` is canonically
isomorphic to the composite of the direct images attached to `f` and to `g`. -/
public noncomputable def bigProetaleMorphismCompPushforwardIso :
    ((bigProetaleMorphism B Y Z g).comp (bigProetaleMorphism B X Y f)).pushforward ≅
      (bigProetaleMorphism B X Z (f ≫ g)).pushforward :=
  Functor.isoWhiskerRight (bigProetalePushforwardIsoRestriction B f) _ ≪≫
    Functor.isoWhiskerLeft _ (bigProetalePushforwardIsoRestriction B g) ≪≫
    Functor.sheafPushforwardContinuousComp' (Over.pullbackComp f g).symm (Type (u + 1))
      (BigProetaleOver.topology B Z.obj Z.property)
      (BigProetaleOver.topology B Y.obj Y.property)
      (BigProetaleOver.topology B X.obj X.property) ≪≫
    (bigProetalePushforwardIsoRestriction B (f ≫ g)).symm

/-- Base change on small pro-étale sites along `g` followed by base change along `f` is base
change along `f ≫ g`. -/
public noncomputable def smallProetaleBaseChangeComp :
    smallProetaleBaseChange B Y Z g ⋙ smallProetaleBaseChange B X Y f ≅
      smallProetaleBaseChange B X Z (f ≫ g) :=
  Functor.fullyFaithfulCancelRight (SmallProetale.inclusion B X.obj X.property)
    (Functor.isoWhiskerLeft (SmallProetale.inclusion B Z.obj Z.property)
      (Over.pullbackComp f g).symm)

/-- The direct image of the small pro-étale morphism attached to `f ≫ g` is canonically
isomorphic to the composite of the direct images attached to `f` and to `g`. -/
public noncomputable def smallProetaleMorphismCompPushforwardIso :
    ((smallProetaleMorphism B Y Z g).comp (smallProetaleMorphism B X Y f)).pushforward ≅
      (smallProetaleMorphism B X Z (f ≫ g)).pushforward :=
  Functor.sheafPushforwardContinuousComp' (smallProetaleBaseChangeComp B f g) (Type (u + 1))
    (SmallProetale.topology B Z.obj Z.property)
    (SmallProetale.topology B Y.obj Y.property)
    (SmallProetale.topology B X.obj X.property)

/-- **Stacks 098U.** For composable morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of a chosen big
pro-étale site we have `g_big ∘ f_big = (g ∘ f)_big` and `g_small ∘ f_small = (g ∘ f)_small`,
as canonical isomorphisms of the direct-image functors. -/
@[stacks 098U]
public noncomputable def proetaleMorphismCompPushforwardIso :
    (((bigProetaleMorphism B Y Z g).comp (bigProetaleMorphism B X Y f)).pushforward ≅
        (bigProetaleMorphism B X Z (f ≫ g)).pushforward) ×
      (((smallProetaleMorphism B Y Z g).comp (smallProetaleMorphism B X Y f)).pushforward ≅
        (smallProetaleMorphism B X Z (f ≫ g)).pushforward) :=
  ⟨bigProetaleMorphismCompPushforwardIso B f g, smallProetaleMorphismCompPushforwardIso B f g⟩

end AlgebraicGeometry.ProEtale

end
