module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Localization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroFinitePushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BaseChangeCommutation

/-!
# Extension by zero and finite direct image, at the hypotheses of Stacks 0GJ1

For a cartesian diagram of schemes of a big étale site
```
U --j'--> X
|g        |f
V --j---> Y
```
with `f` finite and `j` an open immersion, this file supplies the two inputs of the comparison
`AlgebraicGeometry.extensionByZeroFinitePushforwardComparison` and so states Stacks 0GJ1 with no
hypothesis beyond the source's.

* The base-change identification `g_* ∘ (j')^{-1} ≅ j^{-1} ∘ f_*` of the restriction functors,
  `AlgebraicGeometry.abelianRestrictionPushforwardCartesianIso`, does not need Stacks 0959: the
  morphism `j` along which the base change is taken is étale, so both composites are direct
  images along composites of continuous site functors, which send an étale `W ⟶ V` to
  `W ×_V U` and to `W ×_Y X`; these agree because `U = X ×_Y V`
  (`AlgebraicGeometry.smallEtaleCartesianPostcomposeBaseChangeIso`).
* The vanishing of the stalks of `f_*j'_!F` at the geometric points of `Y` outside `V`,
  `AlgebraicGeometry.etaleStalk_pushforward_extensionByZero_isZero`, is Stacks 03QP for abelian
  sheaves together with the vanishing half of Stacks 0F70. Finiteness of `f` enters only here.

## Main results

* `AlgebraicGeometry.extensionByZeroFinitePushforwardCartesianIso` — **Stacks 0GJ1**, the natural
  isomorphism `j_! ∘ g_* ≅ f_* ∘ j'_!`.

## References

* [Stacks Project, Tag 0GJ1](https://stacks.math.columbia.edu/tag/0GJ1)
* [Stacks Project, Tag 0F70](https://stacks.math.columbia.edu/tag/0F70)
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  (U : SmallEtale B X.1 X.property) (V : SmallEtale B Y.1 Y.property)
  (g : U.obj.left ⟶ V.obj.left)

/-! ### The base change identification of the restriction functors -/

/-- For a cartesian square `j' ≫ f = g ≫ j` of a big étale site whose horizontal maps
`j' : U ⟶ X` and `j : V ⟶ Y` are étale, base change along `g` followed by composition with
`j'` agrees with composition with `j` followed by base change along `f`, as functors from the
small étale site of `V` to the small étale site of `X`. On an étale `W ⟶ V` the two sides are
`W ×_V U` and `W ×_Y X`, and the comparison is the canonical isomorphism of the two pullback
squares. -/
public def smallEtaleCartesianPostcomposeBaseChangeIso
    (sq : IsPullback U.obj.hom g f V.obj.hom) :
    smallEtaleBaseChange B g ⋙ smallEtalePostcompose B X.1 X.property U ≅
      smallEtalePostcompose B Y.1 Y.property V ⋙ smallEtaleBaseChange B f := by
  apply Functor.fullyFaithfulCancelRight (SmallEtale.inclusion B X.1 X.property)
  calc (smallEtaleBaseChange B g ⋙ smallEtalePostcompose B X.1 X.property U) ⋙
        SmallEtale.inclusion B X.1 X.property
      ≅ smallEtaleBaseChange B g ⋙ (smallEtalePostcompose B X.1 X.property U ⋙
          SmallEtale.inclusion B X.1 X.property) := Functor.associator _ _ _
    _ = smallEtaleBaseChange B g ⋙
          (SmallEtale.inclusion B U.obj.left.1 U.obj.left.property ⋙
            Over.map U.obj.hom) := by rw [smallEtalePostcompose_comp_inclusion]
    _ ≅ (smallEtaleBaseChange B g ⋙
          SmallEtale.inclusion B U.obj.left.1 U.obj.left.property) ⋙
          Over.map U.obj.hom := (Functor.associator _ _ _).symm
    _ = (SmallEtale.inclusion B V.obj.left.1 V.obj.left.property ⋙ Over.pullback g) ⋙
          Over.map U.obj.hom := by rw [smallEtaleBaseChange_comp_inclusion]
    _ ≅ SmallEtale.inclusion B V.obj.left.1 V.obj.left.property ⋙
          (Over.pullback g ⋙ Over.map U.obj.hom) := Functor.associator _ _ _
    _ ≅ SmallEtale.inclusion B V.obj.left.1 V.obj.left.property ⋙
          (Over.map V.obj.hom ⋙ Over.pullback f) :=
        Functor.isoWhiskerLeft _
          (overPullbackBaseChangeIso U.obj.hom g f V.obj.hom sq).symm
    _ ≅ (SmallEtale.inclusion B V.obj.left.1 V.obj.left.property ⋙
          Over.map V.obj.hom) ⋙ Over.pullback f := (Functor.associator _ _ _).symm
    _ = (smallEtalePostcompose B Y.1 Y.property V ⋙
          SmallEtale.inclusion B Y.1 Y.property) ⋙
          Over.pullback f := by rw [smallEtalePostcompose_comp_inclusion]
    _ ≅ smallEtalePostcompose B Y.1 Y.property V ⋙
          (SmallEtale.inclusion B Y.1 Y.property ⋙ Over.pullback f) :=
        Functor.associator _ _ _
    _ = smallEtalePostcompose B Y.1 Y.property V ⋙
          (smallEtaleBaseChange B f ⋙ SmallEtale.inclusion B X.1 X.property) := by
        rw [smallEtaleBaseChange_comp_inclusion]
    _ ≅ (smallEtalePostcompose B Y.1 Y.property V ⋙ smallEtaleBaseChange B f) ⋙
          SmallEtale.inclusion B X.1 X.property := (Functor.associator _ _ _).symm

/-- **The base change identification of the restriction functors**, for a cartesian square
`j' ≫ f = g ≫ j` of a big étale site with `j` and `j'` étale: restriction to the small étale
site of `U` followed by direct image along `g` agrees with direct image along `f` followed by
restriction to the small étale site of `V`, i.e. `g_* ∘ (j')^{-1} ≅ j^{-1} ∘ f_*` for abelian
sheaves. Both sides are the direct image of a composite of continuous site functors, and the
two composites are identified by
`AlgebraicGeometry.smallEtaleCartesianPostcomposeBaseChangeIso`. -/
public def abelianRestrictionPushforwardCartesianIso
    (sq : IsPullback U.obj.hom g f V.obj.hom) :
    abelianRestriction B X.1 X.property U ⋙
        B.smallPushforward g AddCommGrpCat.{u + 1} ≅
      B.smallPushforward f AddCommGrpCat.{u + 1} ⋙
        abelianRestriction B Y.1 Y.property V := by
  have := Functor.isContinuous_comp
    (smallEtalePostcompose B Y.1 Y.property V) (smallEtaleBaseChange B f)
    (SmallEtale.topology B V.obj.left.1 V.obj.left.property)
    (SmallEtale.topology B Y.1 Y.property)
    (SmallEtale.topology B X.1 X.property)
  exact Functor.sheafPushforwardContinuousComp'
      (smallEtaleCartesianPostcomposeBaseChangeIso B f U V g sq) AddCommGrpCat.{u + 1}
      (SmallEtale.topology B V.obj.left.1 V.obj.left.property)
      (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      (SmallEtale.topology B X.1 X.property) ≪≫
    (Functor.sheafPushforwardContinuousComp
      (smallEtalePostcompose B Y.1 Y.property V) (smallEtaleBaseChange B f)
      AddCommGrpCat.{u + 1}
      (SmallEtale.topology B V.obj.left.1 V.obj.left.property)
      (SmallEtale.topology B Y.1 Y.property)
      (SmallEtale.topology B X.1 X.property)).symm

/-! ### The vanishing of the stalks of `f_*j'_!F` off `V` -/

/-- A geometric lift through `f` of a geometric point of `Y` outside the image of `j` lies
outside the image of `j'`: the square commutes, so the image of `j'` maps into the image
of `j`. -/
public theorem geometricPointLift_not_mem_range
    (sq : IsPullback (B.inclusion.map U.obj.hom) (B.inclusion.map g) (B.inclusion.map f)
      (B.inclusion.map V.obj.hom))
    {y : GeometricPoint Y.1}
    (hy : y.hom default ∉ Set.range (B.inclusion.map V.obj.hom).base)
    (p : GeometricLifts B f y) :
    (geometricPointLift (B.inclusion.map f) y p).hom default ∉
      Set.range (B.inclusion.map U.obj.hom).base := by
  rintro ⟨a, ha⟩
  refine hy ⟨(B.inclusion.map g) a, ?_⟩
  have hsq := congrArg (fun φ : U.obj.left.1 ⟶ Y.1 => φ a) sq.w
  have hp := congrArg (fun φ : y.source ⟶ Y.1 => φ default) p.2
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hsq
  rw [Scheme.Hom.comp_apply] at hp
  rw [← hsq, ha]
  exact hp

/-- **The stalks of `f_*j'_!F` vanish off `V`**, for `f` finite: the stalk of the direct image
at a geometric point `y` of `Y` is the direct sum of the stalks of `j'_!F` over the geometric
lifts of `y` through `f`, by Stacks 03QP for abelian sheaves, and each of those vanishes by
Stacks 0F70 because such a lift misses the image of `j'`. -/
public theorem etaleStalk_pushforward_extensionByZero_isZero [IsFinite (B.inclusion.map f)]
    (sq : IsPullback (B.inclusion.map U.obj.hom) (B.inclusion.map g) (B.inclusion.map f)
      (B.inclusion.map V.obj.hom))
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      AddCommGrpCat.{u + 1})
    (y : GeometricPoint Y.1)
    (hy : y.hom default ∉ Set.range (B.inclusion.map V.obj.hom).base) :
    IsZero (etaleStalk B Y.1 Y.property y
      ((B.smallPushforward f AddCommGrpCat.{u + 1}).obj
        ((abelianExtensionByZero B X.1 X.property U).obj F)).obj) := by
  classical
  refine IsZero.of_iso ?_ (stalkPushforwardIsoDirectSum B f y
    ((abelianExtensionByZero B X.1 X.property U).obj F))
  refine (colimit.isColimit _).isZero_pt (Functor.isZero _ fun p => ?_)
  exact abelianExtensionByZero_stalk_isZero_of_not_mem_range B X.1 X.property U _ F
    (geometricPointLift_not_mem_range B f U V g sq hy p.as)

/-- **Stacks 0GJ1.** For a cartesian square `g ≫ j = j' ≫ f` of schemes of a big étale site
with `f` finite and `j : V ⟶ Y` an open immersion, the functors `j_! ∘ g_*` and `f_* ∘ j'_!`
from abelian sheaves on the small étale site of `U` to abelian sheaves on the small étale site
of `Y` are naturally isomorphic.

The isomorphism is the mate, along the two extension-by-zero adjunctions, of the base change
identification `AlgebraicGeometry.abelianRestrictionPushforwardCartesianIso` of the
restriction functors; it is an isomorphism by the uniqueness characterisation of extension by
zero, whose stalk hypothesis is
`AlgebraicGeometry.etaleStalk_pushforward_extensionByZero_isZero`, where finiteness of `f` is
used. The cartesian square is used twice: once for the base change identification, and once to
see that `j'` is an open immersion. -/
@[stacks 0GJ1]
public def extensionByZeroFinitePushforwardCartesianIso [IsFinite (B.inclusion.map f)]
    [IsOpenImmersion (B.inclusion.map V.obj.hom)]
    (sq : IsPullback (B.inclusion.map U.obj.hom) (B.inclusion.map g) (B.inclusion.map f)
      (B.inclusion.map V.obj.hom)) :
    B.smallPushforward g AddCommGrpCat.{u + 1} ⋙
        abelianExtensionByZero B Y.1 Y.property V ≅
      abelianExtensionByZero B X.1 X.property U ⋙
        B.smallPushforward f AddCommGrpCat.{u + 1} :=
  have : IsOpenImmersion (B.inclusion.map U.obj.hom) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq.flip inferInstance
  have hbc := abelianRestrictionPushforwardCartesianIso B f U V g
    (IsPullback.of_map_of_faithful B.inclusion sq)
  have := isIso_extensionByZeroFinitePushforwardComparison B f U V g hbc
    (etaleStalk_pushforward_extensionByZero_isZero B f U V g sq)
  asIso (extensionByZeroFinitePushforwardComparison B f U V g hbc)

end AlgebraicGeometry

end
