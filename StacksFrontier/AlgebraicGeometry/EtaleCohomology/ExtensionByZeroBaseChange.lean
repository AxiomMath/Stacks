module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Adjunction

/-!
# Extension by zero commutes with base change

Let `f : Y ⟶ X` be a morphism of schemes and let `j : V ⟶ X` be étale. Forming the fibre
product

```
V' = Y ×_X V --j'--> Y
     |               |
     f'              f
     v               v
     V ------j-----> X
```

one has `j'_! ∘ f'^{-1} = f^{-1} ∘ j_!`, both on abelian étale sheaves and on étale sheaves
of modules over a fixed ring. The reason is formal, and is the argument the source gives:
`j'_! ∘ f'^{-1}` is left adjoint to `f'_* ∘ (j')^{-1}` and `f^{-1} ∘ j_!` is left adjoint to
`j^{-1} ∘ f_*`, and those two right adjoints agree because direct image commutes with étale
localization. In the site-theoretic model used here that last agreement is not an equality
but the canonical comparison of two ways of forming `W ×_X Y` for `W` étale over `V`: once as
`W ×_V (V ×_X Y)` and once in one step. Both right adjoints are the direct image of a
composite of continuous site functors, and the composites are identified by that comparison.

## Main definitions

* `AlgebraicGeometry.baseChangedEtaleProjection` — the projection `V' ⟶ V`, i.e. the first
  projection of the fibre product.
* `AlgebraicGeometry.smallEtalePostcomposeBaseChangeIso` — the comparison of site functors
  `f'^* ∘ j'_{post} ≅ j_{post} ∘ f^*` underlying everything else.
* `AlgebraicGeometry.smallEtaleRestrictionPushforwardBaseChangeIso` — the resulting
  identification `(j')^{-1}` followed by `f'_*` with `f_*` followed by `j^{-1}`, for sheaves
  valued in any category.

## Main results

* `AlgebraicGeometry.abelianExtensionByZeroBaseChangeIso` — the base-change isomorphism for
  abelian sheaves.
* `AlgebraicGeometry.moduleExtensionByZeroBaseChangeIso` — the base-change isomorphism for
  sheaves of modules.

## Implementation notes

The étale morphism is an object of the small étale site of `X`; its base change is the
corresponding object of the small étale site of `Y`, and the map from that base change to the
original object is `AlgebraicGeometry.baseChangedEtaleProjection`, the first projection of the
chosen fibre product.

The source's equality of functors is recorded as an isomorphism of functors, which retains
naturality in the sheaf. Each of the two isomorphisms is the mate, under the three
adjunctions involved, of the identification of right adjoints; it is therefore the unique
comparison compatible with the units and counits, not an arbitrary isomorphism.

## References

* [Stacks Project, Tag 03S6](https://stacks.math.columbia.edu/tag/03S6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v u₀ v₀

namespace AlgebraicGeometry

/-- The projection from the base change of an étale object of the small étale site of `X`
along `f : Y ⟶ X` to that object: the first projection of the fibre product. -/
public abbrev baseChangedEtaleProjection
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : Y ⟶ X)
    (U : SmallEtale B X.1 X.property) :
    ((smallEtaleBaseChange B f).obj U).obj.left ⟶ U.obj.left :=
  pullback.fst U.obj.hom f

/-- Base change along `V' ⟶ V` followed by composition with `V' ⟶ Y` agrees with
composition with `V ⟶ X` followed by base change along `f : Y ⟶ X`, as functors from the
small étale site of `V` to the small étale site of `Y`. On an étale `W ⟶ V` the two sides are
`W ×_V (V ×_X Y)` and `W ×_X Y`, and the comparison is the canonical isomorphism of the two
pullback squares. -/
public noncomputable def smallEtalePostcomposeBaseChangeIso
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : Y ⟶ X)
    (U : SmallEtale B X.1 X.property) :
    smallEtaleBaseChange B (baseChangedEtaleProjection B f U) ⋙
        smallEtalePostcompose B Y.1 Y.property ((smallEtaleBaseChange B f).obj U) ≅
      smallEtalePostcompose B X.1 X.property U ⋙ smallEtaleBaseChange B f := by
  apply Functor.fullyFaithfulCancelRight (SmallEtale.inclusion B Y.1 Y.property)
  calc (smallEtaleBaseChange B (baseChangedEtaleProjection B f U) ⋙
        smallEtalePostcompose B Y.1 Y.property ((smallEtaleBaseChange B f).obj U)) ⋙
        SmallEtale.inclusion B Y.1 Y.property
      ≅ smallEtaleBaseChange B (baseChangedEtaleProjection B f U) ⋙
          (smallEtalePostcompose B Y.1 Y.property ((smallEtaleBaseChange B f).obj U) ⋙
            SmallEtale.inclusion B Y.1 Y.property) := Functor.associator _ _ _
    _ = smallEtaleBaseChange B (baseChangedEtaleProjection B f U) ⋙
          (SmallEtale.inclusion B
              ((smallEtaleBaseChange B f).obj U).obj.left.1
              ((smallEtaleBaseChange B f).obj U).obj.left.property ⋙
            Over.map ((smallEtaleBaseChange B f).obj U).obj.hom) := by
        rw [smallEtalePostcompose_comp_inclusion]
    _ ≅ (smallEtaleBaseChange B (baseChangedEtaleProjection B f U) ⋙
          SmallEtale.inclusion B
            ((smallEtaleBaseChange B f).obj U).obj.left.1
            ((smallEtaleBaseChange B f).obj U).obj.left.property) ⋙
          Over.map ((smallEtaleBaseChange B f).obj U).obj.hom :=
        (Functor.associator _ _ _).symm
    _ = (SmallEtale.inclusion B U.obj.left.1 U.obj.left.property ⋙
          Over.pullback (baseChangedEtaleProjection B f U)) ⋙
          Over.map ((smallEtaleBaseChange B f).obj U).obj.hom := by
        rw [smallEtaleBaseChange_comp_inclusion]
    _ ≅ SmallEtale.inclusion B U.obj.left.1 U.obj.left.property ⋙
          (Over.pullback (pullback.fst U.obj.hom f) ⋙
            Over.map (pullback.snd U.obj.hom f)) := Functor.associator _ _ _
    _ ≅ SmallEtale.inclusion B U.obj.left.1 U.obj.left.property ⋙
          (Over.map U.obj.hom ⋙ Over.pullback f) :=
        Functor.isoWhiskerLeft _
          (overPullbackBaseChangeIso (pullback.snd U.obj.hom f)
            (pullback.fst U.obj.hom f) f U.obj.hom
            (IsPullback.of_hasPullback U.obj.hom f).flip).symm
    _ ≅ (SmallEtale.inclusion B U.obj.left.1 U.obj.left.property ⋙
          Over.map U.obj.hom) ⋙ Over.pullback f := (Functor.associator _ _ _).symm
    _ = (smallEtalePostcompose B X.1 X.property U ⋙
          SmallEtale.inclusion B X.1 X.property) ⋙ Over.pullback f := by
        rw [smallEtalePostcompose_comp_inclusion]
    _ ≅ smallEtalePostcompose B X.1 X.property U ⋙
          (SmallEtale.inclusion B X.1 X.property ⋙ Over.pullback f) :=
        Functor.associator _ _ _
    _ = smallEtalePostcompose B X.1 X.property U ⋙
          (smallEtaleBaseChange B f ⋙ SmallEtale.inclusion B Y.1 Y.property) := by
        rw [smallEtaleBaseChange_comp_inclusion]
    _ ≅ (smallEtalePostcompose B X.1 X.property U ⋙ smallEtaleBaseChange B f) ⋙
          SmallEtale.inclusion B Y.1 Y.property := (Functor.associator _ _ _).symm

/-- Restriction to the small étale site of `V'` followed by direct image along `f' : V' ⟶ V`
agrees with direct image along `f : Y ⟶ X` followed by restriction to the small étale site of
`V`. This is the identification of right adjoints from which the base-change isomorphism for
extension by zero is obtained; it holds for sheaves valued in any category. -/
public noncomputable def smallEtaleRestrictionPushforwardBaseChangeIso
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : Y ⟶ X)
    (U : SmallEtale B X.1 X.property) (A : Type u₀) [Category.{v₀} A] :
    (smallEtalePostcompose B Y.1 Y.property
          ((smallEtaleBaseChange B f).obj U)).sheafPushforwardContinuous A
        (SmallEtale.topology B
          ((smallEtaleBaseChange B f).obj U).obj.left.1
          ((smallEtaleBaseChange B f).obj U).obj.left.property)
        (SmallEtale.topology B Y.1 Y.property) ⋙
      (smallEtaleBaseChange B (baseChangedEtaleProjection B f U)
          ).sheafPushforwardContinuous A
        (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
        (SmallEtale.topology B
          ((smallEtaleBaseChange B f).obj U).obj.left.1
          ((smallEtaleBaseChange B f).obj U).obj.left.property) ≅
    (smallEtaleBaseChange B f).sheafPushforwardContinuous A
        (SmallEtale.topology B X.1 X.property)
        (SmallEtale.topology B Y.1 Y.property) ⋙
      (smallEtalePostcompose B X.1 X.property U).sheafPushforwardContinuous A
        (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
        (SmallEtale.topology B X.1 X.property) := by
  have := Functor.isContinuous_comp
    (smallEtalePostcompose B X.1 X.property U) (smallEtaleBaseChange B f)
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    (SmallEtale.topology B X.1 X.property)
    (SmallEtale.topology B Y.1 Y.property)
  exact Functor.sheafPushforwardContinuousComp'
      (smallEtalePostcomposeBaseChangeIso B f U) A
      (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      (SmallEtale.topology B
        ((smallEtaleBaseChange B f).obj U).obj.left.1
        ((smallEtaleBaseChange B f).obj U).obj.left.property)
      (SmallEtale.topology B Y.1 Y.property) ≪≫
    (Functor.sheafPushforwardContinuousComp
      (smallEtalePostcompose B X.1 X.property U) (smallEtaleBaseChange B f) A
      (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      (SmallEtale.topology B X.1 X.property)
      (SmallEtale.topology B Y.1 Y.property)).symm

/-- **Stacks 03S6, abelian sheaves.** Extension by zero of abelian étale sheaves commutes
with base change: for `f : Y ⟶ X` and `j : V ⟶ X` étale with base change `j' : V' ⟶ Y` and
`f' : V' ⟶ V`, one has `j'_! ∘ f'^{-1} ≅ f^{-1} ∘ j_!`, naturally in the sheaf. -/
@[stacks 03S6 "abelian sheaves"]
public noncomputable def abelianExtensionByZeroBaseChangeIso
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : Y ⟶ X)
    (U : SmallEtale B X.1 X.property) :
    (smallEtaleBaseChange B (baseChangedEtaleProjection B f U)).sheafPullback
        AddCommGrpCat.{u + 1}
        (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
        (SmallEtale.topology B
          ((smallEtaleBaseChange B f).obj U).obj.left.1
          ((smallEtaleBaseChange B f).obj U).obj.left.property) ⋙
      abelianExtensionByZero B Y.1 Y.property
        ((smallEtaleBaseChange B f).obj U) ≅
    abelianExtensionByZero B X.1 X.property U ⋙
      (smallEtaleBaseChange B f).sheafPullback AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.1 X.property)
        (SmallEtale.topology B Y.1 Y.property) :=
  Adjunction.leftAdjointCompIso
    ((smallEtaleBaseChange B (baseChangedEtaleProjection B f U)).sheafAdjunctionContinuous
      AddCommGrpCat.{u + 1}
      (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      (SmallEtale.topology B
        ((smallEtaleBaseChange B f).obj U).obj.left.1
        ((smallEtaleBaseChange B f).obj U).obj.left.property))
    (abelianExtensionByZeroAdjunction B Y.1 Y.property ((smallEtaleBaseChange B f).obj U))
    ((abelianExtensionByZeroAdjunction B X.1 X.property U).comp
      ((smallEtaleBaseChange B f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.1 X.property)
        (SmallEtale.topology B Y.1 Y.property)))
    (smallEtaleRestrictionPushforwardBaseChangeIso B f U AddCommGrpCat.{u + 1})

/-- **Stacks 03S6, sheaves of modules.** Extension by zero of étale sheaves of `Λ`-modules
commutes with base change, by the same adjunction argument as for abelian sheaves. -/
@[stacks 03S6 "sheaves of modules"]
public noncomputable def moduleExtensionByZeroBaseChangeIso
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : Y ⟶ X)
    (U : SmallEtale B X.1 X.property) (Λ : Type v) [Ring Λ] :
    (smallEtaleBaseChange B (baseChangedEtaleProjection B f U)).sheafPullback
        (ModuleCat.{max (u + 1) v} Λ)
        (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
        (SmallEtale.topology B
          ((smallEtaleBaseChange B f).obj U).obj.left.1
          ((smallEtaleBaseChange B f).obj U).obj.left.property) ⋙
      moduleExtensionByZero B Y.1 Y.property
        ((smallEtaleBaseChange B f).obj U) Λ ≅
    moduleExtensionByZero B X.1 X.property U Λ ⋙
      (smallEtaleBaseChange B f).sheafPullback (ModuleCat.{max (u + 1) v} Λ)
        (SmallEtale.topology B X.1 X.property)
        (SmallEtale.topology B Y.1 Y.property) :=
  Adjunction.leftAdjointCompIso
    ((smallEtaleBaseChange B (baseChangedEtaleProjection B f U)).sheafAdjunctionContinuous
      (ModuleCat.{max (u + 1) v} Λ)
      (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      (SmallEtale.topology B
        ((smallEtaleBaseChange B f).obj U).obj.left.1
        ((smallEtaleBaseChange B f).obj U).obj.left.property))
    (moduleExtensionByZeroAdjunction B Y.1 Y.property
      ((smallEtaleBaseChange B f).obj U) Λ)
    ((moduleExtensionByZeroAdjunction B X.1 X.property U Λ).comp
      ((smallEtaleBaseChange B f).sheafAdjunctionContinuous (ModuleCat.{max (u + 1) v} Λ)
        (SmallEtale.topology B X.1 X.property)
        (SmallEtale.topology B Y.1 Y.property)))
    (smallEtaleRestrictionPushforwardBaseChangeIso B f U (ModuleCat.{max (u + 1) v} Λ))

end AlgebraicGeometry

end
