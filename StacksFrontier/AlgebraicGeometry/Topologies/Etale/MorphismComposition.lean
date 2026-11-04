module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange

/-!
# Composing the big and small étale morphisms of topoi

For composable morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of a big étale site, the big étale
morphism of topoi along `f ≫ g` is the composite of those along `f` and `g`, and likewise on
small étale sites.

## Main definitions

* `AlgebraicGeometry.smallEtaleBaseChange_compIso` — the comparison of successive small étale
  base changes with base change along the composite, together with its characterization after
  forgetting the étale condition.

## Main results

* `CategoryTheory.Over.pullbackComp_hom_app_left_fst_fst` and
  `CategoryTheory.Over.pullbackComp_inv_app_left_fst` — the components of the slice comparison
  `CategoryTheory.Over.pullbackComp`, read on the underlying objects.
* `AlgebraicGeometry.bigEtaleMorphism_comp_pushforwardIso` and
  `AlgebraicGeometry.bigEtaleMorphism_comp_inverseImageIso` — the big-site comparisons.
* `AlgebraicGeometry.smallEtaleMorphism_comp_pushforwardIso` and
  `AlgebraicGeometry.smallEtaleMorphism_comp_inverseImageIso` — the small-site comparisons.

## Implementation notes

The source writes equalities of geometric morphisms. Here the fibre products are chosen, so an
equality of base-change functors holds only up to the canonical comparison
`CategoryTheory.Over.pullbackComp`, and the statements are correspondingly natural
isomorphisms. Each direct-image comparison is induced by the comparison of the underlying site
functors, and each inverse-image comparison is its mate under the three adjunctions involved.

The small-site comparison is packaged as a subtype: the isomorphism of functors together with
the equation identifying it, after applying the fully faithful inclusion, with the slice
comparison. That equation is what pins the isomorphism down, since the inclusion is faithful,
and it is restated separately as `smallEtaleBaseChange_compIso_app`.

## References

* [Stacks Project, Lemma 34.4.7 (Tag 021J)](https://stacks.math.columbia.edu/tag/021J)
-/

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory.Over

variable {C : Type*} [Category C] {P Q R : C} (g : P ⟶ Q) (h : Q ⟶ R)
  [Limits.HasPullbacksAlong g] [Limits.HasPullbacksAlong h] (V : Over R)

/-- The canonical factorization of a two-step slice pullback through the one-step pullback,
read on the underlying objects. -/
theorem pullbackComp_hom_app_left_fst_fst :
    ((Over.pullbackComp g h).hom.app V).left ≫
        Limits.pullback.fst ((Over.pullback h).obj V).hom g ≫
          Limits.pullback.fst V.hom h =
      Limits.pullback.fst V.hom (g ≫ h) := by
  have hc := conjugateEquiv_counit (Over.mapPullbackAdj (g ≫ h))
      ((Over.mapPullbackAdj g).comp (Over.mapPullbackAdj h))
      (Over.mapComp g h).symm.hom V
  have hc' : (Over.map g ⋙ Over.map h).map ((Over.pullbackComp g h).hom.app V) ≫
      ((Over.mapPullbackAdj g).comp (Over.mapPullbackAdj h)).counit.app V =
      (Over.mapComp g h).symm.hom.app ((Over.pullback (g ≫ h)).obj V) ≫
      (Over.mapPullbackAdj (g ≫ h)).counit.app V := by
    simpa [Over.pullbackComp] using hc
  simpa [Over.mapPullbackAdj_counit_app, Adjunction.comp_counit_app, Over.mapComp,
    Over.pullbackComp] using congrArg (fun k => k.left) hc'

/-- The inverse form of `CategoryTheory.Over.pullbackComp_hom_app_left_fst_fst`: the
comparison from a two-step slice pullback to the pullback along the composite carries the
projection of the composite to the composite of the two projections. -/
theorem pullbackComp_inv_app_left_fst :
    ((Over.pullbackComp g h).inv.app V).left ≫ Limits.pullback.fst V.hom (g ≫ h) =
      Limits.pullback.fst ((Over.pullback h).obj V).hom g ≫
        Limits.pullback.fst V.hom h := by
  have hcancel : ((Over.pullbackComp g h).inv.app V).left ≫
      ((Over.pullbackComp g h).hom.app V).left = 𝟙 _ :=
    congrArg Over.Hom.left ((Over.pullbackComp g h).inv_hom_id_app V)
  rw [← pullbackComp_hom_app_left_fst_fst, reassoc_of% hcancel]

end CategoryTheory.Over

namespace AlgebraicGeometry

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (X Y Z : B.Scheme)
  (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **Stacks 021J.** The canonical comparison of successive small étale base changes with
base change along the composite, characterized by its image under the inclusion of the small
étale category. -/
@[stacks 021J "small étale site functor composition"]
public noncomputable def smallEtaleBaseChange_compIso :
    { e : smallEtaleBaseChange B g ⋙ smallEtaleBaseChange B f ≅
        smallEtaleBaseChange B (f ≫ g) //
      ∀ U : SmallEtale B Z.obj Z.property,
        (SmallEtale.inclusion B X.obj X.property).map (e.hom.app U) =
          (Over.pullbackComp f g).inv.app U.obj } := by
  let i :
      (smallEtaleBaseChange B g ⋙ smallEtaleBaseChange B f) ⋙
          SmallEtale.inclusion B X.obj X.property ≅
        smallEtaleBaseChange B (f ≫ g) ⋙
          SmallEtale.inclusion B X.obj X.property :=
    NatIso.ofComponents
      (fun U => (Over.pullbackComp f g).symm.app U.obj)
      (fun {U V} k =>
        (Over.pullbackComp f g).symm.hom.naturality
          ((SmallEtale.inclusion B Z.obj Z.property).map k))
  let e := Functor.fullyFaithfulCancelRight
    (SmallEtale.inclusion B X.obj X.property) i
  refine ⟨e, fun U => ?_⟩
  simp only [e, Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
  rfl

/-- **Stacks 021J.** The small-site comparison is the canonical comparison of pullbacks in
the ambient slice category, after forgetting the étale condition. -/
@[stacks 021J "canonicity of small étale site composition"]
public theorem smallEtaleBaseChange_compIso_app
    (U : SmallEtale B Z.obj Z.property) :
    (SmallEtale.inclusion B X.obj X.property).map
      ((smallEtaleBaseChange_compIso B X Y Z f g).val.hom.app U) =
    (Over.pullbackComp f g).inv.app U.obj :=
  (smallEtaleBaseChange_compIso B X Y Z f g).property U

/-- The comparison of successive small étale base changes with base change along a chosen
factorisation `fg = f ≫ g` of the composite: `AlgebraicGeometry.smallEtaleBaseChange_compIso`
transported along the factorisation. -/
public noncomputable def smallEtaleBaseChange_factoredCompIso (fg : X ⟶ Z)
    (hfg : f ≫ g = fg) :
    smallEtaleBaseChange B g ⋙ smallEtaleBaseChange B f ≅ smallEtaleBaseChange B fg :=
  (smallEtaleBaseChange_compIso B X Y Z f g).val ≪≫
    eqToIso (congrArg (smallEtaleBaseChange B) hfg)

/-- On underlying objects, the factored composition comparison carries the projection of the
base change along the composite to the composite of the two projections. -/
public theorem smallEtaleBaseChange_factoredCompIso_hom_app_fst (fg : X ⟶ Z)
    (hfg : f ≫ g = fg) (W : SmallEtale B Z.obj Z.property) :
    ((smallEtaleBaseChange_factoredCompIso B X Y Z f g fg hfg).hom.app W).hom.left ≫
        Limits.pullback.fst W.obj.hom fg =
      Limits.pullback.fst ((smallEtaleBaseChange B g).obj W).obj.hom f ≫
        Limits.pullback.fst W.obj.hom g := by
  subst hfg
  have hiso : (smallEtaleBaseChange_factoredCompIso B X Y Z f g (f ≫ g) rfl).hom.app W =
      (smallEtaleBaseChange_compIso B X Y Z f g).val.hom.app W := by
    simp [smallEtaleBaseChange_factoredCompIso]
  have hl : ((smallEtaleBaseChange_compIso B X Y Z f g).val.hom.app W).hom.left =
      ((Over.pullbackComp f g).inv.app W.obj).left :=
    congrArg Over.Hom.left (smallEtaleBaseChange_compIso_app B X Y Z f g W)
  rw [hiso, hl]
  exact Over.pullbackComp_inv_app_left_fst f g W.obj

/-- **Stacks 021J.** The canonical big-site direct-image comparison, obtained from the
base-change formula and the composition comparison of pullbacks. -/
@[stacks 021J "big étale direct images"]
public noncomputable def bigEtaleMorphism_comp_pushforwardIso :
    (bigEtaleMorphism B X Y f).pushforward ⋙
        (bigEtaleMorphism B Y Z g).pushforward ≅
      (bigEtaleMorphism B X Z (f ≫ g)).pushforward :=
  Functor.isoWhiskerRight (bigEtaleMorphismPushforwardIso B X Y f)
      (bigEtaleMorphism B Y Z g).pushforward ≪≫
    Functor.isoWhiskerLeft
      ((Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
        (BigEtaleOver.topology B Y.obj Y.property)
        (BigEtaleOver.topology B X.obj X.property))
      (bigEtaleMorphismPushforwardIso B Y Z g) ≪≫
    Functor.sheafPushforwardContinuousComp'
      (Over.pullbackComp f g).symm (Type (u + 1))
      (BigEtaleOver.topology B Z.obj Z.property)
      (BigEtaleOver.topology B Y.obj Y.property)
      (BigEtaleOver.topology B X.obj X.property) ≪≫
    (bigEtaleMorphismPushforwardIso B X Z (f ≫ g)).symm

/-- **Stacks 021J.** The inverse-image comparison is the mate of the big direct-image
comparison under the three geometric adjunctions. -/
@[stacks 021J "big étale inverse images"]
public noncomputable def bigEtaleMorphism_comp_inverseImageIso :
    (bigEtaleMorphism B Y Z g).inverseImage ⋙
        (bigEtaleMorphism B X Y f).inverseImage ≅
      (bigEtaleMorphism B X Z (f ≫ g)).inverseImage :=
  Adjunction.leftAdjointCompIso
    (bigEtaleMorphism B Y Z g).adj
    (bigEtaleMorphism B X Y f).adj
    (bigEtaleMorphism B X Z (f ≫ g)).adj
    (bigEtaleMorphism_comp_pushforwardIso B X Y Z f g)

/-- **Stacks 021J.** The direct-image comparison induced by the canonical composition
comparison of small-site base-change functors. -/
@[stacks 021J "small étale direct images"]
public noncomputable def smallEtaleMorphism_comp_pushforwardIso :
    (smallEtaleBaseChange B f).sheafPushforwardContinuous
        (Type (u + 1)) (SmallEtale.topology B Y.obj Y.property)
          (SmallEtale.topology B X.obj X.property) ⋙
      (smallEtaleBaseChange B g).sheafPushforwardContinuous
        (Type (u + 1)) (SmallEtale.topology B Z.obj Z.property)
          (SmallEtale.topology B Y.obj Y.property) ≅
    (smallEtaleBaseChange B (f ≫ g)).sheafPushforwardContinuous
      (Type (u + 1)) (SmallEtale.topology B Z.obj Z.property)
        (SmallEtale.topology B X.obj X.property) :=
  Functor.sheafPushforwardContinuousComp'
    (smallEtaleBaseChange_compIso B X Y Z f g).val
    (Type (u + 1)) (SmallEtale.topology B Z.obj Z.property)
    (SmallEtale.topology B Y.obj Y.property)
    (SmallEtale.topology B X.obj X.property)

/-- **Stacks 021J.** The inverse-image comparison is the mate of the small direct-image
comparison under the three sheaf adjunctions. -/
@[stacks 021J "small étale inverse images"]
public noncomputable def smallEtaleMorphism_comp_inverseImageIso :
    (smallEtaleBaseChange B g).sheafPullback
        (Type (u + 1)) (SmallEtale.topology B Z.obj Z.property)
          (SmallEtale.topology B Y.obj Y.property) ⋙
      (smallEtaleBaseChange B f).sheafPullback
        (Type (u + 1)) (SmallEtale.topology B Y.obj Y.property)
          (SmallEtale.topology B X.obj X.property) ≅
    (smallEtaleBaseChange B (f ≫ g)).sheafPullback
      (Type (u + 1)) (SmallEtale.topology B Z.obj Z.property)
        (SmallEtale.topology B X.obj X.property) :=
  Adjunction.leftAdjointCompIso
    ((smallEtaleBaseChange B g).sheafAdjunctionContinuous
      (Type (u + 1)) (SmallEtale.topology B Z.obj Z.property)
      (SmallEtale.topology B Y.obj Y.property))
    ((smallEtaleBaseChange B f).sheafAdjunctionContinuous
      (Type (u + 1)) (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B X.obj X.property))
    ((smallEtaleBaseChange B (f ≫ g)).sheafAdjunctionContinuous
      (Type (u + 1)) (SmallEtale.topology B Z.obj Z.property)
      (SmallEtale.topology B X.obj X.property))
    (smallEtaleMorphism_comp_pushforwardIso B X Y Z f g)

end AlgebraicGeometry
