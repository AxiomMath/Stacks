module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.LocalComparisonPseudonaturalProofMates
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BigSiteStarPullback

/-!
# Restriction along an arrow of a site, as a left adjoint in two ways

For an arrow `f : V ⟶ U` of a site with pullbacks, restriction of sheaves of modules along `f`,
`SheafOfModules.overMap`, is left adjoint to the reindexed pushforward along the product with
`Over.mk f`. At the big fppf site this exhibits
`AlgebraicGeometry.BigFppfOver.objRestrictRightAdjointIso`, the comparison of the two right
adjoints of restriction to an object `T`, as the comparison of two adjunctions of
`SheafOfModules.overMap`.

## Main definitions

* `Stacks.SheafOfModules.overMapReindexEquivalence`: the reindexing equivalence of
  [Stacks, Tag 06WI] between modules on the localization of the site of `U` at `Over.mk f` and
  modules on the site of `V`.
* `Stacks.SheafOfModules.overMapStarPushforward`: the reindexed pushforward along the product with
  `Over.mk f`.
* `Stacks.SheafOfModules.overMapStarAdjunction`: restriction along `f : V ⟶ U`, as
  `SheafOfModules.overMap`, is left adjoint to `overMapStarPushforward`.

## Main results

* `Stacks.SheafOfModules.comparisonComp_starIteratedSliceForwardIsoPullback`: the two functors
  of sites related by the isomorphism of [Stacks, Tag 04IR] carry the same comparison of structure
  sheaves.
* `Stacks.SheafOfModules.heq_overMapStarAdjunction`: `overMapStarAdjunction` is the composite of
  the localized pushforward adjunction with the reindexing equivalence, the two differing only in
  the spelling of their common left adjoint.
* `AlgebraicGeometry.BigFppfOver.objRestrictRightAdjointIso_eq_rightAdjointUniq_overMap`: the
  comparison of the two right adjoints of restriction to an object of the big fppf site is
  `CategoryTheory.Adjunction.rightAdjointUniq` of two adjunctions of `SheafOfModules.overMap`.

## References

* [Stacks Project, Tag 04IR](https://stacks.math.columbia.edu/tag/04IR)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Stacks.SheafOfModules

attribute [local instance] Over.ConstructProducts.over_binaryProduct_of_pullback

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {J : GrothendieckTopology C}
  {U V : C} (f : V ⟶ U)

/-- Passing from the site of `V` to the localization of the site of `U` at `Over.mk f`, as the
functor of the symmetric of `CategoryTheory.Over.iteratedSliceEquiv`, is continuous. -/
public instance isContinuous_iteratedSliceEquivSymm_functor :
    ((Over.mk f).iteratedSliceEquiv.symm).functor.IsContinuous
      (J.over V) ((J.over U).over (Over.mk f)) :=
  Stacks.SheafOfModules.isContinuous_iteratedSliceBackward (J := J) f

/-- Passing from the localization of the site of `U` at `Over.mk f` to the site of `V`, as the
inverse of the symmetric of `CategoryTheory.Over.iteratedSliceEquiv`, is continuous. -/
public instance isContinuous_iteratedSliceEquivSymm_inverse :
    ((Over.mk f).iteratedSliceEquiv.symm).inverse.IsContinuous
      ((J.over U).over (Over.mk f)) (J.over V) :=
  inferInstanceAs ((Over.mk f).iteratedSliceForward.IsContinuous
    ((J.over U).over (Over.mk f)) (J.over (Over.mk f).left))

/-- Passing from the localization of the site of `U` at `Over.mk f` to the site of `V`, as
`CategoryTheory.Over.iteratedSliceForward`, is continuous. -/
public instance isContinuous_iteratedSliceForward' :
    (Over.mk f).iteratedSliceForward.IsContinuous ((J.over U).over (Over.mk f)) (J.over V) :=
  inferInstanceAs ((Over.mk f).iteratedSliceForward.IsContinuous
    ((J.over U).over (Over.mk f)) (J.over (Over.mk f).left))

/-- **Taking the product with `Over.mk f` and passing to the site of `V` is continuous.** -/
public instance isContinuous_starIteratedSliceForward :
    (Over.star (Over.mk f) ⋙ (Over.mk f).iteratedSliceForward).IsContinuous
      (J.over U) (J.over V) :=
  Functor.isContinuous_comp _ _ _ ((J.over U).over (Over.mk f)) _

/-- **Base change along `f` is continuous.** -/
public instance isContinuous_overPullback :
    (Over.pullback f).IsContinuous (J.over U) (J.over V) :=
  (Over.mapPullbackAdj f).isContinuous_of_isCocontinuous _ _

variable (R : Sheaf J RingCat.{w})

/-- **The two functors of sites carry the same comparison of structure sheaves.**  A global
function on the underlying object of `Z` is carried to the underlying object of `Over.mk f ⨯ Z` in
two ways: by restricting along the first projection of the fibre product `Z ×_U V` and then along
the comparison `CategoryTheory.starIteratedSliceForwardIsoPullback f` of [Stacks, Tag 04IR], or by
restricting along the second projection of the product. The two agree. -/
public theorem comparisonComp_starIteratedSliceForwardIsoPullback :
    Sheaf.toPushforwardOverPullback R f ≫
        (@Functor.sheafPushforwardContinuousNatTrans (Over U) _ (Over V) _ _ _
          (starIteratedSliceForwardIsoPullback f).hom RingCat.{w} _ (J.over U) (J.over V)
          (isContinuous_starIteratedSliceForward f)
          (isContinuous_overPullback f)).app (R.over V) =
      @SheafOfModules.comparisonComp (Over U) _ (Over (Over.mk f)) _ (Over V) _
        (J.over U) ((J.over U).over (Over.mk f)) (J.over V)
        (Over.star (Over.mk f)) ((Over.mk f).iteratedSliceForward)
        _ (isContinuous_iteratedSliceForward' f) (isContinuous_starIteratedSliceForward f)
        _ _ (R.over V)
        (SheafOfModules.pushforwardOver (R := R.over U) (Over.mk f))
        (𝟙 ((R.over U).over (Over.mk f))) := by
  ext : 2
  funext Z
  change R.obj.map (Quiver.Hom.op (pullback.fst (Over.hom Z.unop) f)) ≫
      R.obj.map (Quiver.Hom.op
        ((starIteratedSliceForwardIsoPullback f).hom.app Z.unop).left) =
    R.obj.map (Quiver.Hom.op (prod.snd : Over.mk f ⨯ Z.unop ⟶ Z.unop).left) ≫ 𝟙 _
  refine Eq.trans (R.obj.map_comp _ _).symm ?_
  refine Eq.trans (congrArg (fun k => R.obj.map (Quiver.Hom.op k))
    (starIteratedSliceForwardIsoPullback_hom_app_left_comp_fst f Z.unop)) ?_
  exact (Category.comp_id _).symm

/-- **The reindexing equivalence of [Stacks, Tag 06WI] along an arrow of a site**: modules on the
localization of the site of `U` at `Over.mk f` are modules on the site of `V`. It is
`Stacks.SheafOfModules.reindexEquivalence` at the symmetric of
`CategoryTheory.Over.iteratedSliceEquiv`. -/
public noncomputable abbrev overMapReindexEquivalence :=
  @Stacks.SheafOfModules.reindexEquivalence _ _ _ _ ((J.over U).over (Over.mk f))
    (J.over V) ((Over.mk f).iteratedSliceEquiv.symm)
    (isContinuous_iteratedSliceEquivSymm_functor f)
    (isContinuous_iteratedSliceEquivSymm_inverse f)
    ((R.over U).over (Over.mk f))

/-- **The right adjoint of restriction along `f`, read through the product with `Over.mk f`**:
a module on the site of `V` is read on the localization of the site of `U` at `Over.mk f` by
`overMapReindexEquivalence` and then pushed forward along the product with `Over.mk f`. -/
public noncomputable abbrev overMapStarPushforward :=
  (overMapReindexEquivalence f R).inverse ⋙
    SheafOfModules.pushforward.{w} (SheafOfModules.pushforwardOver (R := R.over U) (Over.mk f))

/-- **Restriction along an arrow of a site is left adjoint to the reindexed pushforward along the
product with that arrow**: `SheafOfModules.overMap` along `f` is left adjoint to
`overMapStarPushforward f R`. It is the composite of `SheafOfModules.overPushforwardOverAdj` at
`Over.mk f` with the reindexing equivalence `overMapReindexEquivalence f R`. -/
public noncomputable def overMapStarAdjunction :
    SheafOfModules.overMap.{w} R f ⊣ overMapStarPushforward f R :=
  (SheafOfModules.overPushforwardOverAdj.{w} (R := R.over U) (Over.mk f)).comp
    (overMapReindexEquivalence f R).toAdjunction

/-- **`overMapStarAdjunction` is the composite it is built from**, as a heterogeneous equality:
the two differ only in the spelling of their common left adjoint — `SheafOfModules.overMap` along
`f` on one side, and restriction to the localization followed by the reindexing on the other. -/
public theorem heq_overMapStarAdjunction :
    HEq ((SheafOfModules.overPushforwardOverAdj.{w} (R := R.over U) (Over.mk f)).comp
        (overMapReindexEquivalence f R).toAdjunction)
      (overMapStarAdjunction f R) :=
  HEq.rfl

end Stacks.SheafOfModules

namespace AlgebraicGeometry.BigFppfOver

open Stacks.SheafOfModules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T : BigFppfOver B S hS)

/-- **The comparison of the two right adjoints of restriction to an object of the big fppf site is
a comparison of two adjunctions of `SheafOfModules.overMap`.**
`AlgebraicGeometry.BigFppfOver.objRestrictRightAdjointIso` is
`CategoryTheory.Adjunction.rightAdjointUniq` of `Stacks.SheafOfModules.overMapStarAdjunction` and
`SheafOfModules.overMapPushforwardAdj`, both along the structure morphism of `T`. -/
public theorem objRestrictRightAdjointIso_eq_rightAdjointUniq_overMap :
    objRestrictRightAdjointIso B S hS T =
      Adjunction.rightAdjointUniq
        (overMapStarAdjunction (J := B.topology) T.hom B.structureSheaf)
        (SheafOfModules.overMapPushforwardAdj.{u} B.structureSheaf T.hom) :=
  objRestrictRightAdjointIso_eq_rightAdjointUniq B S hS T
    (heq_overMapStarAdjunction T.hom B.structureSheaf)

end AlgebraicGeometry.BigFppfOver

end
