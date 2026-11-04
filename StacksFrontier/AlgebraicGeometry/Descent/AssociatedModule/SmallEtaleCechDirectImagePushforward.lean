module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedComparison
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Etale.SmallEtalePostcomposeBaseChangeCounit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.SheafLevelComplexOfAFamily

/-!
# A Čech direct image is a direct image along a morphism of small étale ringed sites

Let `B` be a big étale site containing a scheme `X` and let `U` be an object of the small étale
site of `X`, with structure morphism `p_U : U ⟶ X`. The terms of the sheaf-level Čech complex of
[Stacks, Tag 071N] are built from `Stacks.CechSite.SheafLevel.directImage`, that is from
`j_{U,*} j_U^{-1}`: restriction to the localization at `U` followed by the direct image along
`CategoryTheory.Over.star U`. This file identifies that functor with restriction to the small
étale site of the scheme of `U` followed by the direct image
`SheafOfModules.pushforward (AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing B p_U)` along
the morphism of small étale ringed sites of [Stacks, Tag 070R] (2).

## Main definitions

* `AlgebraicGeometry.SmallEtale.objRestrictFunctorPushforwardIso`: the comparison of the two
  direct images out of the localization of `X_étale` at `U`.
* `AlgebraicGeometry.SmallEtale.directImageIsoPushforward`: the Čech direct image
  `j_{U,*} j_U^{-1}` on the small étale site of `X` is restriction to the small étale site of the
  scheme of `U` followed by the direct image along `ε_{p_U}`.

## Main results

* `AlgebraicGeometry.SmallEtale.toScheme_map_postcomposeBaseChangeAdjunction_counit_app`: the
  counit of `AlgebraicGeometry.SmallEtale.postcomposeBaseChangeAdjunction`, read on the underlying
  schemes, is the base-change projection.
* `SmallEtale.smallEtaleStructureMapRing_comp_natTrans_baseChangeLocalizationIsoStar`
  (namespace `AlgebraicGeometry`): the structure map of `ε_{p_U}`, reindexed along the comparison
  of the binary product with the fibre product, is `SheafOfModules.pushforwardOver U`.
* `AlgebraicGeometry.SmallEtale.comparisonComp_baseChangeLocalizationIsoStar`: the same equation
  with the structure map written as a composite of two morphisms of ringed sites.

## References

* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
  (U : SmallEtale B X hX)

/-- Base change along the structure morphism of `U` is continuous for the small étale topologies
of `X` and of the scheme of `U`. -/
public instance isContinuous_smallEtaleBaseChange_structureHom :
    (smallEtaleBaseChange B U.obj.hom).IsContinuous (topology B X hX)
      (topology B (objScheme B X hX U) (contains_objScheme B X hX U)) :=
  smallEtaleBaseChange_isContinuous (S := B.obj X hX) (T := U.obj.left) B U.obj.hom

/-- Base-changing along `p_U` and then passing to the localization of the small étale site of `X`
at `U` is continuous. -/
public instance isContinuous_smallEtaleBaseChange_comp_localizationEquivalence :
    (smallEtaleBaseChange B U.obj.hom ⋙
        (localizationEquivalence B X hX U).functor).IsContinuous
      (topology B X hX) ((topology B X hX).over U) :=
  Functor.isContinuous_comp _ _ _ (topology B (objScheme B X hX U)
    (contains_objScheme B X hX U)) _

/-- The counit of `AlgebraicGeometry.SmallEtale.postcomposeBaseChangeAdjunction`, read on the
underlying schemes, is the base-change projection `U ×_X W ⟶ W`. -/
public theorem toScheme_map_postcomposeBaseChangeAdjunction_counit_app
    (W : SmallEtale B X hX) :
    (toScheme B X hX).map ((postcomposeBaseChangeAdjunction B X hX U).counit.app W) =
      B.inclusion.map (Limits.pullback.fst W.obj.hom U.obj.hom) := by
  have h : (BigEtaleOver.toScheme B X hX).map ((inclusion B X hX).map
        ((postcomposeBaseChangeAdjunction B X hX U).counit.app W)) =
      (BigEtaleOver.toScheme B X hX).map ((Over.mapPullbackAdj U.obj.hom).counit.app
        ((inclusion B X hX).obj W)) :=
    congrArg (BigEtaleOver.toScheme B X hX).map
      (inclusion_map_postcomposeBaseChangeAdjunction_counit_app B X hX U W)
  rwa [Over.mapPullbackAdj_counit_app] at h

/-- The structure map of `ε_{p_U}`, reindexed along the comparison of the binary product with the
fibre product, is `SheafOfModules.pushforwardOver U`. -/
public theorem smallEtaleStructureMapRing_comp_natTrans_baseChangeLocalizationIsoStar :
    smallEtaleStructureMapRing B U.obj.hom ≫
        (Functor.sheafPushforwardContinuousNatTrans
          (baseChangeLocalizationIsoStar B X hX U).inv RingCat.{u}
          (topology B X hX) ((topology B X hX).over U)).app
            ((structureSheaf B X hX).over U) =
      SheafOfModules.pushforwardOver U := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun W => ?_)
  induction W with | op W => ?_
  have hphi : (smallEtaleStructureMapRing B U.obj.hom).hom.app (Opposite.op W) =
      (structureSheaf B X hX).obj.map
        ((postcomposeBaseChangeAdjunction B X hX U).counit.app W).op := by
    rw [smallEtaleStructureMapRing_hom_app,
      ← toScheme_map_postcomposeBaseChangeAdjunction_counit_app B X hX U W]
    rfl
  refine Eq.trans (congrArg (fun k => k ≫ (structureSheaf B X hX).obj.map
    (((baseChangeLocalizationIsoStar B X hX U).inv.app W).left).op) hphi) ?_
  refine Eq.trans (((structureSheaf B X hX).obj.map_comp
    ((postcomposeBaseChangeAdjunction B X hX U).counit.app W).op
    (((baseChangeLocalizationIsoStar B X hX U).inv.app W).left).op).symm) ?_
  exact congrArg (fun k : (U ⨯ W : SmallEtale B X hX) ⟶ W =>
      (structureSheaf B X hX).obj.map k.op)
    (baseChangeLocalizationIsoStar_inv_app_left_comp_counit B X hX U W)

/-- The structure map of `ε_{p_U}`, written as a composite with the identity morphism of ringed
sites of the reindexed structure sheaf and reindexed along the comparison of the binary product
with the fibre product, is `SheafOfModules.pushforwardOver U`. -/
public theorem comparisonComp_baseChangeLocalizationIsoStar :
    SheafOfModules.comparisonComp (smallEtaleStructureMapRing B U.obj.hom)
        (𝟙 (Stacks.SheafOfModules.reindexRing
          (topology B U.obj.left.obj U.obj.left.property)
          (localizationEquivalence B X hX U) ((structureSheaf B X hX).over U))) ≫
      (Functor.sheafPushforwardContinuousNatTrans
        (baseChangeLocalizationIsoStar B X hX U).inv RingCat.{u}
        (topology B X hX) ((topology B X hX).over U)).app
          ((structureSheaf B X hX).over U) =
      SheafOfModules.pushforwardOver U :=
  have hcomp : SheafOfModules.comparisonComp (smallEtaleStructureMapRing B U.obj.hom)
      (𝟙 (Stacks.SheafOfModules.reindexRing
        (topology B U.obj.left.obj U.obj.left.property)
        (localizationEquivalence B X hX U) ((structureSheaf B X hX).over U))) =
      smallEtaleStructureMapRing B U.obj.hom :=
    (congrArg (fun k => smallEtaleStructureMapRing B U.obj.hom ≫ k)
      (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
  Eq.trans (congrArg (fun k => k ≫ (Functor.sheafPushforwardContinuousNatTrans
      (baseChangeLocalizationIsoStar B X hX U).inv RingCat.{u}
      (topology B X hX) ((topology B X hX).over U)).app
      ((structureSheaf B X hX).over U)) hcomp)
    (smallEtaleStructureMapRing_comp_natTrans_baseChangeLocalizationIsoStar B X hX U)

/-- The direct image along `CategoryTheory.Over.star U` is isomorphic to the crossover to the small
étale site of the scheme of `U` followed by the direct image along `ε_{p_U}`. -/
public def objRestrictFunctorPushforwardIso :
    objRestrictFunctor B X hX U ⋙
        SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B U.obj.hom) ≅
      SheafOfModules.pushforward.{u} (SheafOfModules.pushforwardOver U) :=
  SheafOfModules.pushforwardComp.{u} (smallEtaleStructureMapRing B U.obj.hom)
      (𝟙 (Stacks.SheafOfModules.reindexRing
        (topology B U.obj.left.obj U.obj.left.property)
        (localizationEquivalence B X hX U) ((structureSheaf B X hX).over U))) ≪≫
    SheafOfModules.pushforwardCongr₂.{u} _
      (baseChangeLocalizationIsoStar B X hX U).symm
      (comparisonComp_baseChangeLocalizationIsoStar B X hX U)

/-- The direct image `j_{U,*} j_U^{-1}` of the sheaf-level Čech complex is isomorphic to a direct
image along a morphism of small étale ringed sites: restricting an `𝒪_{X_étale}`-module to the
localization at `U` and pushing it back along `CategoryTheory.Over.star U` is restricting it to
the small étale site of the scheme of `U` and pushing it forward along the morphism of ringed
sites `ε_{p_U}` of [Stacks, Tag 070R] (2). -/
public def directImageIsoPushforward :
    Stacks.CechSite.SheafLevel.directImage (structureSheaf B X hX) U ≅
      objRestrict B X hX U ⋙
        SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B U.obj.hom) :=
  (Functor.isoWhiskerLeft (SheafOfModules.overFunctor.{u} (structureSheaf B X hX) U)
      (objRestrictFunctorPushforwardIso B X hX U)).symm ≪≫
    (Functor.associator _ _ _).symm

end AlgebraicGeometry.SmallEtale

end
