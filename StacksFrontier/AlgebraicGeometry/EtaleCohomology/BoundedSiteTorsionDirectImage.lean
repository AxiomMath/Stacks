module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.SheafCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardBoundedSite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.TorsionSheavesAndRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedExactFunctor
public import StacksFrontier.Homology.CompositeCollapse
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerived.DerivedDeltaFunctor
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.ProperBaseChangeAtAPoint

/-!
# Torsion of higher direct images on the small étale sites of a big étale site

Let `B` be a big étale site and `f : T ⟶ S` a morphism of its underlying category whose morphism
of schemes is quasi-compact and quasi-separated. Part (1) of Stacks 0DDD says that the higher
direct images `R^n f_* F` of a torsion abelian sheaf `F` on `T_étale` are torsion. On Mathlib's
small étale sites this is
`Stacks.EtaleCohomology.torsionSheafProperty_rightDerived_smallEtaleDirectImageAb`; this
file transports it to the size-bounded small étale sites `AlgebraicGeometry.SmallEtale B S hS` of
Stacks 021B, along the comparison `AlgebraicGeometry.SmallEtale.sheafEquiv` of the two sites.

## Main results

* `AlgebraicGeometry.SmallEtale.torsionSheafProperty_sheafEquiv_functor_obj` and
  `AlgebraicGeometry.SmallEtale.torsionSheafProperty_sheafEquiv_inverse_obj` — the comparison
  preserves torsion sheaves in both directions.
* `AlgebraicGeometry.SmallEtale.smallPushforwardIsoSheafEquiv` — the bounded direct image is the
  conjugate of Mathlib's under the comparison.
* `AlgebraicGeometry.SmallEtale.torsionSheafProperty_rightDerived_smallPushforward` — part (1) of
  Stacks 0DDD on the bounded small étale sites.

## Implementation notes

The comparison of the two direct images is the comparison of the two base change functors of
sites, `AlgebraicGeometry.SmallEtale.toEtaleSiteBaseChangeIso`, read on sheaves. The derived
functors are then compared by `Stacks.RightDerivedComp.objIso`, the comparison functor being an
equivalence, hence exact and preserving injective objects, and by
`Stacks.Cohomology.ProperBaseChange.rightDerivedCompObjIso` for the exact functor applied after.

## References

* [Stacks Project, Tag 0DDD](https://stacks.math.columbia.edu/tag/0DDD)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.EtaleCohomology

/-- The direct image of abelian sheaves on small étale sites is additive, stated at the
coefficient universe `u + 1` so that instance search does not have to solve a universe
constraint. -/
public instance (priority := high) additive_smallEtaleDirectImageAb
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :
    (smallEtaleDirectImageAb.{u + 1} f).Additive where
  map_add := rfl

end Stacks.EtaleCohomology

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u})

/-- Under the comparison `AlgebraicGeometry.SmallEtale.sheafEquiv` of the bounded small étale
site with Mathlib's, a torsion abelian sheaf goes to a torsion abelian sheaf: its restriction back
to the bounded site is the sheaf itself, and restriction along a dense subsite detects torsion. -/
public theorem torsionSheafProperty_sheafEquiv_functor_obj (X : B.Scheme)
    (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hG : Stacks.Torsion.torsionSheafProperty.{u + 1} (SmallEtale.topology B X.obj X.property) G) :
    Stacks.Torsion.torsionSheafProperty.{u + 1} X.obj.smallEtaleTopology
      ((SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}).functor.obj G) :=
  Stacks.EtaleCohomology.torsionSheafProperty_of_pushforward _ _ (SmallEtale.toEtaleSite B X.obj
    X.property) _ ((Stacks.Torsion.torsionSheafProperty _).prop_of_iso
      ((SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}).unitIso.app G) hG)

/-- Under the comparison of the bounded small étale site with Mathlib's, a torsion abelian sheaf
on Mathlib's site restricts to a torsion abelian sheaf on the bounded site: restriction along a
cocontinuous functor preserves local torsion. -/
public theorem torsionSheafProperty_sheafEquiv_inverse_obj (X : B.Scheme)
    (G : Sheaf X.obj.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : Stacks.Torsion.torsionSheafProperty.{u + 1} X.obj.smallEtaleTopology G) :
    Stacks.Torsion.torsionSheafProperty.{u + 1} (SmallEtale.topology B X.obj X.property)
      ((SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}).inverse.obj G) :=
  Stacks.Torsion.torsionSheafProperty_sheafPushforwardContinuous
    (SmallEtale.toEtaleSite B X.obj X.property) G hG

variable {B} {S T : B.Scheme} (f : T ⟶ S)

attribute [local instance] smallEtaleSheaf_hasInjectiveResolutions

/-- The bounded direct image is additive, stated so that instance search does not try the
universe-polymorphic instances for Mathlib's small étale sites. -/
local instance (priority := high) additive_smallPushforward :
    (B.smallPushforward f AddCommGrpCat.{u + 1}).Additive where
  map_add := rfl

/-- Restricting from Mathlib's small étale site and then taking the bounded direct image is
taking Mathlib's direct image and then restricting: the base change functors of the two sites
commute with the comparison, `AlgebraicGeometry.SmallEtale.toEtaleSiteBaseChangeIso`. -/
public def sheafEquivInverseSmallPushforwardIso :
    (SmallEtale.sheafEquiv B T.obj T.property AddCommGrpCat.{u + 1}).inverse ⋙
        B.smallPushforward f AddCommGrpCat.{u + 1} ≅
      Stacks.EtaleCohomology.smallEtaleDirectImageAb.{u + 1} (B.inclusion.map f) ⋙
        (SmallEtale.sheafEquiv B S.obj S.property AddCommGrpCat.{u + 1}).inverse :=
  haveI : (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)).IsContinuous
      S.obj.smallEtaleTopology T.obj.smallEtaleTopology :=
    Stacks.EtaleCohomology.smallEtaleBaseChange_isContinuous (B.inclusion.map f)
  haveI : (toEtaleSite B S.obj S.property).IsContinuous (SmallEtale.topology B S.obj S.property)
      S.obj.smallEtaleTopology := isContinuous_toEtaleSite B S.obj S.property
  haveI : (toEtaleSite B T.obj T.property).IsContinuous (SmallEtale.topology B T.obj T.property)
      T.obj.smallEtaleTopology := isContinuous_toEtaleSite B T.obj T.property
  haveI : (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)).IsContinuous
      (B.inclusion.obj S).smallEtaleTopology T.obj.smallEtaleTopology :=
    Stacks.EtaleCohomology.smallEtaleBaseChange_isContinuous (B.inclusion.map f)
  haveI : (toEtaleSite B S.obj S.property).IsContinuous (SmallEtale.topology B S.obj S.property)
      (B.inclusion.obj S).smallEtaleTopology := isContinuous_toEtaleSite B S.obj S.property
  haveI := Functor.isContinuous_comp (AlgebraicGeometry.smallEtaleBaseChange B f)
    (toEtaleSite B T.obj T.property) (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property) T.obj.smallEtaleTopology
  haveI := Functor.isContinuous_comp (toEtaleSite B S.obj S.property)
    (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f))
    (SmallEtale.topology B S.obj S.property) S.obj.smallEtaleTopology T.obj.smallEtaleTopology
  Functor.sheafPushforwardContinuousComp' (SmallEtale.toEtaleSiteBaseChangeIso B f) _ _ _ _ ≪≫
    (Functor.sheafPushforwardContinuousComp _ _ _ _ _ _).symm

/-- **The bounded direct image is Mathlib's, conjugated by the comparison of sites.** -/
public def smallPushforwardIsoSheafEquiv :
    B.smallPushforward f AddCommGrpCat.{u + 1} ≅
      (SmallEtale.sheafEquiv B T.obj T.property AddCommGrpCat.{u + 1}).functor ⋙
        Stacks.EtaleCohomology.smallEtaleDirectImageAb.{u + 1} (B.inclusion.map f) ⋙
          (SmallEtale.sheafEquiv B S.obj S.property AddCommGrpCat.{u + 1}).inverse :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (SmallEtale.sheafEquiv B T.obj T.property AddCommGrpCat.{u + 1}).unitIso
      _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (sheafEquivInverseSmallPushforwardIso f)

/-- **Part (1) of Stacks 0DDD on the small étale sites of a big étale site.** If the morphism of
schemes underlying `f : T ⟶ S` is quasi-compact and quasi-separated, then for a torsion abelian
sheaf `F` on `T_étale` every higher direct image `R^n f_* F` is a torsion abelian sheaf on
`S_étale`. -/
public theorem torsionSheafProperty_rightDerived_smallPushforward
    [QuasiCompact (B.inclusion.map f)] [QuasiSeparated (B.inclusion.map f)] (n : ℕ)
    (F : Sheaf (SmallEtale.topology B T.obj T.property) AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty.{u + 1} (SmallEtale.topology B T.obj T.property) F) :
    Stacks.Torsion.torsionSheafProperty.{u + 1} (SmallEtale.topology B S.obj S.property)
      (((B.smallPushforward f AddCommGrpCat.{u + 1}).rightDerived n).obj F) := by
  have := smallEtaleSheaf_isGrothendieckAbelian B T
  let ΨT := SmallEtale.sheafEquiv B T.obj T.property AddCommGrpCat.{u + 1}
  let ΨS := SmallEtale.sheafEquiv B S.obj S.property AddCommGrpCat.{u + 1}
  have : ΨT.functor.Additive := ΨT.functor.additive_of_preserves_binary_products
  have : ΨS.inverse.Additive := ΨS.inverse.additive_of_preserves_binary_products
  let D := Stacks.EtaleCohomology.smallEtaleDirectImageAb.{u + 1} (B.inclusion.map f)
  have hD : Stacks.Torsion.torsionSheafProperty.{u + 1} S.obj.smallEtaleTopology
      ((D.rightDerived n).obj (ΨT.functor.obj F)) :=
    Stacks.EtaleCohomology.torsionSheafProperty_rightDerived_smallEtaleDirectImageAb.{0, u} _ n _
      (torsionSheafProperty_sheafEquiv_functor_obj B T F hF)
  refine (Stacks.Torsion.torsionSheafProperty _).prop_of_iso ?_
    (torsionSheafProperty_sheafEquiv_inverse_obj B S _ hD)
  exact Stacks.Cohomology.ProperBaseChange.rightDerivedCompObjIso D ΨS.inverse _ n ≪≫
    (Stacks.RightDerivedComp.objIso ΨT.functor (injectiveResolution F)
      (fun m hm => Functor.isZero_rightDerived_of_exact _ F m hm) (D ⋙ ΨS.inverse) n).symm ≪≫
    ((Stacks.Cohomology.CechDelta.rightDerivedIsoOfIso
      (smallPushforwardIsoSheafEquiv f) n).app F).symm

end AlgebraicGeometry.SmallEtale

end
