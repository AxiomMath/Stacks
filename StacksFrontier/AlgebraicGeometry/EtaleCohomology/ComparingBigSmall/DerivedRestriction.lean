module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.Restriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.SheafCohomology
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallToBigTopos
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.AbelianSheavesOnALocalizedSite

/-!
# Derived direct image commutes with restriction to the small étale site

Let `f : T ⟶ S` be a morphism of a big étale site. Restricting the unbounded derived direct
image of a complex of abelian sheaves from the big étale site over `S` to the small étale site
of `S` agrees naturally with the derived direct image on the small étale sites of the
restriction of the complex to the small étale site of `T`.

The comparison is assembled from three inputs, none of which is re-proved here. The
undetermined-level statement is the commutation of the *undrived* functors, which holds because
all four of them are restrictions along functors of sites: direct image along the cocontinuous
`Over.map f` is restriction along the base-change functor `Over.pullback f`
(`CategoryTheory.Adjunction.sheafPushforwardCocontinuousIso` applied to
`CategoryTheory.Over.mapPullbackAdj`), and the two composites of site functors agree on the nose
by `AlgebraicGeometry.smallEtaleBaseChange_comp_inclusion`. The second input is that restriction
to a small étale site is exact, which is what makes its right derived functor the induced functor
on derived categories. The third is that restriction preserves K-injectivity of complexes
(`AlgebraicGeometry.isKInjective_smallEtaleRestriction`, Tag 0758), which is what identifies the
composite of the two derived functors on the small-site side as a right derived functor of the
composite.

## Main results

* `AlgebraicGeometry.smallEtaleRestriction_preservesFiniteColimits` — restriction of abelian
  sheaves to a small étale site preserves finite colimits; together with preservation of finite
  limits this is its exactness.
* `AlgebraicGeometry.bigSmallEtalePushforwardRestrictionIso` — the commutation of the undrived
  functors.
* `AlgebraicGeometry.bigSmallEtaleDerivedPushforwardIso` — the derived comparison.

## Implementation notes

The equality asserted in the source is recorded as a natural isomorphism of functors on
unbounded derived categories, so it is natural in the derived object rather than valid only in
each degree. The four derived functors are arbitrary choices supplied with their right-derived
universal properties, and each derived category is taken at a free morphism universe; no model
of a derived category is pinned, so the statement is not about one particular construction.

Exactness of restriction is obtained by identifying it with the inverse image of the morphism of
topoi it induces: the small étale inclusion is both continuous and cocontinuous, so
`CategoryTheory.Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous` presents
restriction as a left adjoint, whence it preserves colimits, while it is a right adjoint of
sheaf pullback, whence it preserves limits. Cocontinuity of the bare inclusion is transported
from cocontinuity of postcomposition along an identity, which is the form in which it is
available.

## References

* [Stacks Project, Tag 075A](https://stacks.math.columbia.edu/tag/075A)
* [Stacks Project, Tag 0758](https://stacks.math.columbia.edu/tag/0758)
* [Stacks Project, Tag 021I](https://stacks.math.columbia.edu/tag/021I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.Localization

universe u wTb wSb wTs wSs

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

/-- Restriction of abelian sheaves to the small étale site of `X` preserves finite limits: it is
a right adjoint of sheaf pullback along the inclusion. -/
public instance smallEtaleRestriction_preservesFiniteLimits (X : B.Scheme)
    [HasSheafify (BigEtaleOver.topology B X.obj X.property) Ab.{u + 1}] :
    PreservesFiniteLimits
      ((SmallEtale.inclusion B X.obj X.property).sheafPushforwardContinuous Ab.{u + 1}
        (SmallEtale.topology B X.obj X.property)
        (BigEtaleOver.topology B X.obj X.property)) := by
  have := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (SmallEtale.inclusion B X.obj X.property) Ab.{u + 1}
    (SmallEtale.topology B X.obj X.property)
    (BigEtaleOver.topology B X.obj X.property)).isRightAdjoint
  infer_instance

/-- Restriction of abelian sheaves to the small étale site of `X` preserves finite colimits:
the inclusion is cocontinuous as well as continuous, so restriction is the inverse image of the
induced morphism of topoi and hence a left adjoint. Together with
`AlgebraicGeometry.smallEtaleRestriction_preservesFiniteLimits` this is exactness of
restriction. -/
public instance smallEtaleRestriction_preservesFiniteColimits (X : B.Scheme)
    [HasSheafify (BigEtaleOver.topology B X.obj X.property) Ab.{u + 1}] :
    PreservesFiniteColimits
      ((SmallEtale.inclusion B X.obj X.property).sheafPushforwardContinuous Ab.{u + 1}
        (SmallEtale.topology B X.obj X.property)
        (BigEtaleOver.topology B X.obj X.property)) := by
  have := smallEtaleInclusion_isCocontinuous B X.obj X.property
  have adj := (SmallEtale.inclusion B X.obj X.property).sheafAdjunctionPullbackCocontinuous
    Ab.{u + 1} (SmallEtale.topology B X.obj X.property)
    (BigEtaleOver.topology B X.obj X.property)
  have : PreservesFiniteColimits
      ((SmallEtale.inclusion B X.obj X.property).sheafPullbackCocontinuous Ab.{u + 1}
        (SmallEtale.topology B X.obj X.property)
        (BigEtaleOver.topology B X.obj X.property)) :=
    (adj.leftAdjoint_preservesColimits.{u + 1, u + 1}).preservesFiniteColimits
  exact preservesFiniteColimits_of_natIso
    ((SmallEtale.inclusion B X.obj X.property
        ).sheafPullbackCocontinuousIsoSheafPushforwardContinuous
      Ab.{u + 1} (SmallEtale.topology B X.obj X.property)
      (BigEtaleOver.topology B X.obj X.property))

/-- **Stacks 075A, undrived.** Direct image of abelian sheaves along `f` on the big étale site
followed by restriction to the small étale site of `S` agrees with restriction to the small
étale site of `T` followed by direct image on the small étale sites. -/
public def bigSmallEtalePushforwardRestrictionIso (T S : B.Scheme) (f : T ⟶ S)
    [HasSheafify (BigEtaleOver.topology B T.obj T.property) Ab.{u + 1}]
    [HasSheafify (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1}] :
    (Over.map f).sheafPushforwardCocontinuous Ab.{u + 1}
        (BigEtaleOver.topology B T.obj T.property)
        (BigEtaleOver.topology B S.obj S.property) ⋙
      (SmallEtale.inclusion B S.obj S.property).sheafPushforwardContinuous Ab.{u + 1}
        (SmallEtale.topology B S.obj S.property)
        (BigEtaleOver.topology B S.obj S.property) ≅
    (SmallEtale.inclusion B T.obj T.property).sheafPushforwardContinuous Ab.{u + 1}
        (SmallEtale.topology B T.obj T.property)
        (BigEtaleOver.topology B T.obj T.property) ⋙
      (smallEtaleBaseChange B f).sheafPushforwardContinuous Ab.{u + 1}
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
  exact Functor.isoWhiskerRight
      ((Over.mapPullbackAdj f).sheafPushforwardCocontinuousIso Ab.{u + 1})
      ((SmallEtale.inclusion B S.obj S.property).sheafPushforwardContinuous Ab.{u + 1}
        (SmallEtale.topology B S.obj S.property)
        (BigEtaleOver.topology B S.obj S.property)) ≪≫
    Functor.sheafPushforwardContinuousComp
      (SmallEtale.inclusion B S.obj S.property) (Over.pullback f) Ab.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (BigEtaleOver.topology B S.obj S.property)
      (BigEtaleOver.topology B T.obj T.property) ≪≫
    (Functor.sheafPushforwardContinuousComp
      (smallEtaleBaseChange B f) (SmallEtale.inclusion B T.obj T.property) Ab.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)
      (BigEtaleOver.topology B T.obj T.property)).symm

/-- **Stacks 075A, part (1).** The derived direct image on the big étale site commutes
naturally with restriction to the small étale site. -/
public def bigSmallEtaleDerivedPushforwardIso
    (T S : B.Scheme) (f : T ⟶ S)
    [HasSheafify (BigEtaleOver.topology B T.obj T.property) Ab.{u + 1}]
    [HasSheafify (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1}]
    [HasSheafify (SmallEtale.topology B T.obj T.property) Ab.{u + 1}]
    [HasSheafify (SmallEtale.topology B S.obj S.property) Ab.{u + 1}]
    [HasDerivedCategory.{wTb} (Sheaf (BigEtaleOver.topology B T.obj T.property) Ab.{u + 1})]
    [HasDerivedCategory.{wSb} (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1})]
    [HasDerivedCategory.{wTs} (Sheaf (SmallEtale.topology B T.obj T.property) Ab.{u + 1})]
    [HasDerivedCategory.{wSs} (Sheaf (SmallEtale.topology B S.obj S.property) Ab.{u + 1})]
    [((Over.map f).sheafPushforwardCocontinuous Ab.{u + 1}
      (BigEtaleOver.topology B T.obj T.property)
      (BigEtaleOver.topology B S.obj S.property)).Additive]
    [((smallEtaleBaseChange B f).sheafPushforwardContinuous
      Ab.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).Additive]
    [((SmallEtale.inclusion B S.obj S.property).sheafPushforwardContinuous
      Ab.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (BigEtaleOver.topology B S.obj S.property)).Additive]
    [((SmallEtale.inclusion B T.obj T.property).sheafPushforwardContinuous
      Ab.{u + 1}
      (SmallEtale.topology B T.obj T.property)
      (BigEtaleOver.topology B T.obj T.property)).Additive]
    (RfBig : DerivedCategory (Sheaf (BigEtaleOver.topology B T.obj T.property) Ab.{u + 1}) ⥤
      DerivedCategory (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1}))
    (RfSmall : DerivedCategory (Sheaf (SmallEtale.topology B T.obj T.property) Ab.{u + 1}) ⥤
      DerivedCategory (Sheaf (SmallEtale.topology B S.obj S.property) Ab.{u + 1}))
    (RresS : DerivedCategory (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1}) ⥤
      DerivedCategory (Sheaf (SmallEtale.topology B S.obj S.property) Ab.{u + 1}))
    (RresT : DerivedCategory (Sheaf (BigEtaleOver.topology B T.obj T.property) Ab.{u + 1}) ⥤
      DerivedCategory (Sheaf (SmallEtale.topology B T.obj T.property) Ab.{u + 1}))
    (αbig : homotopyToDerived
      ((Over.map f).sheafPushforwardCocontinuous Ab.{u + 1}
        (BigEtaleOver.topology B T.obj T.property)
        (BigEtaleOver.topology B S.obj S.property)) ⟶ DerivedCategory.Qh ⋙ RfBig)
    (αsmall : homotopyToDerived
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous
        Ab.{u + 1}
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)) ⟶ DerivedCategory.Qh ⋙ RfSmall)
    (αresS : homotopyToDerived
      ((SmallEtale.inclusion B S.obj S.property).sheafPushforwardContinuous Ab.{u + 1}
        (SmallEtale.topology B S.obj S.property)
        (BigEtaleOver.topology B S.obj S.property)) ⟶ DerivedCategory.Qh ⋙ RresS)
    (αresT : homotopyToDerived
      ((SmallEtale.inclusion B T.obj T.property).sheafPushforwardContinuous Ab.{u + 1}
        (SmallEtale.topology B T.obj T.property)
        (BigEtaleOver.topology B T.obj T.property)) ⟶ DerivedCategory.Qh ⋙ RresT)
    [RfBig.IsRightDerivedFunctor αbig (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    [RfSmall.IsRightDerivedFunctor αsmall (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    [RresS.IsRightDerivedFunctor αresS (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    [RresT.IsRightDerivedFunctor αresT (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))] :
    RfBig ⋙ RresS ≅ RresT ⋙ RfSmall := by
  let AT := Sheaf (BigEtaleOver.topology B T.obj T.property) Ab.{u + 1}
  let pushBig := (Over.map f).sheafPushforwardCocontinuous Ab.{u + 1}
    (BigEtaleOver.topology B T.obj T.property)
    (BigEtaleOver.topology B S.obj S.property)
  let pushSmall := (smallEtaleBaseChange B f).sheafPushforwardContinuous Ab.{u + 1}
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property)
  let resS := (SmallEtale.inclusion B S.obj S.property).sheafPushforwardContinuous Ab.{u + 1}
    (SmallEtale.topology B S.obj S.property)
    (BigEtaleOver.topology B S.obj S.property)
  let resT := (SmallEtale.inclusion B T.obj T.property).sheafPushforwardContinuous Ab.{u + 1}
    (SmallEtale.topology B T.obj T.property)
    (BigEtaleOver.topology B T.obj T.property)
  let : IsGrothendieckAbelian.{u + 1, u + 1, u + 2} AT :=
    sheaf_isGrothendieckAbelian (BigEtaleOver.topology B T.obj T.property)
  let : IsGrothendieckAbelian.{u + 1, u + 1, u + 2}
      (Sheaf (SmallEtale.topology B T.obj T.property) Ab.{u + 1}) :=
    sheaf_isGrothendieckAbelian (SmallEtale.topology B T.obj T.property)
  -- The big-site direct image followed by restriction to `S`, as a right derived functor.
  let αleft := derivedCompositeUnit pushBig resS RfBig RresS αbig αresS
  have hαleft : (RfBig ⋙ RresS).IsRightDerivedFunctor αleft
      (HomotopyCategory.quasiIso AT (ComplexShape.up ℤ)) := by
    apply derivedComposite_isRightDerived pushBig resS RfBig RresS αbig αresS
    intro I hI
    let : IsIso (αbig.app
        ((HomotopyCategory.quotient AT (ComplexShape.up ℤ)).obj I)) :=
      rightDerivedUnit_isIso_app_of_isKInjective
        (homotopyToDerived pushBig) RfBig αbig I hI
    let : IsIso αresS := exactRightDerivedUnit_isIso resS RresS αresS
    dsimp [derivedCompositeUnit]
    infer_instance
  -- Restriction to `T` followed by the small-site direct image, as a right derived functor.
  let αright := derivedCompositeUnit resT pushSmall RresT RfSmall αresT αsmall
  have hαright : (RresT ⋙ RfSmall).IsRightDerivedFunctor αright
      (HomotopyCategory.quasiIso AT (ComplexShape.up ℤ)) := by
    apply derivedComposite_isRightDerived resT pushSmall RresT RfSmall αresT αsmall
    intro I hI
    let : IsIso αresT := exactRightDerivedUnit_isIso resT RresT αresT
    let I' := ((resT.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
    let : CochainComplex.IsKInjective I' :=
      isKInjective_smallEtaleRestriction B T.obj T.property I
    have hsmall := rightDerivedUnit_isIso_app_of_isKInjective
      (homotopyToDerived pushSmall) RfSmall αsmall I' inferInstance
    dsimp [derivedCompositeUnit]
    have : IsIso (αsmall.app
        ((resT.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient AT (ComplexShape.up ℤ)).obj I))) := by
      change IsIso (αsmall.app ((HomotopyCategory.quotient
        (Sheaf (SmallEtale.topology B T.obj T.property) Ab.{u + 1})
        (ComplexShape.up ℤ)).obj I'))
      exact hsmall
    infer_instance
  -- Transport the undrived commutation to the homotopy categories and descend.
  let underH :=
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (pushBig ⋙ resS))
      (ComplexShape.up ℤ)).symm ≪≫
      Functor.mapHomotopyCategoryCompIso
        (bigSmallEtalePushforwardRestrictionIso B T S f) (ComplexShape.up ℤ)
  exact Functor.rightDerivedNatIso (RfBig ⋙ RresS) (RresT ⋙ RfSmall) αleft αright
    (HomotopyCategory.quasiIso AT (ComplexShape.up ℤ))
    (Functor.isoWhiskerRight underH DerivedCategory.Qh)

end AlgebraicGeometry

end
