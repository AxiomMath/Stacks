module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.DerivedRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.Existence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.SheafCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.RingedToposTwoIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSiteGrothendieck
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.CohomologyAfterRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.RingedBigSiteHom
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.RingedProjectionAndIf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExactness
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.ExactSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.KInjectiveRestrictionAlongOverMapEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BaseChangeCommutation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.CompositionOfDirectImages
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackToposGeneral
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.BaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallToBigTopos
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory
public import StacksCore.Tactic.StacksAttribute

/-!
# Derived direct image on the big étale site, restriction and base change (Stacks 075A)

Let `f : T ⟶ S` be a morphism of a big étale site `B`, let `g : S' ⟶ S` be an object of
`(Sch/S)_étale` and let `T' = T ×_S S'`, with projections `f' : T' ⟶ S'` and `g' : T' ⟶ T`.
Stacks 075A:

1. for `K` in `D((Sch/T)_étale)`, `(Rf_{big, *}K)|_{S_étale} = Rf_{small, *}(K|_{T_étale})`;
2. the same for `K` in `D((Sch/T)_étale, 𝒪)`, in `D(Mod(S_étale, 𝒪_S))`;
3. for `K` in `D((Sch/T)_étale)`, `i_g^{-1}(Rf_{big, *}K) = Rf'_{small, *}(i_{g'}^{-1}K)`;
4. for `K` in `D((Sch/T)_étale, 𝒪)`, `i_g^*(Rf_{big, *}K) = Rf'_{small, *}(i_{g'}^*K)`;
5. for `K` in `D((Sch/T)_étale)`, `g_big^{-1}(Rf_{big, *}K) = Rf'_{big, *}((g'_big)^{-1}K)`;
6. for `K` in `D((Sch/T)_étale, 𝒪)`, `g_big^*(Rf_{big, *}K) = Rf'_{big, *}((g'_big)^*K)`.

Each is stated as a natural isomorphism of functors between unbounded derived categories, with
the canonical derived direct images (total right derived functors of the degreewise direct
images) and with the exact restriction and inverse-image functors applied degreewise.

## Main results

* `AlgebraicGeometry.bigSmallEtaleDerivedPushforwardRestrictionIso`: part (1).
* `AlgebraicGeometry.bigSmallEtaleDerivedModulePushforwardRestrictionIso`: part (2).
* `AlgebraicGeometry.smallEtaleDerivedPushforwardRestrictionAlongIso`: part (3).
* `AlgebraicGeometry.smallEtaleDerivedModulePushforwardRestrictionAlongIso`: part (4).
* `AlgebraicGeometry.bigEtaleDerivedPushforwardInverseImageIso`: part (5).
* `AlgebraicGeometry.bigEtaleDerivedModulePushforwardInverseImageIso`: part (6).
* `AlgebraicGeometry.bigSmallEtaleModulePushforwardRestrictionIso` and
  `AlgebraicGeometry.bigEtaleModulePushforwardInverseImageIso`: the underived comparisons for
  `𝒪`-modules (Stacks 0759 and the module form of 0DDA).
* `AlgebraicGeometry.isKInjective_bigEtaleModuleInverseImage`: `g_big^*` preserves K-injective
  complexes of `𝒪`-modules (Stacks 08FI).

## Implementation notes

Abelian sheaves are taken with values in `Ab.{u + 1}`, as in `bigSmallEtaleDerivedPushforwardIso`;
`𝒪`-modules are taken with sections in `Type u`, the universe of the structure rings. The derived
categories are the standard ones, `HasDerivedCategory.standard`.

## References

* [Stacks Project, Tag 075A](https://stacks.math.columbia.edu/tag/075A)
* [Stacks Project, Tag 0758](https://stacks.math.columbia.edu/tag/0758)
* [Stacks Project, Tag 0759](https://stacks.math.columbia.edu/tag/0759)
* [Stacks Project, Tag 0DDA](https://stacks.math.columbia.edu/tag/0DDA)
* [Stacks Project, Tag 0EZ0](https://stacks.math.columbia.edu/tag/0EZ0)
* [Stacks Project, Tag 0FN5](https://stacks.math.columbia.edu/tag/0FN5)
* [Stacks Project, Tag 0D6E](https://stacks.math.columbia.edu/tag/0D6E)
* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.Localization

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {T S : B.Scheme} (f : T ⟶ S)

section Abelian

attribute [local instance] HasDerivedCategory.standard

/-- Abelian sheaves on the big étale site over an object of `B` form a Grothendieck abelian
category. -/
instance bigEtaleOver_abelianSheaves_isGrothendieckAbelian (X : B.Scheme) :
    IsGrothendieckAbelian.{u + 1} (Sheaf (BigEtaleOver.topology B X.obj X.property) Ab.{u + 1}) :=
  sheaf_isGrothendieckAbelian _

/-- Abelian sheaves on the small étale site of an object of `B` form a Grothendieck abelian
category. -/
instance smallEtale_abelianSheaves_isGrothendieckAbelian (X : B.Scheme) :
    IsGrothendieckAbelian.{u + 1} (Sheaf (SmallEtale.topology B X.obj X.property) Ab.{u + 1}) :=
  sheaf_isGrothendieckAbelian _

/-- The direct image `f_{big, *}` of abelian sheaves on the big étale sites. -/
abbrev bigEtaleAbelianPushforward :
    Sheaf (BigEtaleOver.topology B T.obj T.property) Ab.{u + 1} ⥤
      Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1} :=
  (Over.map f).sheafPushforwardCocontinuous Ab.{u + 1}
    (BigEtaleOver.topology B T.obj T.property) (BigEtaleOver.topology B S.obj S.property)

/-- The direct image `f_{small, *}` of abelian sheaves on the small étale sites. -/
abbrev smallEtaleAbelianPushforward :
    Sheaf (SmallEtale.topology B T.obj T.property) Ab.{u + 1} ⥤
      Sheaf (SmallEtale.topology B S.obj S.property) Ab.{u + 1} :=
  (smallEtaleBaseChange B f).sheafPushforwardContinuous Ab.{u + 1}
    (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)

/-- Restriction `K ↦ K|_{X_étale}` of abelian sheaves from the big étale site over `X` to the
small étale site of `X`, that is the direct image `π_{X, *}`. -/
abbrev smallEtaleAbelianRestriction (X : B.Scheme) :
    Sheaf (BigEtaleOver.topology B X.obj X.property) Ab.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X.obj X.property) Ab.{u + 1} :=
  (SmallEtale.inclusion B X.obj X.property).sheafPushforwardContinuous Ab.{u + 1}
    (SmallEtale.topology B X.obj X.property) (BigEtaleOver.topology B X.obj X.property)

/-- The direct image `f_{big, *}` of abelian sheaves is additive. -/
instance bigEtaleAbelianPushforward_additive : (bigEtaleAbelianPushforward B f).Additive := by
  have := ((Over.map f).sheafAdjunctionCocontinuous Ab.{u + 1}
    (BigEtaleOver.topology B T.obj T.property)
    (BigEtaleOver.topology B S.obj S.property)).isRightAdjoint
  exact Functor.additive_of_preserves_binary_products _

/-- The direct image `f_{small, *}` of abelian sheaves is additive. -/
instance smallEtaleAbelianPushforward_additive : (smallEtaleAbelianPushforward B f).Additive :=
  ⟨rfl⟩

/-- The restriction `K ↦ K|_{X_étale}` of abelian sheaves is additive. -/
instance smallEtaleAbelianRestriction_additive (X : B.Scheme) :
    (smallEtaleAbelianRestriction B X).Additive :=
  ⟨rfl⟩

/-- The unbounded derived direct image `Rf_{big, *} : D((Sch/T)_étale) ⥤ D((Sch/S)_étale)`. -/
abbrev bigEtaleDerivedPushforward :
    DerivedCategory (Sheaf (BigEtaleOver.topology B T.obj T.property) Ab.{u + 1}) ⥤
      DerivedCategory (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1}) :=
  haveI := Stacks.Cohomology.UnboundedComplexes.hasPointwiseRightDerivedFunctor
    (homotopyToDerived (bigEtaleAbelianPushforward B f))
  (homotopyToDerived (bigEtaleAbelianPushforward B f)).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

/-- The comparison `f_{big, *} ⟶ Rf_{big, *}`. -/
abbrev bigEtaleDerivedPushforwardUnit :
    homotopyToDerived (bigEtaleAbelianPushforward B f) ⟶
      DerivedCategory.Qh ⋙ bigEtaleDerivedPushforward B f :=
  haveI := Stacks.Cohomology.UnboundedComplexes.hasPointwiseRightDerivedFunctor
    (homotopyToDerived (bigEtaleAbelianPushforward B f))
  (homotopyToDerived (bigEtaleAbelianPushforward B f)).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

/-- The unbounded derived direct image `Rf_{small, *} : D(T_étale) ⥤ D(S_étale)`. -/
abbrev smallEtaleDerivedPushforward :
    DerivedCategory (Sheaf (SmallEtale.topology B T.obj T.property) Ab.{u + 1}) ⥤
      DerivedCategory (Sheaf (SmallEtale.topology B S.obj S.property) Ab.{u + 1}) :=
  haveI := Stacks.Cohomology.UnboundedComplexes.hasPointwiseRightDerivedFunctor
    (homotopyToDerived (smallEtaleAbelianPushforward B f))
  (homotopyToDerived (smallEtaleAbelianPushforward B f)).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

/-- The comparison `f_{small, *} ⟶ Rf_{small, *}`. -/
abbrev smallEtaleDerivedPushforwardUnit :
    homotopyToDerived (smallEtaleAbelianPushforward B f) ⟶
      DerivedCategory.Qh ⋙ smallEtaleDerivedPushforward B f :=
  haveI := Stacks.Cohomology.UnboundedComplexes.hasPointwiseRightDerivedFunctor
    (homotopyToDerived (smallEtaleAbelianPushforward B f))
  (homotopyToDerived (smallEtaleAbelianPushforward B f)).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

/-- For a morphism `f : T ⟶ S` of schemes and `K` in the unbounded derived category
`D((Sch/T)_étale)` of abelian sheaves on the big étale site,
`(Rf_{big, *}K)|_{S_étale} = Rf_{small, *}(K|_{T_étale})` in `D(S_étale)`, naturally in `K`. -/
@[stacks 075A "part (1)"]
def bigSmallEtaleDerivedPushforwardRestrictionIso :
    bigEtaleDerivedPushforward B f ⋙ (smallEtaleAbelianRestriction B S).mapDerivedCategory ≅
      (smallEtaleAbelianRestriction B T).mapDerivedCategory ⋙ smallEtaleDerivedPushforward B f :=
  haveI := Stacks.Cohomology.UnboundedComplexes.hasPointwiseRightDerivedFunctor
    (homotopyToDerived (bigEtaleAbelianPushforward B f))
  haveI := Stacks.Cohomology.UnboundedComplexes.hasPointwiseRightDerivedFunctor
    (homotopyToDerived (smallEtaleAbelianPushforward B f))
  haveI (X : B.Scheme) : (smallEtaleAbelianRestriction B X).mapDerivedCategory.IsRightDerivedFunctor
      (smallEtaleAbelianRestriction B X).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts _ _
      (smallEtaleAbelianRestriction B X).mapDerivedCategoryFactorsh
  haveI : ((Over.map f).sheafPushforwardCocontinuous Ab.{u + 1}
      (BigEtaleOver.topology B T.obj T.property)
      (BigEtaleOver.topology B S.obj S.property)).Additive :=
    bigEtaleAbelianPushforward_additive B f
  bigSmallEtaleDerivedPushforwardIso B T S f _ _ _ _
    (bigEtaleDerivedPushforwardUnit B f) (smallEtaleDerivedPushforwardUnit B f)
    (smallEtaleAbelianRestriction B S).mapDerivedCategoryFactorsh.inv
    (smallEtaleAbelianRestriction B T).mapDerivedCategoryFactorsh.inv

end Abelian

section AbelianBaseChange

attribute [local instance] HasDerivedCategory.standard

variable {X Y : B.Scheme} (g : X ⟶ Y)

/-- The inverse image `g_big^{-1}` of abelian sheaves along `g : X ⟶ Y`: restriction along
postcomposition with `g`. -/
abbrev bigEtaleAbelianInverseImage :
    Sheaf (BigEtaleOver.topology B Y.obj Y.property) Ab.{u + 1} ⥤
      Sheaf (BigEtaleOver.topology B X.obj X.property) Ab.{u + 1} :=
  (Over.map g).sheafPushforwardContinuous Ab.{u + 1}
    (BigEtaleOver.topology B X.obj X.property) (BigEtaleOver.topology B Y.obj Y.property)

/-- The inverse image `i_g^{-1}` of abelian sheaves along `i_g : Sh(X_étale) ⟶ Sh((Sch/Y)_étale)`:
restriction along `V/X ↦ V/Y`. -/
abbrev smallEtaleAbelianRestrictionAlong :
    Sheaf (BigEtaleOver.topology B Y.obj Y.property) Ab.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X.obj X.property) Ab.{u + 1} :=
  (smallEtaleToBigEtaleFunctor B X Y g).sheafPushforwardContinuous Ab.{u + 1}
    (SmallEtale.topology B X.obj X.property) (BigEtaleOver.topology B Y.obj Y.property)

/-- The inverse image `g_big^{-1}` of abelian sheaves is additive. -/
instance bigEtaleAbelianInverseImage_additive : (bigEtaleAbelianInverseImage B g).Additive :=
  ⟨rfl⟩

/-- The inverse image `i_g^{-1}` of abelian sheaves is additive. -/
instance smallEtaleAbelianRestrictionAlong_additive :
    (smallEtaleAbelianRestrictionAlong B g).Additive :=
  ⟨rfl⟩

/-- The inverse image `g_big^{-1}` of abelian sheaves preserves finite limits. -/
instance bigEtaleAbelianInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (bigEtaleAbelianInverseImage B g) := by
  have := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Over.map g) Ab.{u + 1}
    (BigEtaleOver.topology B X.obj X.property)
    (BigEtaleOver.topology B Y.obj Y.property)).isRightAdjoint
  infer_instance

/-- The inverse image `g_big^{-1}` of abelian sheaves preserves finite colimits. -/
instance bigEtaleAbelianInverseImage_preservesFiniteColimits :
    PreservesFiniteColimits (bigEtaleAbelianInverseImage B g) := by
  have adj := (Over.map g).sheafAdjunctionPullbackCocontinuous Ab.{u + 1}
    (BigEtaleOver.topology B X.obj X.property) (BigEtaleOver.topology B Y.obj Y.property)
  have : PreservesFiniteColimits ((Over.map g).sheafPullbackCocontinuous Ab.{u + 1}
      (BigEtaleOver.topology B X.obj X.property) (BigEtaleOver.topology B Y.obj Y.property)) :=
    (adj.leftAdjoint_preservesColimits.{u + 1, u + 1}).preservesFiniteColimits
  exact preservesFiniteColimits_of_natIso
    ((Over.map g).sheafPullbackCocontinuousIsoSheafPushforwardContinuous Ab.{u + 1}
      (BigEtaleOver.topology B X.obj X.property) (BigEtaleOver.topology B Y.obj Y.property))

/-- `i_g^{-1} = π_{X, *} ∘ g_big^{-1}` on abelian sheaves: `V/X ↦ V/Y` is the inclusion of the
small étale site of `X` followed by postcomposition with `g`. -/
def smallEtaleAbelianRestrictionAlongIso :
    smallEtaleAbelianRestrictionAlong B g ≅
      bigEtaleAbelianInverseImage B g ⋙ smallEtaleAbelianRestriction B X :=
  (SmallEtale.inclusion B X.obj X.property).sheafPushforwardContinuousComp (Over.map g)
    Ab.{u + 1} (SmallEtale.topology B X.obj X.property)
    (BigEtaleOver.topology B X.obj X.property) (BigEtaleOver.topology B Y.obj Y.property)

/-- The inverse image `i_g^{-1}` of abelian sheaves preserves finite limits. -/
instance smallEtaleAbelianRestrictionAlong_preservesFiniteLimits :
    PreservesFiniteLimits (smallEtaleAbelianRestrictionAlong B g) :=
  preservesFiniteLimits_of_natIso (smallEtaleAbelianRestrictionAlongIso B g).symm

/-- The inverse image `i_g^{-1}` of abelian sheaves preserves finite colimits. -/
instance smallEtaleAbelianRestrictionAlong_preservesFiniteColimits :
    PreservesFiniteColimits (smallEtaleAbelianRestrictionAlong B g) :=
  preservesFiniteColimits_of_natIso (smallEtaleAbelianRestrictionAlongIso B g).symm

variable (D : CartesianBaseChangeSituation.{u})

/-- The morphism `g : S' ⟶ S` of the big étale site underlying the object `g` of
`(Sch/S)_étale`. -/
abbrev CartesianBaseChangeSituation.gHom : D.S' ⟶ D.S := D.g.hom

/-- Let `f : T ⟶ S` be a morphism of schemes, `g : S' ⟶ S` an object of `(Sch/S)_étale` and
`T' = T ×_S S'` with projections `f' : T' ⟶ S'` and `g' : T' ⟶ T`. For `K` in `D((Sch/T)_étale)`,
`g_big^{-1}(Rf_{big, *}K) = Rf'_{big, *}((g'_big)^{-1}K)` in `D((Sch/S')_étale)`, naturally in `K`.
-/
@[stacks 075A "part (5)"]
def bigEtaleDerivedPushforwardInverseImageIso :
    bigEtaleDerivedPushforward D.B D.f ⋙
        (bigEtaleAbelianInverseImage D.B D.gHom).mapDerivedCategory ≅
      (bigEtaleAbelianInverseImage D.B D.g').mapDerivedCategory ⋙
        bigEtaleDerivedPushforward D.B D.f' :=
  haveI := Stacks.Cohomology.UnboundedComplexes.hasPointwiseRightDerivedFunctor
    (homotopyToDerived (bigEtaleAbelianPushforward D.B D.f))
  haveI := Stacks.Cohomology.UnboundedComplexes.hasPointwiseRightDerivedFunctor
    (homotopyToDerived (bigEtaleAbelianPushforward D.B D.f'))
  haveI {X Y : D.B.Scheme} (g : X ⟶ Y) :
      (bigEtaleAbelianInverseImage D.B g).mapDerivedCategory.IsRightDerivedFunctor
        (bigEtaleAbelianInverseImage D.B g).mapDerivedCategoryFactorsh.inv
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts _ _
      (bigEtaleAbelianInverseImage D.B g).mapDerivedCategoryFactorsh
  haveI : ((Over.map D.f).sheafPushforwardCocontinuous Ab.{u + 1}
      (BigEtaleOver.topology D.B D.T.obj D.T.property)
      (BigEtaleOver.topology D.B D.S.obj D.S.property)).Additive :=
    bigEtaleAbelianPushforward_additive D.B D.f
  haveI : ((Over.map D.f').sheafPushforwardCocontinuous Ab.{u + 1}
      (BigEtaleOver.topology D.B D.T'.obj D.T'.property)
      (BigEtaleOver.topology D.B D.S'.obj D.S'.property)).Additive :=
    bigEtaleAbelianPushforward_additive D.B D.f'
  haveI : (Over.map D.g.hom).IsContinuous
      (BigEtaleOver.topology D.B D.S'.obj D.S'.property)
      (BigEtaleOver.topology D.B D.S.obj D.S.property) :=
    bigEtaleMap_isContinuous D.B D.S' D.S D.gHom
  haveI : ((Over.map D.g.hom).sheafPushforwardContinuous Ab.{u + 1}
      (BigEtaleOver.topology D.B D.S'.obj D.S'.property)
      (BigEtaleOver.topology D.B D.S.obj D.S.property)).Additive := ⟨rfl⟩
  haveI : ((Over.map D.g').sheafPushforwardContinuous Ab.{u + 1}
      (BigEtaleOver.topology D.B D.T'.obj D.T'.property)
      (BigEtaleOver.topology D.B D.T.obj D.T.property)).Additive := ⟨rfl⟩
  bigEtaleDerivedPushforwardBaseChangeIso D _ _ _ _
    (bigEtaleDerivedPushforwardUnit D.B D.f) (bigEtaleDerivedPushforwardUnit D.B D.f')
    (bigEtaleAbelianInverseImage D.B D.gHom).mapDerivedCategoryFactorsh.inv
    (bigEtaleAbelianInverseImage D.B D.g').mapDerivedCategoryFactorsh.inv

/-- In the situation of part (5), for `K` in `D((Sch/T)_étale)`,
`i_g^{-1}(Rf_{big, *}K) = Rf'_{small, *}(i_{g'}^{-1}K)` in `D(S'_étale)`, naturally in `K`. -/
@[stacks 075A "part (3)"]
def smallEtaleDerivedPushforwardRestrictionAlongIso :
    bigEtaleDerivedPushforward D.B D.f ⋙
        (smallEtaleAbelianRestrictionAlong D.B D.gHom).mapDerivedCategory ≅
      (smallEtaleAbelianRestrictionAlong D.B D.g').mapDerivedCategory ⋙
        smallEtaleDerivedPushforward D.B D.f' :=
  Functor.isoWhiskerLeft _ (Dualizing.mapDerivedCategoryCompNatIso _ _ _
      (smallEtaleAbelianRestrictionAlongIso D.B D.gHom).symm).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (bigEtaleDerivedPushforwardInverseImageIso D) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (bigSmallEtaleDerivedPushforwardRestrictionIso D.B D.f') ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Dualizing.mapDerivedCategoryCompNatIso _ _ _
      (smallEtaleAbelianRestrictionAlongIso D.B D.g').symm) _

end AbelianBaseChange

section Modules

/-- The big étale site over an object `X` of `B` with its structure sheaf `𝒪`, as a ringed
topos. -/
abbrev bigEtaleOverRingedTopos (X : B.Scheme) : RingedTopos.{u, u + 1, u} :=
  (bigSiteRingedSite (τ := .etale) B X.obj X.property).toRingedTopos

/-- The small étale site of an object `X` of `B` with its structure sheaf `𝒪_X`, as a ringed
topos. -/
abbrev smallEtaleRingedTopos (X : B.Scheme) : RingedTopos.{u, u + 1, u} :=
  (smallEtaleRingedSite B X.obj X.property).toRingedTopos

/-- Sheafification of abelian presheaves exists on the big étale site over `X`. -/
instance bigEtaleOverRingedTopos_hasSheafify (X : B.Scheme) :
    HasSheafify (bigEtaleOverRingedTopos B X).J AddCommGrpCat.{u} :=
  BigEtaleOver.hasSheafify' B X.obj X.property

/-- Weak sheafification of abelian presheaves exists on the big étale site over `X`. -/
instance bigEtaleOverRingedTopos_hasWeakSheafify (X : B.Scheme) :
    HasWeakSheafify (bigEtaleOverRingedTopos B X).J AddCommGrpCat.{u} :=
  (BigEtaleOver.hasSheafify' B X.obj X.property).isRightAdjoint

/-- On the big étale site over `X`, a morphism of abelian presheaves becomes an isomorphism
after sheafification exactly when it is locally bijective. -/
instance bigEtaleOverRingedTopos_wEqualsLocallyBijective (X : B.Scheme) :
    (bigEtaleOverRingedTopos B X).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  BigEtaleOver.wEqualsLocallyBijective' B X.obj X.property

/-- Sheafification of presheaves of types exists on the big étale site over `X`. -/
instance bigEtaleOverRingedTopos_hasSheafifyType (X : B.Scheme) :
    HasSheafify (bigEtaleOverRingedTopos B X).J (Type u) :=
  haveI : EssentiallySmall.{u} (bigEtaleOverRingedTopos B X).C :=
    essentiallySmall_overBase (τ := .etale) B X.obj X.property
  hasSheafifyEssentiallySmallSite.{u, u, u + 1, u + 1, u} _ _

/-- The category of `𝒪`-modules on the big étale site over `X` is a Grothendieck abelian
category. -/
instance bigEtaleOverRingedTopos_isGrothendieckAbelian (X : B.Scheme) :
    IsGrothendieckAbelian.{u} (bigEtaleOverRingedTopos B X).Modules :=
  haveI : EssentiallySmall.{u} (bigEtaleOverRingedTopos B X).C :=
    essentiallySmall_overBase (τ := .etale) B X.obj X.property
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall (R := _)

/-- `π_X : ((Sch/X)_étale, 𝒪) ⟶ (X_étale, 𝒪_X)` as a morphism of ringed topoi. -/
abbrev bigToSmallEtaleRingedToposHom (X : B.Scheme) :
    RingedToposHom (bigEtaleOverRingedTopos B X) (smallEtaleRingedTopos B X) :=
  (smallEtalePiRingedSiteHom B (S := X)).toRingedToposHom

/-- `f_big : ((Sch/T)_étale, 𝒪) ⟶ ((Sch/S)_étale, 𝒪)` as a morphism of ringed topoi. -/
abbrev bigEtaleRingedToposHom :
    RingedToposHom (bigEtaleOverRingedTopos B T) (bigEtaleOverRingedTopos B S) :=
  (bigSiteRingedSiteHom (τ := .etale) B f).toRingedToposHom

/-- The direct image `π_{X, *}` of `𝒪`-modules is additive. -/
instance bigToSmallEtaleModules_additive (X : B.Scheme) :
    (bigToSmallEtaleRingedToposHom B X).pushforwardModules.Additive :=
  RingedToposHom.pushforwardModules_additive (X := bigEtaleOverRingedTopos B X)
    (Y := smallEtaleRingedTopos B X) _

/-- The direct image `f_{big, *}` of `𝒪`-modules is additive. -/
instance bigEtaleModulePushforward_additive :
    (bigEtaleRingedToposHom B f).pushforwardModules.Additive :=
  RingedToposHom.pushforwardModules_additive (X := bigEtaleOverRingedTopos B T)
    (Y := bigEtaleOverRingedTopos B S) _

/-- The direct image `f_{small, *}` of `𝒪`-modules is additive. -/
instance smallEtaleModulePushforward_additive :
    (smallEtaleRingedToposHom B f).pushforwardModules.Additive :=
  RingedToposHom.pushforwardModules_additive (X := smallEtaleRingedTopos B T)
    (Y := smallEtaleRingedTopos B S) _

/-- Restriction of `𝒪`-modules to the small étale site, `π_{X, *}`, is the restriction functor
along the inclusion of the small étale site. -/
def bigToSmallEtaleModulesIso (X : B.Scheme) :
    (bigToSmallEtaleRingedToposHom B X).pushforwardModules ≅
      Stacks.SheafOfModules.restriction (SmallEtale.topology B X.obj X.property)
        (BigEtaleOver.topology B X.obj X.property) (SmallEtale.inclusion B X.obj X.property)
        (Stacks.SheafOfModules.Tensor.ringSheaf (bigEtaleOverRingedTopos B X).O) :=
  (smallEtalePiRingedSiteHom B (S := X)).pushforwardToposIsoGeneral

/-- The direct image `π_{X, *}` of `𝒪`-modules preserves finite limits. -/
instance bigToSmallEtaleModules_preservesFiniteLimits (X : B.Scheme) :
    PreservesFiniteLimits (bigToSmallEtaleRingedToposHom B X).pushforwardModules :=
  @preservesFiniteLimits_of_natIso _ _ _ _ _ _ (bigToSmallEtaleModulesIso B X).symm (by
    exact Stacks.SheafOfModules.restriction_preservesFiniteLimits
      (SmallEtale.topology B X.obj X.property)
      (BigEtaleOver.topology B X.obj X.property) (SmallEtale.inclusion B X.obj X.property)
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigEtaleOverRingedTopos B X).O))

/-- The direct image `π_{X, *}` of `𝒪`-modules preserves finite colimits. -/
instance bigToSmallEtaleModules_preservesFiniteColimits (X : B.Scheme) :
    PreservesFiniteColimits (bigToSmallEtaleRingedToposHom B X).pushforwardModules :=
  haveI := smallEtaleInclusion_isCocontinuous B X.obj X.property
  @preservesFiniteColimits_of_natIso _ _ _ _ _ _ (bigToSmallEtaleModulesIso B X).symm (by
    exact Stacks.SheafOfModules.restriction_preservesFiniteColimits
      (SmallEtale.topology B X.obj X.property)
      (BigEtaleOver.topology B X.obj X.property) (SmallEtale.inclusion B X.obj X.property)
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigEtaleOverRingedTopos B X).O))

/-- The two composite structure maps `𝒪_S ⟶ (π_S ∘ f_big)_* 𝒪` and `𝒪_S ⟶ (f_small ∘ π_T)_* 𝒪`
agree: on an étale `V/S` both are pullback of functions along `T ×_S V ⟶ V`. -/
theorem bigSmallEtale_compositeStructureMap_eq :
    letI := (smallEtalePiRingedSiteHom B (S := S)).toRingedToposSiteHom.isContinuous
    (smallEtalePiRingedSiteHom B (S := S)).toRingedToposSiteHom.fSharpRing ≫
        ((SmallEtale.inclusion B S.obj S.property).sheafPushforwardContinuous RingCat.{u}
          (SmallEtale.topology B S.obj S.property) (BigEtaleOver.topology B S.obj S.property)).map
          (bigSiteRingedSiteHom (τ := .etale) B f).toRingedToposSiteHom.fSharpRing =
      (smallEtaleRingedSiteHom B f).toRingedToposSiteHom.fSharpRing ≫
        ((smallEtaleBaseChange B f).sheafPushforwardContinuous RingCat.{u}
          (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)).map
          (smallEtalePiRingedSiteHom B (S := T)).toRingedToposSiteHom.fSharpRing := by
  apply ObjectProperty.hom_ext
  ext V x
  rfl

/-- The comparison of Stacks 0759 for `𝒪`-modules, for the site-presented direct images. -/
def bigSmallEtaleModulePushforwardToposIso :
    (bigSiteRingedSiteHom (τ := .etale) B f).toRingedToposSiteHom.pushforwardTopos ⋙
        (smallEtalePiRingedSiteHom B (S := S)).toRingedToposSiteHom.pushforwardTopos ≅
      (smallEtalePiRingedSiteHom B (S := T)).toRingedToposSiteHom.pushforwardTopos ⋙
        (smallEtaleRingedSiteHom B f).toRingedToposSiteHom.pushforwardTopos :=
  letI := (smallEtalePiRingedSiteHom B (S := S)).toRingedToposSiteHom.isContinuous
  letI := (smallEtalePiRingedSiteHom B (S := T)).toRingedToposSiteHom.isContinuous
  letI := (bigSiteRingedSiteHom (τ := .etale) B f).toRingedToposSiteHom.isContinuous
  letI := (smallEtaleRingedSiteHom B f).toRingedToposSiteHom.isContinuous
  letI := Functor.isContinuous_comp (smallEtalePiRingedSiteHom B (S := S)).toRingedToposSiteHom.u
    (bigSiteRingedSiteHom (τ := .etale) B f).toRingedToposSiteHom.u
    (smallEtaleRingedSite B S.obj S.property).toRingedTopos.J
    (bigSiteRingedSite (τ := .etale) B S.obj S.property).toRingedTopos.J
    (bigSiteRingedSite (τ := .etale) B T.obj T.property).toRingedTopos.J
  SheafOfModules.pushforwardComp
      (smallEtalePiRingedSiteHom B (S := S)).toRingedToposSiteHom.fSharpRing
      (bigSiteRingedSiteHom (τ := .etale) B f).toRingedToposSiteHom.fSharpRing ≪≫
    SheafOfModules.pushforwardCongr (by exact bigSmallEtale_compositeStructureMap_eq B f) ≪≫
    (SheafOfModules.pushforwardComp
      (smallEtaleRingedSiteHom B f).toRingedToposSiteHom.fSharpRing
      (smallEtalePiRingedSiteHom B (S := T)).toRingedToposSiteHom.fSharpRing).symm

/-- **Stacks 0759 for `𝒪`-modules.** `(f_{big, *}ℱ)|_{S_étale} = f_{small, *}(ℱ|_{T_étale})` as
`𝒪_S`-modules, naturally in the `𝒪`-module `ℱ`. -/
def bigSmallEtaleModulePushforwardRestrictionIso :
    (bigEtaleRingedToposHom B f).pushforwardModules ⋙
        (bigToSmallEtaleRingedToposHom B S).pushforwardModules ≅
      (bigToSmallEtaleRingedToposHom B T).pushforwardModules ⋙
        (smallEtaleRingedToposHom B f).pushforwardModules :=
  Functor.isoWhiskerRight (bigSiteRingedSiteHom (τ := .etale) B f).pushforwardToposIsoGeneral _ ≪≫
    Functor.isoWhiskerLeft _ (smallEtalePiRingedSiteHom B (S := S)).pushforwardToposIsoGeneral ≪≫
    bigSmallEtaleModulePushforwardToposIso B f ≪≫
    Functor.isoWhiskerRight
      (smallEtalePiRingedSiteHom B (S := T)).pushforwardToposIsoGeneral.symm _ ≪≫
    Functor.isoWhiskerLeft _ (smallEtaleRingedSiteHom B f).pushforwardToposIsoGeneral.symm

attribute [local instance 10000] HasDerivedCategory.standard in
/-- For a morphism `f : T ⟶ S` of schemes and `K` in the unbounded derived category
`D((Sch/T)_étale, 𝒪)` of `𝒪`-modules on the big étale site,
`(Rf_{big, *}K)|_{S_étale} = Rf_{small, *}(K|_{T_étale})` in `D(Mod(S_étale, 𝒪_S))`, naturally in
`K`. -/
@[stacks 075A "part (2)"]
def bigSmallEtaleDerivedModulePushforwardRestrictionIso :
    Stacks.Cohomology.DerivedPushforward.derivedPushforward (X := bigEtaleOverRingedTopos B T)
        (Y := bigEtaleOverRingedTopos B S) (bigEtaleRingedToposHom B f) ⋙
        (bigToSmallEtaleRingedToposHom B S).pushforwardModules.mapDerivedCategory ≅
      (bigToSmallEtaleRingedToposHom B T).pushforwardModules.mapDerivedCategory ⋙
        Stacks.Cohomology.DerivedPushforward.derivedPushforward (X := smallEtaleRingedTopos B T)
          (Y := smallEtaleRingedTopos B S) (smallEtaleRingedToposHom B f) :=
  RingedToposHom.derivedPushforwardExactSquareIso (bigEtaleRingedToposHom B f)
    (bigToSmallEtaleRingedToposHom B S) (bigToSmallEtaleRingedToposHom B T)
    (smallEtaleRingedToposHom B f) (bigSmallEtaleModulePushforwardRestrictionIso B f)

section ModuleBaseChange

variable {X Y : B.Scheme} (g : X ⟶ Y)

/-- The morphism of ringed topoi, presented by the continuous functor `Over.map g`, whose direct
image is the restriction `g_big^{-1}` from `(Sch/Y)_étale` to `(Sch/X)_étale`; its structure map
is the identity, the structure sheaf of `(Sch/X)_étale` being the restriction of that of
`(Sch/Y)_étale` on the nose. -/
def bigEtaleRestrictionRingedToposSiteHom :
    RingedToposSiteHom (bigEtaleOverRingedTopos B Y) (bigEtaleOverRingedTopos B X) where
  u := Over.map g
  isContinuous := bigEtaleMap_isContinuous B X Y g
  fSharp := 𝟙 _

/-- The inverse image `g_big^* = g_big^{-1}` of `𝒪`-modules along `g : X ⟶ Y`: restriction along
postcomposition with `g`. -/
abbrev bigEtaleModuleInverseImage {X Y : B.Scheme} (g : X ⟶ Y) :
    (bigEtaleOverRingedTopos B Y).Modules ⥤ (bigEtaleOverRingedTopos B X).Modules :=
  (bigEtaleRestrictionRingedToposSiteHom B g).pushforwardTopos

/-- The inverse image `g_big^*` of `𝒪`-modules is additive. -/
instance bigEtaleModuleInverseImage_additive : (bigEtaleModuleInverseImage B g).Additive :=
  RingedToposSiteHom.pushforwardTopos_additive _

/-- The inverse image `g_big^*` of `𝒪`-modules preserves finite limits. -/
instance bigEtaleModuleInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (bigEtaleModuleInverseImage B g) :=
  letI := (bigEtaleRestrictionRingedToposSiteHom B g).isContinuous
  Stacks.SheafOfModules.restriction_preservesFiniteLimits
    (bigEtaleOverRingedTopos B X).J (bigEtaleOverRingedTopos B Y).J
    (bigEtaleRestrictionRingedToposSiteHom B g).u
    (Stacks.SheafOfModules.Tensor.ringSheaf (bigEtaleOverRingedTopos B Y).O)

/-- The inverse image `g_big^*` of `𝒪`-modules preserves finite colimits. -/
instance bigEtaleModuleInverseImage_preservesFiniteColimits :
    PreservesFiniteColimits (bigEtaleModuleInverseImage B g) :=
  letI := (bigEtaleRestrictionRingedToposSiteHom B g).isContinuous
  letI : (bigEtaleRestrictionRingedToposSiteHom B g).u.IsCocontinuous
      (bigEtaleOverRingedTopos B X).J (bigEtaleOverRingedTopos B Y).J :=
    bigEtaleMap_isCocontinuous B X Y g
  Stacks.SheafOfModules.restriction_preservesFiniteColimits
    (bigEtaleOverRingedTopos B X).J (bigEtaleOverRingedTopos B Y).J
    (bigEtaleRestrictionRingedToposSiteHom B g).u
    (Stacks.SheafOfModules.Tensor.ringSheaf (bigEtaleOverRingedTopos B Y).O)

/-- **Stacks 08FI for the big étale sites.** `g_big^*` carries K-injective complexes of
`𝒪`-modules to K-injective complexes. -/
theorem isKInjective_bigEtaleModuleInverseImage
    (I : CochainComplex (bigEtaleOverRingedTopos B Y).Modules ℤ) [hI : I.IsKInjective] :
    CochainComplex.IsKInjective
      (((bigEtaleModuleInverseImage B g).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  have hs : EssentiallySmall.{u} (bigEtaleOverRingedTopos B Y).C :=
    essentiallySmall_overBase (τ := .etale) B Y.obj Y.property
  have hs' : EssentiallySmall.{u} (Over (Over.mk g : (bigEtaleOverRingedTopos B Y).C)) := by
    change EssentiallySmall.{u} (CostructuredArrow (𝟭 _) _)
    infer_instance
  exact Stacks.Cohomology.Localization.isKInjective_restriction_overMap_of_essentiallySmall
    B.topology g (bigEtaleOverRingedTopos B Y).J
    (bigEtaleOverRingedTopos B X).J (bigEtaleOver_topology_eq_of_obj B Y)
    (bigEtaleOver_topology_eq_of_obj B X) (bigEtaleRestrictionRingedToposSiteHom B g).isContinuous
    (Stacks.SheafOfModules.Tensor.ringSheaf (bigEtaleOverRingedTopos B Y).O) hs
    (bigEtaleOverRingedTopos_hasWeakSheafify B Y)
    (bigEtaleOverRingedTopos_wEqualsLocallyBijective B Y)
    (bigEtaleOverRingedTopos_hasWeakSheafify B X)
    (bigEtaleOverRingedTopos_wEqualsLocallyBijective B X)
    (GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u} _).isRightAdjoint
    (GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u} _) I ‹_›

variable (D : CartesianBaseChangeSituation.{u})

/-- The cartesian square `T' ⟶ T`, `T' ⟶ S'`, `T ⟶ S`, `S' ⟶ S` of a base-change situation. -/
theorem CartesianBaseChangeSituation.isPullback : IsPullback D.g' D.f' D.f D.gHom := by
  apply IsPullback.of_map_of_faithful D.B.inclusion
  exact IsPullback.of_hasPullback (D.B.inclusion.map D.f) (D.B.inclusion.map D.g.hom)

/-- The base-change comparison `T' ×_{S'} V ⟶ T ×_S V`, for `V` over `S'`, commutes with the two
projections to `V`. -/
theorem overPullbackBaseChangeIso_inv_app_left_fst (V : Over D.S') :
    ((overPullbackBaseChangeIso D.g' D.f' D.f D.gHom D.isPullback).inv.app V).left ≫
        pullback.fst (V.hom ≫ D.gHom) D.f = pullback.fst V.hom D.f' := by
  simp [overPullbackBaseChangeIso, IsPullback.isoIsPullback_inv_fst]

/-- `overPullbackBaseChangeIso_inv_app_left_fst` on global functions. -/
theorem overPullbackBaseChangeIso_inv_app_left_Γ (V : Over D.S') :
    Scheme.Γ.map (D.B.inclusion.map (pullback.fst (V.hom ≫ D.gHom) D.f)).op ≫
        Scheme.Γ.map (D.B.inclusion.map ((overPullbackBaseChangeIso D.g' D.f' D.f D.gHom
          D.isPullback).inv.app V).left).op =
      Scheme.Γ.map (D.B.inclusion.map (pullback.fst V.hom D.f')).op := by
  rw [← Functor.map_comp, ← op_comp, ← Functor.map_comp, overPullbackBaseChangeIso_inv_app_left_fst]

/-- `g_big^* f_{big, *} = f'_{big, *} (g'_big)^*` on site-presented direct images of
`𝒪`-modules. -/
def bigEtaleModulePushforwardInverseImageToposIso :
    (bigSiteRingedSiteHom (τ := .etale) D.B D.f).toRingedToposSiteHom.pushforwardTopos ⋙
        bigEtaleModuleInverseImage D.B D.gHom ≅
      bigEtaleModuleInverseImage D.B D.g' ⋙
        (bigSiteRingedSiteHom (τ := .etale) D.B D.f').toRingedToposSiteHom.pushforwardTopos :=
  let a := (bigSiteRingedSiteHom (τ := .etale) D.B D.f).toRingedToposSiteHom
  let a' := (bigSiteRingedSiteHom (τ := .etale) D.B D.f').toRingedToposSiteHom
  let r := bigEtaleRestrictionRingedToposSiteHom D.B D.gHom
  let r' := bigEtaleRestrictionRingedToposSiteHom D.B D.g'
  let e : (a'.comp r').u ≅ (r.comp a).u :=
    (overPullbackBaseChangeIso D.g' D.f' D.f D.gHom D.isPullback).symm
  letI := (a'.comp r').isContinuous
  letI := (r.comp a).isContinuous
  (a.pushforwardToposCompIso r).symm ≪≫
    SheafOfModules.pushforwardCongr₂ _ e (by
      apply ObjectProperty.hom_ext
      ext V x
      change (Scheme.Γ.map (D.B.inclusion.map (pullback.fst (V.unop.hom ≫ D.gHom) D.f)).op ≫
          Scheme.Γ.map (D.B.inclusion.map ((overPullbackBaseChangeIso D.g' D.f' D.f D.gHom
            D.isPullback).inv.app V.unop).left).op) x =
        Scheme.Γ.map (D.B.inclusion.map (pullback.fst V.unop.hom D.f')).op x
      exact congrArg (fun φ => (ConcreteCategory.hom φ) x)
        (overPullbackBaseChangeIso_inv_app_left_Γ D V.unop)) ≪≫
    r'.pushforwardToposCompIso a'

/-- `g_big^* f_{big, *} = f'_{big, *} (g'_big)^*` on direct images of `𝒪`-modules along the
morphisms of ringed topoi `f_big` and `f'_big`. -/
def bigEtaleModulePushforwardInverseImageIso :
    (bigEtaleRingedToposHom D.B D.f).pushforwardModules ⋙ bigEtaleModuleInverseImage D.B D.gHom ≅
      bigEtaleModuleInverseImage D.B D.g' ⋙ (bigEtaleRingedToposHom D.B D.f').pushforwardModules :=
  Functor.isoWhiskerRight
      (bigSiteRingedSiteHom (τ := .etale) D.B D.f).pushforwardToposIsoGeneral _ ≪≫
    bigEtaleModulePushforwardInverseImageToposIso D ≪≫
    Functor.isoWhiskerLeft _
      (bigSiteRingedSiteHom (τ := .etale) D.B D.f').pushforwardToposIsoGeneral.symm

attribute [local instance 10000] HasDerivedCategory.standard in
/-- Let `f : T ⟶ S` be a morphism of schemes, `g : S' ⟶ S` an object of `(Sch/S)_étale` and
`T' = T ×_S S'` with projections `f' : T' ⟶ S'` and `g' : T' ⟶ T`. For `K` in
`D((Sch/T)_étale, 𝒪)`, `g_big^*(Rf_{big, *}K) = Rf'_{big, *}((g'_big)^*K)` in
`D((Sch/S')_étale, 𝒪)`, naturally in `K`. -/
@[stacks 075A "part (6)"]
def bigEtaleDerivedModulePushforwardInverseImageIso :
    Stacks.Cohomology.DerivedPushforward.derivedPushforward (X := bigEtaleOverRingedTopos D.B D.T)
        (Y := bigEtaleOverRingedTopos D.B D.S) (bigEtaleRingedToposHom D.B D.f) ⋙
        (bigEtaleModuleInverseImage D.B D.gHom).mapDerivedCategory ≅
      (bigEtaleModuleInverseImage D.B D.g').mapDerivedCategory ⋙
        Stacks.Cohomology.DerivedPushforward.derivedPushforward
          (X := bigEtaleOverRingedTopos D.B D.T') (Y := bigEtaleOverRingedTopos D.B D.S')
          (bigEtaleRingedToposHom D.B D.f') :=
  RingedToposHom.derivedPushforwardExactSquareIsoOfKInjective (bigEtaleRingedToposHom D.B D.f)
    (bigEtaleRingedToposHom D.B D.f') _ _
    (fun I hI => isKInjective_bigEtaleModuleInverseImage D.B D.g' I (hI := hI))
    (bigEtaleModulePushforwardInverseImageIso D)

/-- The inverse image `i_g^*` of `𝒪`-modules along `i_g : (X_étale, 𝒪_X) ⟶ ((Sch/Y)_étale, 𝒪)`:
restriction along `V/X ↦ V/Y`, with the identity structure map. It is presented as the direct
image along the composite `π_X ∘ g_big^{-1}` of site-presented morphisms of ringed topoi, whose
underlying functor of sites is `V/X ↦ V/Y` on the nose. -/
abbrev smallEtaleModuleRestrictionAlong {X Y : B.Scheme} (g : X ⟶ Y) :
    (bigEtaleOverRingedTopos B Y).Modules ⥤ (smallEtaleRingedTopos B X).Modules :=
  ((smallEtalePiRingedSiteHom B (S := X)).toRingedToposSiteHom.comp
    (bigEtaleRestrictionRingedToposSiteHom B g)).pushforwardTopos

/-- `i_g^* = π_{X, *} ∘ g_big^*` on `𝒪`-modules. -/
def smallEtaleModuleRestrictionAlongIso {X Y : B.Scheme} (g : X ⟶ Y) :
    smallEtaleModuleRestrictionAlong B g ≅
      bigEtaleModuleInverseImage B g ⋙ (bigToSmallEtaleRingedToposHom B X).pushforwardModules :=
  (bigEtaleRestrictionRingedToposSiteHom B g).pushforwardToposCompIso
      (smallEtalePiRingedSiteHom B (S := X)).toRingedToposSiteHom ≪≫
    Functor.isoWhiskerLeft _ (smallEtalePiRingedSiteHom B (S := X)).pushforwardToposIsoGeneral.symm

/-- The inverse image `i_g^*` of `𝒪`-modules is additive. -/
instance smallEtaleModuleRestrictionAlong_additive {X Y : B.Scheme} (g : X ⟶ Y) :
    (smallEtaleModuleRestrictionAlong B g).Additive :=
  RingedToposSiteHom.pushforwardTopos_additive _

/-- The inverse image `i_g^*` of `𝒪`-modules preserves finite limits. -/
instance smallEtaleModuleRestrictionAlong_preservesFiniteLimits {X Y : B.Scheme} (g : X ⟶ Y) :
    PreservesFiniteLimits (smallEtaleModuleRestrictionAlong B g) :=
  preservesFiniteLimits_of_natIso (smallEtaleModuleRestrictionAlongIso B g).symm

/-- The inverse image `i_g^*` of `𝒪`-modules preserves finite colimits. -/
instance smallEtaleModuleRestrictionAlong_preservesFiniteColimits {X Y : B.Scheme} (g : X ⟶ Y) :
    PreservesFiniteColimits (smallEtaleModuleRestrictionAlong B g) :=
  preservesFiniteColimits_of_natIso (smallEtaleModuleRestrictionAlongIso B g).symm

attribute [local instance 10000] HasDerivedCategory.standard in
/-- In the situation of part (6), for `K` in `D((Sch/T)_étale, 𝒪)`,
`i_g^*(Rf_{big, *}K) = Rf'_{small, *}(i_{g'}^*K)` in `D(Mod(S'_étale, 𝒪_{S'}))`, naturally in `K`.
-/
@[stacks 075A "part (4)"]
def smallEtaleDerivedModulePushforwardRestrictionAlongIso :
    Stacks.Cohomology.DerivedPushforward.derivedPushforward (X := bigEtaleOverRingedTopos D.B D.T)
        (Y := bigEtaleOverRingedTopos D.B D.S) (bigEtaleRingedToposHom D.B D.f) ⋙
        (smallEtaleModuleRestrictionAlong D.B D.gHom).mapDerivedCategory ≅
      (smallEtaleModuleRestrictionAlong D.B D.g').mapDerivedCategory ⋙
        Stacks.Cohomology.DerivedPushforward.derivedPushforward
          (X := smallEtaleRingedTopos D.B D.T') (Y := smallEtaleRingedTopos D.B D.S')
          (smallEtaleRingedToposHom D.B D.f') :=
  Functor.isoWhiskerLeft _ (Dualizing.mapDerivedCategoryCompNatIso _ _ _
      (smallEtaleModuleRestrictionAlongIso D.B D.gHom).symm).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (bigEtaleDerivedModulePushforwardInverseImageIso D) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (bigSmallEtaleDerivedModulePushforwardRestrictionIso D.B D.f') ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Dualizing.mapDerivedCategoryCompNatIso _ _ _
      (smallEtaleModuleRestrictionAlongIso D.B D.g').symm) _

end ModuleBaseChange

end Modules

end AlgebraicGeometry
