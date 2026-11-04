module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.Situation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.ExactInverseImageComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowBaseChangeOfUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.DerivedPushforwardRestriction
public import StacksFrontier.Homology.Injectives.KInjective.RightDerivedCriterion
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BigEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.CohomologicalDescent

/-!
# Comparing fppf and étale cohomology: the functors `ε_X` and `a_X`

Let `B` be a big fppf site and let `(Sch/S)_étale` be the étale site on the same category of
schemes (`AlgebraicGeometry.associatedBigEtaleSite`). For an object `X` the comparison morphism
`ε_X : (Sch/X)_fppf ⟶ (Sch/X)_étale` has as direct image `ε_{X,*}`, an fppf sheaf regarded as an
étale sheaf, and as inverse image `ε_X^{-1}`, fppf sheafification. The composite
`a_X = π_X ∘ ε_X : (Sch/X)_fppf ⟶ X_étale` has inverse image `a_X^{-1} = ε_X^{-1} ∘ π_X^{-1}`.
This file sets up these functors on abelian sheaves and reads Stacks 0EZF through them, in
Situation 0EZ3 for the fppf and étale topologies (Stacks 0F0H). That gives parts (1) and (3) of
Stacks 0DDS.

## Main definitions

* `AlgebraicGeometry.fppfBigEtaleAbelianPushforward`,
  `AlgebraicGeometry.fppfBigEtaleAbelianPullback` and
  `AlgebraicGeometry.fppfBigEtaleAbelianAdjunction`: `ε_X^{-1} ⊣ ε_{X,*}` on abelian sheaves.
* `AlgebraicGeometry.fppfSmallEtaleAbelianPullback`: `a_X^{-1} = π_X^{-1} ⋙ ε_X^{-1}`.
* `AlgebraicGeometry.fppfSmallEtaleDerivedUnit`: the map `π_X^{-1}K ⟶ Rε_{X,*}(a_X^{-1}K)` on
  `D⁺(X_étale)`.
* `AlgebraicGeometry.fppfEtaleBigSmallDerivedBaseChangePlusIso`: an identification
  `π_Y^{-1} ∘ Rf_{small,*} = Rf_{big,*} ∘ π_X^{-1}` on unbounded derived categories, as in Stacks
  0DDJ (4), read on `D⁺` and for the localized étale topology.
* `AlgebraicGeometry.fppfSmallEtaleDerivedBaseChangeIsoOfUnbounded` and
  `AlgebraicGeometry.fppfSmallEtaleHigherBaseChangeIsoOfUnbounded`: from such an identification,
  `a_Y^{-1} ∘ Rf_{small,*} = Rf_{big,fppf,*} ∘ a_X^{-1}` on `D⁺(X_étale)` and in each degree, the
  shapes of Stacks 0DDS (4) and (2).
* `AlgebraicGeometry.fppfSmallEtaleDerivedPushforwardEtaleIso`:
  `Rε_{Y,*} Rf_{big,fppf,*} a_X^{-1} = Rf_{big,étale,*} π_X^{-1}` on `D⁺(X_étale)`, the first two
  steps of the proof of Stacks 0DDS (5).

## Main results

* `AlgebraicGeometry.isIso_fppfBigEtaleAbelianAdjunction_unit_app_projectionPullback`: the
  degree zero half of Stacks 0DDS (1), `π_X^{-1}F = ε_{X,*}a_X^{-1}F`, by the unit of
  `ε_X^{-1} ⊣ ε_{X,*}`.
* `AlgebraicGeometry.isZero_fppfBigEtaleAbelianPushforward_rightDerived_of_finite`: the vanishing
  `R^iε_{X,*}(a_X^{-1}F) = 0` for `i > 0` of Stacks 0DDS (1).
* `AlgebraicGeometry.isIso_fppfSmallEtaleDerivedUnit_of_finite`: Stacks 0DDS (3).

## Implementation notes

Situation 0EZ3 for the fppf and étale topologies is
`AlgebraicGeometry.fppfEtaleCohomologyComparisonOfFinite`. It is built from the two facts about
the direct image along a finite morphism that its property (0EZ7) needs, which are the inputs of
the proof of Stacks 0DDJ (4). The results of this file that use the situation take those two
facts as the arguments `hex` and `hbc`.

The direct image `f_{big,*}` on the big étale sites appears in two spellings, for the localized
topologies of Situation 0EZ3 and for the slice topologies `AlgebraicGeometry.BigEtaleOver.topology`
in which Stacks 0DDJ is stated. `AlgebraicGeometry.fppfEtaleBigPushforwardTransportIso` identifies
them.

The derived categories are those of `HasDerivedCategory.standard`, the model in which Stacks
0EZF, `Stacks.ComparingTopologies.isIso_derivedComparisonUnit_app`, is stated.

## References

* [Stacks Project, Tag 0DDS](https://stacks.math.columbia.edu/tag/0DDS)
* [Stacks Project, Tag 0F0H](https://stacks.math.columbia.edu/tag/0F0H)
* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.ComparingTopologies

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (X : B.Schemes)

/-- The direct image `ε_{X,*}` of the comparison morphism `ε_X : (Sch/X)_fppf ⟶ (Sch/X)_étale` on
abelian sheaves: an fppf sheaf regarded as an étale sheaf. -/
abbrev fppfBigEtaleAbelianPushforward :
    Sheaf (B.topology.over X) AddCommGrpCat.{u + 1} ⥤
      Sheaf ((associatedBigEtaleSite B).topology.over X) AddCommGrpCat.{u + 1} :=
  abelianComparisonPushforward B.precoverage (associatedBigEtaleSite B).precoverage
    (associatedEtalePrecoverage_le_fppfPrecoverage B) X

/-- The inverse image `ε_X^{-1}` of the comparison morphism on abelian sheaves: fppf
sheafification of an étale sheaf. -/
abbrev fppfBigEtaleAbelianPullback :
    Sheaf ((associatedBigEtaleSite B).topology.over X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (B.topology.over X) AddCommGrpCat.{u + 1} :=
  abelianComparisonPullback B.precoverage (associatedBigEtaleSite B).precoverage X

/-- The adjunction `ε_X^{-1} ⊣ ε_{X,*}` on abelian sheaves. -/
abbrev fppfBigEtaleAbelianAdjunction :
    fppfBigEtaleAbelianPullback B X ⊣ fppfBigEtaleAbelianPushforward B X :=
  abelianComparisonAdjunction B.precoverage (associatedBigEtaleSite B).precoverage
    (associatedEtalePrecoverage_le_fppfPrecoverage B) X

/-- The inverse image `a_X^{-1} = ε_X^{-1} ∘ π_X^{-1}` of abelian sheaves along the morphism of
topoi `a_X : Sh((Sch/X)_fppf) ⟶ Sh(X_étale)`. -/
abbrev fppfSmallEtaleAbelianPullback :
    Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1} ⥤
      Sheaf (B.topology.over X) AddCommGrpCat.{u + 1} :=
  fppfEtaleProjectionPullback B X ⋙ fppfBigEtaleAbelianPullback B X

/-- The inverse image `ε_X^{-1}` of abelian sheaves preserves finite colimits. -/
instance : PreservesFiniteColimits (fppfBigEtaleAbelianPullback B X) :=
  have := (fppfBigEtaleAbelianAdjunction B X).leftAdjoint_preservesColimits
  inferInstance

/-- The inverse image `a_X^{-1}` of abelian sheaves preserves finite limits. -/
instance : PreservesFiniteLimits (fppfSmallEtaleAbelianPullback B X) :=
  comp_preservesFiniteLimits _ _

/-- The inverse image `a_X^{-1}` of abelian sheaves preserves finite colimits. -/
instance : PreservesFiniteColimits (fppfSmallEtaleAbelianPullback B X) :=
  comp_preservesFiniteColimits _ _

/-- **The degree zero half of Stacks 0DDS (1).** For an abelian sheaf `F` on `X_étale` the unit
`π_X^{-1}F ⟶ ε_{X,*}ε_X^{-1}π_X^{-1}F = ε_{X,*}a_X^{-1}F` is an isomorphism, because `π_X^{-1}F`
is already an fppf sheaf (Stacks 0DDL). -/
theorem isIso_fppfBigEtaleAbelianAdjunction_unit_app_projectionPullback
    (F : Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1}) :
    IsIso ((fppfBigEtaleAbelianAdjunction B X).unit.app
      ((fppfEtaleProjectionPullback B X).obj F)) :=
  (fppfBigEtaleAbelianAdjunction B X).isIso_unit_app_of_iso
    (show (fppfEtaleProjectionPullback B X).obj F ≅ (fppfBigEtaleAbelianPushforward B X).obj
      ⟨((fppfEtaleProjectionPullback B X).obj F).obj,
        fppfEtaleWeakSerre_isSheaf_fppf _ ((fppfEtaleProjectionPullback B X).obj_mem_essImage F)⟩
      from Iso.refl _)

/-- The map `π_X^{-1}K ⟶ Rε_{X,*}(a_X^{-1}K)` of Stacks 0DDS (3), for `K` in `D⁺(X_étale)`. It is
the unit of the derived adjunction `ε_X^{-1} ⊣ Rε_{X,*}` at `π_X^{-1}K`, followed by `Rε_{X,*}` of
the identification `ε_X^{-1}(π_X^{-1}K) ≅ a_X^{-1}K` of the derived actions of exact functors. -/
def fppfSmallEtaleDerivedUnit :
    (fppfEtaleProjectionPullback B X).mapDerivedCategoryPlus ⟶
      (fppfSmallEtaleAbelianPullback B X).mapDerivedCategoryPlus ⋙
        (fppfBigEtaleAbelianPushforward B X).rightDerivedFunctorPlus :=
  Functor.whiskerLeft (fppfEtaleProjectionPullback B X).mapDerivedCategoryPlus
      (derivedPlusAdjunction (fppfBigEtaleAbelianAdjunction B X)).unit ≫
    Functor.whiskerRight (Stacks.DerivedFunctor.mapDerivedCategoryPlusCompIso
        (fppfEtaleProjectionPullback B X) (fppfBigEtaleAbelianPullback B X)).hom
      (fppfBigEtaleAbelianPushforward B X).rightDerivedFunctorPlus

/-- The direct image `f_{big,*}` of abelian sheaves on the big étale sites, in its two spellings:
as the pushforward along the cocontinuous `Over.map f` for the localized étale topologies of
Situation 0EZ3, and as the pushforward along the continuous `Over.pullback f` for the slice
topologies `AlgebraicGeometry.BigEtaleOver.topology`. The two topologies agree, through
`CategoryTheory.sheafEquivOfTopologyEq`, and the two pushforwards agree by the adjunction
`Over.map f ⊣ Over.pullback f`; this is `AlgebraicGeometry.fppfEtaleOverMapPushforwardIso` with
the transport moved to the source. -/
def fppfEtaleBigPushforwardTransportIso {X Y : B.Schemes} (f : X ⟶ Y) :
    (sheafEquivOfTopologyEq (bigEtaleOver_topology_eq (associatedBigEtaleSite B) X.1 X.2)
        AddCommGrpCat.{u + 1}).functor ⋙
      (Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        ((associatedBigEtaleSite B).topology.over X) ((associatedBigEtaleSite B).topology.over Y) ≅
    (Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (BigEtaleOver.topology (associatedBigEtaleSite B) Y.1 Y.2)
        (BigEtaleOver.topology (associatedBigEtaleSite B) X.1 X.2) ⋙
      (sheafEquivOfTopologyEq (bigEtaleOver_topology_eq (associatedBigEtaleSite B) Y.1 Y.2)
        AddCommGrpCat.{u + 1}).functor :=
  Functor.isoWhiskerLeft _ (fppfEtaleOverMapPushforwardIso f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sheafEquivOfTopologyEq
      (bigEtaleOver_topology_eq (associatedBigEtaleSite B) X.1 X.2)
        AddCommGrpCat.{u + 1}).unitIso.symm
      _ ≪≫
    Functor.leftUnitor _

section Situation

/-! ### Consequences of Situation 0EZ3 for the fppf and étale topologies

The hypotheses `hex` and `hbc` are the two facts about the direct image `f_{big,*}` along a
finite morphism `f` of the big étale site from which
`AlgebraicGeometry.fppfEtaleCohomologyComparisonOfFinite` builds Situation 0EZ3. `hex` is
exactness and `hbc` is `f_{big,*}π_X^{-1}F ∈ 𝒜'_Y`; both are in the proof of Stacks 0DDJ (4). -/

variable {B}
  (hex : ∀ ⦃X Y : B.Schemes⦄ (f : X ⟶ Y), fppfEtaleFinite B f →
    PreservesFiniteColimits ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      ((associatedBigEtaleSite B).topology.over X) ((associatedBigEtaleSite B).topology.over Y)))
  (hbc : ∀ ⦃X Y : B.Schemes⦄ (f : X ⟶ Y), fppfEtaleFinite B f → ∀ A, fppfEtaleWeakSerre B Y
    (((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      ((associatedBigEtaleSite B).topology.over X)
      ((associatedBigEtaleSite B).topology.over Y)).obj ((fppfEtaleProjectionPullback B X).obj A)))

include hex hbc in
/-- **The higher direct images `R^iε_{X,*}(a_X^{-1}F)` vanish for `i > 0`**, the second half of
Stacks 0DDS (1), given the two inputs of Situation 0EZ3 for the fppf and étale topologies. It is
the vanishing condition `(V_n)` of Stacks 0EZF at `a_X^{-1}F = ε_X^{-1}π_X^{-1}F`. -/
theorem isZero_fppfBigEtaleAbelianPushforward_rightDerived_of_finite
    (F : Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1})
    (i : ℕ) (hi : 0 < i) :
    IsZero (((fppfBigEtaleAbelianPushforward B X).rightDerived i).obj
      ((fppfSmallEtaleAbelianPullback B X).obj F)) :=
  CohomologyComparison.isZero_rightDerived_abelianComparisonPullback
    (fppfEtaleCohomologyComparisonOfFinite B hex hbc) X ((fppfEtaleProjectionPullback B X).obj F)
    ((fppfEtaleProjectionPullback B X).obj_mem_essImage F) i hi

include hex hbc in
/-- **The map `π_X^{-1}K ⟶ Rε_{X,*}(a_X^{-1}K)` is an isomorphism** for `K` in `D⁺(X_étale)`,
Stacks 0DDS (3), given the two inputs of Situation 0EZ3 for the fppf and étale topologies. It is
Stacks 0EZF (1) at `π_X^{-1}K`, which lies in `D⁺_{𝒜'_X}`. -/
theorem isIso_fppfSmallEtaleDerivedUnit_of_finite : IsIso (fppfSmallEtaleDerivedUnit B X) := by
  let S := fppfEtaleCohomologyComparisonOfFinite B hex hbc
  let P : Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1} ⥤
      Stacks.Cohomology.Localization.AbelianSheaves S.coarseCoverage.toGrothendieck X :=
    fppfEtaleProjectionPullback B X
  have : P.Additive := fppfEtaleProjectionPullback_additive B X
  have : PreservesFiniteLimits P :=
    inferInstanceAs (PreservesFiniteLimits (fppfEtaleProjectionPullback B X))
  have : PreservesFiniteColimits P :=
    inferInstanceAs (PreservesFiniteColimits (fppfEtaleProjectionPullback B X))
  have h := CohomologyComparison.isIso_derivedComparisonUnitAlong S X P
    (fun F ↦ (fppfEtaleProjectionPullback B X).obj_mem_essImage F)
  have hu : (derivedPlusAdjunction (fppfBigEtaleAbelianAdjunction B X)).unit =
      derivedComparisonUnit S X :=
    derivedComparisonAdjunction_unit S X
  rwa [fppfSmallEtaleDerivedUnit, hu]

section BaseChange

/-- The inverse image `π_X^{-1}` from the small étale site to the slice topology
`AlgebraicGeometry.BigEtaleOver.topology` is exact (Stacks 0DDI). -/
local instance projectionSheafPullback_preservesFiniteLimits (X : B.Schemes) :
    PreservesFiniteLimits ((SmallEtale.inclusion (associatedBigEtaleSite B) X.1 X.2).sheafPullback
      AddCommGrpCat.{u + 1} (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2)
      (BigEtaleOver.topology (associatedBigEtaleSite B) X.1 X.2)) :=
  ((exactFunctor_iff _).mp (projectionPullback_exact.{u, 0} (associatedBigEtaleSite B) X.1 X.2)).1

/-- The inverse image `π_X^{-1}` from the small étale site to the slice topology
`AlgebraicGeometry.BigEtaleOver.topology` preserves finite colimits. -/
local instance projectionSheafPullback_preservesFiniteColimits (X : B.Schemes) :
    PreservesFiniteColimits ((SmallEtale.inclusion (associatedBigEtaleSite B) X.1 X.2).sheafPullback
      AddCommGrpCat.{u + 1} (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2)
      (BigEtaleOver.topology (associatedBigEtaleSite B) X.1 X.2)) :=
  ((exactFunctor_iff _).mp (projectionPullback_exact.{u, 0} (associatedBigEtaleSite B) X.1 X.2)).2

/-- The inverse image `π_X^{-1}` from the small étale site to the slice topology
`AlgebraicGeometry.BigEtaleOver.topology` is additive. -/
local instance projectionSheafPullback_additive (X : B.Schemes) :
    ((SmallEtale.inclusion (associatedBigEtaleSite B) X.1 X.2).sheafPullback
      AddCommGrpCat.{u + 1} (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2)
      (BigEtaleOver.topology (associatedBigEtaleSite B) X.1 X.2)).Additive :=
  Functor.additive_of_preserves_binary_products _

variable {X Y : B.Schemes} (f : X ⟶ Y)
  (RfSmall : DerivedCategory
      (Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1}) ⥤
    DerivedCategory
      (Sheaf (SmallEtale.topology (associatedBigEtaleSite B) Y.1 Y.2) AddCommGrpCat.{u + 1}))
  (αSmall :
      ((associatedBigEtaleSite B).smallPushforward f AddCommGrpCat.{u + 1}).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RfSmall)
  [RfSmall.IsRightDerivedFunctor αSmall (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
  (RfBig : DerivedCategory
      (Sheaf (BigEtaleOver.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1}) ⥤
    DerivedCategory
      (Sheaf (BigEtaleOver.topology (associatedBigEtaleSite B) Y.1 Y.2) AddCommGrpCat.{u + 1}))
  (αBig : ((Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (BigEtaleOver.topology (associatedBigEtaleSite B) Y.1 Y.2)
      (BigEtaleOver.topology (associatedBigEtaleSite B) X.1 X.2)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RfBig)
  [RfBig.IsRightDerivedFunctor αBig (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]

/-- **The base change identification of Stacks 0DDJ (4), restricted to `D⁺` and to Situation
0EZ3.** Let `f : X ⟶ Y` be a morphism of the big fppf site, and let `Rf_{small,*}` and
`Rf_{big,*}` be right derived functors, on unbounded derived categories, of the direct images of
abelian sheaves along `f` on the small and the big étale sites. An identification
`π_Y^{-1} ∘ Rf_{small,*} = Rf_{big,*} ∘ π_X^{-1}` on `D(X_étale)` gives the same identification
on `D⁺(X_étale)`, with `f_{big,*}` and `π^{-1}` written for the localized étale topology of
Situation 0EZ3 and the right derived functors built from injective resolutions. For `f` finite
the identification on `D(X_étale)` is Stacks 0DDJ (4). -/
def fppfEtaleBigSmallDerivedBaseChangePlusIso
    (e : RfSmall ⋙ ((SmallEtale.inclusion (associatedBigEtaleSite B) Y.1 Y.2).sheafPullback
        AddCommGrpCat.{u + 1} (SmallEtale.topology (associatedBigEtaleSite B) Y.1 Y.2)
        (BigEtaleOver.topology (associatedBigEtaleSite B) Y.1 Y.2)).mapDerivedCategory ≅
      ((SmallEtale.inclusion (associatedBigEtaleSite B) X.1 X.2).sheafPullback
        AddCommGrpCat.{u + 1} (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2)
        (BigEtaleOver.topology (associatedBigEtaleSite B) X.1 X.2)).mapDerivedCategory ⋙ RfBig) :
    ((associatedBigEtaleSite B).smallPushforward f AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus ⋙
        (fppfEtaleProjectionPullback B Y).mapDerivedCategoryPlus ≅
      (fppfEtaleProjectionPullback B X).mapDerivedCategoryPlus ⋙
        ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          ((associatedBigEtaleSite B).topology.over X)
          ((associatedBigEtaleSite B).topology.over Y)).rightDerivedFunctorPlus := by
  haveI := projectionSheafPullback_additive X
  haveI := projectionSheafPullback_additive Y
  haveI := projectionSheafPullback_preservesFiniteLimits X
  haveI := projectionSheafPullback_preservesFiniteLimits Y
  haveI := projectionSheafPullback_preservesFiniteColimits X
  haveI := projectionSheafPullback_preservesFiniteColimits Y
  haveI : (sheafEquivOfTopologyEq (bigEtaleOver_topology_eq (associatedBigEtaleSite B) X.1 X.2)
      AddCommGrpCat.{u + 1}).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  haveI : (sheafEquivOfTopologyEq (bigEtaleOver_topology_eq (associatedBigEtaleSite B) Y.1 Y.2)
      AddCommGrpCat.{u + 1}).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  haveI : (sheafEquivOfTopologyEq (bigEtaleOver_topology_eq (associatedBigEtaleSite B) X.1 X.2)
      AddCommGrpCat.{u + 1}).functor.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (sheafEquivOfTopologyEq (bigEtaleOver_topology_eq (associatedBigEtaleSite B) X.1 X.2)
        AddCommGrpCat.{u + 1}).symm.toAdjunction
  haveI : (((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        ((associatedBigEtaleSite B).topology.over X)
        ((associatedBigEtaleSite B).topology.over Y)).mapHomotopyCategoryPlus ⋙
          DerivedCategory.Plus.Qh).HasPointwiseRightDerivedFunctor
        (HomotopyCategory.Plus.quasiIso _) :=
    HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso _
  have hA : ∀ K : CochainComplex (Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2)
      AddCommGrpCat.{u + 1}) ℤ, ∃ (I : CochainComplex _ ℤ) (q : K ⟶ I),
        I.IsKInjective ∧ QuasiIso q := fun K ↦
    haveI := smallEtale_abelianSheaves_isGrothendieckAbelian (associatedBigEtaleSite B) X
    Stacks.Injectives.exists_kInjective_resolution_of_grothendieck K
  have hS : ∀ K : CochainComplex (Sheaf (BigEtaleOver.topology (associatedBigEtaleSite B) X.1 X.2)
      AddCommGrpCat.{u + 1}) ℤ, ∃ (I : CochainComplex _ ℤ) (q : K ⟶ I),
        I.IsKInjective ∧ QuasiIso q := fun K ↦
    haveI := bigEtaleOver_abelianSheaves_isGrothendieckAbelian (associatedBigEtaleSite B) X
    Stacks.Injectives.exists_kInjective_resolution_of_grothendieck K
  have hacyclic : ∀ I, Injective I →
      ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        ((associatedBigEtaleSite B).topology.over X)
        ((associatedBigEtaleSite B).topology.over Y)).rightAcyclic
        ((sheafEquivOfTopologyEq (bigEtaleOver_topology_eq (associatedBigEtaleSite B) X.1 X.2)
          AddCommGrpCat.{u + 1}).functor.obj I) := fun I _ ↦
    haveI : Injective ((sheafEquivOfTopologyEq
        (bigEtaleOver_topology_eq (associatedBigEtaleSite B) X.1 X.2)
          AddCommGrpCat.{u + 1}).functor.obj I) :=
      Injective.injective_of_adjoint
        (sheafEquivOfTopologyEq (bigEtaleOver_topology_eq (associatedBigEtaleSite B) X.1 X.2)
          AddCommGrpCat.{u + 1}).symm.toAdjunction I
    Functor.rightAcyclic_of_injective _ _
  exact Stacks.DerivedFunctor.boundedBelowBaseChangeIsoOfUnboundedTransport
    ((associatedBigEtaleSite B).smallPushforward f AddCommGrpCat.{u + 1})
    ((Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (BigEtaleOver.topology (associatedBigEtaleSite B) Y.1 Y.2)
      (BigEtaleOver.topology (associatedBigEtaleSite B) X.1 X.2))
    ((SmallEtale.inclusion (associatedBigEtaleSite B) X.1 X.2).sheafPullback
      AddCommGrpCat.{u + 1} (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2)
      (BigEtaleOver.topology (associatedBigEtaleSite B) X.1 X.2))
    ((SmallEtale.inclusion (associatedBigEtaleSite B) Y.1 Y.2).sheafPullback
      AddCommGrpCat.{u + 1} (SmallEtale.topology (associatedBigEtaleSite B) Y.1 Y.2)
      (BigEtaleOver.topology (associatedBigEtaleSite B) Y.1 Y.2))
    RfSmall αSmall RfBig αBig
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      ((associatedBigEtaleSite B).topology.over X) ((associatedBigEtaleSite B).topology.over Y))
    (sheafEquivOfTopologyEq (bigEtaleOver_topology_eq (associatedBigEtaleSite B) X.1 X.2)
      AddCommGrpCat.{u + 1}).functor
    (sheafEquivOfTopologyEq (bigEtaleOver_topology_eq (associatedBigEtaleSite B) Y.1 Y.2)
      AddCommGrpCat.{u + 1}).functor
    hA hS e
    (fppfEtaleBigPushforwardTransportIso B f)
    hacyclic

include hex hbc in
/-- **Stacks 0DDS (4), from Stacks 0DDJ (4).** In the situation of
`fppfEtaleBigSmallDerivedBaseChangePlusIso`, and given the two inputs of Situation 0EZ3 for the
fppf and étale topologies, an identification `π_Y^{-1} ∘ Rf_{small,*} = Rf_{big,*} ∘ π_X^{-1}` on
`D(X_étale)` gives

`a_Y^{-1} ∘ Rf_{small,*} = Rf_{big,fppf,*} ∘ a_X^{-1}`

on `D⁺(X_étale)`. It is base change along the change of topology, Stacks 0EZF (2), at
`π_X^{-1}K`, which lies in `D⁺_{𝒜'_X}` (`CohomologyComparison.derivedBaseChangeAlongIso`). -/
def fppfSmallEtaleDerivedBaseChangeIsoOfUnbounded
    (e : RfSmall ⋙ ((SmallEtale.inclusion (associatedBigEtaleSite B) Y.1 Y.2).sheafPullback
        AddCommGrpCat.{u + 1} (SmallEtale.topology (associatedBigEtaleSite B) Y.1 Y.2)
        (BigEtaleOver.topology (associatedBigEtaleSite B) Y.1 Y.2)).mapDerivedCategory ≅
      ((SmallEtale.inclusion (associatedBigEtaleSite B) X.1 X.2).sheafPullback
        AddCommGrpCat.{u + 1} (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2)
        (BigEtaleOver.topology (associatedBigEtaleSite B) X.1 X.2)).mapDerivedCategory ⋙ RfBig) :
    ((associatedBigEtaleSite B).smallPushforward f AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus ⋙
        (fppfSmallEtaleAbelianPullback B Y).mapDerivedCategoryPlus ≅
      (fppfSmallEtaleAbelianPullback B X).mapDerivedCategoryPlus ⋙
        ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          (B.topology.over X) (B.topology.over Y)).rightDerivedFunctorPlus := by
  let S := fppfEtaleCohomologyComparisonOfFinite B hex hbc
  let P : Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1} ⥤
      Stacks.Cohomology.Localization.AbelianSheaves S.coarseCoverage.toGrothendieck X :=
    fppfEtaleProjectionPullback B X
  let P' : Sheaf (SmallEtale.topology (associatedBigEtaleSite B) Y.1 Y.2) AddCommGrpCat.{u + 1} ⥤
      Stacks.Cohomology.Localization.AbelianSheaves S.coarseCoverage.toGrothendieck Y :=
    fppfEtaleProjectionPullback B Y
  haveI : P.Additive := fppfEtaleProjectionPullback_additive B X
  haveI : PreservesFiniteLimits P :=
    inferInstanceAs (PreservesFiniteLimits (fppfEtaleProjectionPullback B X))
  haveI : PreservesFiniteColimits P :=
    inferInstanceAs (PreservesFiniteColimits (fppfEtaleProjectionPullback B X))
  haveI : P'.Additive := fppfEtaleProjectionPullback_additive B Y
  haveI : PreservesFiniteLimits P' :=
    inferInstanceAs (PreservesFiniteLimits (fppfEtaleProjectionPullback B Y))
  haveI : PreservesFiniteColimits P' :=
    inferInstanceAs (PreservesFiniteColimits (fppfEtaleProjectionPullback B Y))
  exact CohomologyComparison.derivedBaseChangeAlongIso S f P P'
    ((associatedBigEtaleSite B).smallPushforward f AddCommGrpCat.{u + 1})
    (fun F ↦ (fppfEtaleProjectionPullback B X).obj_mem_essImage F)
    (fppfEtaleBigSmallDerivedBaseChangePlusIso f RfSmall αSmall RfBig αBig e)

include hex hbc in
/-- **Stacks 0DDS (2), from Stacks 0DDJ (4).** In the situation of
`fppfSmallEtaleDerivedBaseChangeIsoOfUnbounded`, for every `i`,

`a_Y^{-1}(R^i f_{small,*} F) = R^i f_{big,fppf,*}(a_X^{-1} F)`,

naturally in the abelian sheaf `F` on `X_étale`: the degree `i` cohomology of the identification
of Stacks 0DDS (4) at `F` placed in degree zero
(`CohomologyComparison.higherBaseChangeAlongIso`). -/
def fppfSmallEtaleHigherBaseChangeIsoOfUnbounded
    (e : RfSmall ⋙ ((SmallEtale.inclusion (associatedBigEtaleSite B) Y.1 Y.2).sheafPullback
        AddCommGrpCat.{u + 1} (SmallEtale.topology (associatedBigEtaleSite B) Y.1 Y.2)
        (BigEtaleOver.topology (associatedBigEtaleSite B) Y.1 Y.2)).mapDerivedCategory ≅
      ((SmallEtale.inclusion (associatedBigEtaleSite B) X.1 X.2).sheafPullback
        AddCommGrpCat.{u + 1} (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2)
        (BigEtaleOver.topology (associatedBigEtaleSite B) X.1 X.2)).mapDerivedCategory ⋙ RfBig)
    (i : ℕ) :
    ((associatedBigEtaleSite B).smallPushforward f AddCommGrpCat.{u + 1}).rightDerived i ⋙
        fppfSmallEtaleAbelianPullback B Y ≅
      fppfSmallEtaleAbelianPullback B X ⋙
        ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          (B.topology.over X) (B.topology.over Y)).rightDerived i := by
  let S := fppfEtaleCohomologyComparisonOfFinite B hex hbc
  let P : Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1} ⥤
      Stacks.Cohomology.Localization.AbelianSheaves S.coarseCoverage.toGrothendieck X :=
    fppfEtaleProjectionPullback B X
  let P' : Sheaf (SmallEtale.topology (associatedBigEtaleSite B) Y.1 Y.2) AddCommGrpCat.{u + 1} ⥤
      Stacks.Cohomology.Localization.AbelianSheaves S.coarseCoverage.toGrothendieck Y :=
    fppfEtaleProjectionPullback B Y
  haveI : P.Additive := fppfEtaleProjectionPullback_additive B X
  haveI : PreservesFiniteLimits P :=
    inferInstanceAs (PreservesFiniteLimits (fppfEtaleProjectionPullback B X))
  haveI : PreservesFiniteColimits P :=
    inferInstanceAs (PreservesFiniteColimits (fppfEtaleProjectionPullback B X))
  haveI : P'.Additive := fppfEtaleProjectionPullback_additive B Y
  haveI : PreservesFiniteLimits P' :=
    inferInstanceAs (PreservesFiniteLimits (fppfEtaleProjectionPullback B Y))
  haveI : PreservesFiniteColimits P' :=
    inferInstanceAs (PreservesFiniteColimits (fppfEtaleProjectionPullback B Y))
  exact CohomologyComparison.higherBaseChangeAlongIso S f P P'
    ((associatedBigEtaleSite B).smallPushforward f AddCommGrpCat.{u + 1})
    (fun F ↦ (fppfEtaleProjectionPullback B X).obj_mem_essImage F)
    (fppfEtaleBigSmallDerivedBaseChangePlusIso f RfSmall αSmall RfBig αBig e) i

include hex hbc in
/-- **The first two steps of the proof of Stacks 0DDS (5).** For a morphism `f : X ⟶ Y` of the
big fppf site and `K` in `D⁺(X_étale)`,

`Rε_{Y,*} Rf_{big,fppf,*} a_X^{-1} K = Rf_{big,étale,*} Rε_{X,*} a_X^{-1} K`
`= Rf_{big,étale,*} π_X^{-1} K`,

given the two inputs of Situation 0EZ3 for the fppf and étale topologies. The first equality is
the derived square of topoi (`CohomologyComparison.derivedPlusComparisonSquareIso`), the second
is Stacks 0DDS (3). -/
def fppfSmallEtaleDerivedPushforwardEtaleIso :
    (fppfSmallEtaleAbelianPullback B X).mapDerivedCategoryPlus ⋙
        ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          (B.topology.over X) (B.topology.over Y)).rightDerivedFunctorPlus ⋙
        (fppfBigEtaleAbelianPushforward B Y).rightDerivedFunctorPlus ≅
      (fppfEtaleProjectionPullback B X).mapDerivedCategoryPlus ⋙
        ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          ((associatedBigEtaleSite B).topology.over X)
          ((associatedBigEtaleSite B).topology.over Y)).rightDerivedFunctorPlus :=
  haveI := isIso_fppfSmallEtaleDerivedUnit_of_finite X hex hbc
  Functor.isoWhiskerLeft (fppfSmallEtaleAbelianPullback B X).mapDerivedCategoryPlus
      (CohomologyComparison.derivedPlusComparisonSquareIso
        (fppfEtaleCohomologyComparisonOfFinite B hex hbc) f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (fppfSmallEtaleDerivedUnit B X)).symm _

end BaseChange

end Situation

end AlgebraicGeometry
