module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.UnderlyingAbelianLocalCohomologyInvertible
import StacksCore.Tactic.StacksAttribute

/-!
# The local cohomology sheaves and the underlying abelian sheaf, degreewise

Let `Z` be a closed subset of a ringed space `X`. The local cohomology sheaves `ℋ ⁿ_Z` are
defined twice in this library: on sheaves of `𝒪_X`-modules, as
`Stacks.Cohomology.SupportedComplexes.localCohomologySheafFunctor`, and on abelian sheaves, as
`ClosedImmersionSheaves.localCohomologySheafFunctor`. Both are Mathlib's `ℕ`-indexed
`CategoryTheory.Functor.rightDerived` of the corresponding supported-sections functor. This file
proves that the two agree:

`ℋ ⁿ_Z(ℱ)_ab ≅ ℋ ⁿ_Z(ℱ_ab)`,

naturally in the `𝒪_X`-module `ℱ` and in every degree `n`.

This is the form in which Stacks 0G74 part (2) gets used. The statement proved there,
`isIso_localCohomologySheafForgetComparison_of_isRightDerivedFunctor` of the namespace
`Stacks.Cohomology.SupportedComplexes`,
is about total right derived functors on the unbounded derived category; a consumer which has a
functor `ℋ ⁿ_Z` of modules and wants to apply it to a morphism that is only additive needs the
comparison between the two `ℕ`-indexed functors instead. Supplying it is the whole content of
this file: no new mathematics enters, only the passage between the two indexings.

## Main results

* `Stacks.Cohomology.SupportedComplexes.localCohomologySheafFunctorForgetIso`: the comparison
  `ℋ ⁿ_Z(ℱ)_ab ≅ ℋ ⁿ_Z(ℱ_ab)` in every degree.

## Implementation notes

The two right derived functors on the unbounded derived category are quantified over, with their
derivation units, exactly as in `UnderlyingAbelianLocalCohomologyComparison.lean` and
`UnderlyingAbelianLocalCohomologyInvertible.lean`; the resulting statement is stronger than one
for a fixed choice, and
`Stacks.Cohomology.SupportedComplexes.exists_rightDerivedFunctor_supportedSectionsOnClosed`
records that the family is not empty. The conclusion itself mentions neither, both sides being
the choice-free `CategoryTheory.Functor.rightDerived`.

The isomorphism is a composite of four steps and nothing else:

* the bridge `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` at `H_Z` on
  modules, which identifies `Rⁿ H_Z` with `Hⁿ(RH_Z(ℱ[0]))`; the hypothesis that K-injective
  resolutions exist is `Stacks.Cohomology.Localization.enoughKInjectives`, both categories of
  sheaves of modules being Grothendieck abelian;
* exactness of forgetting the module structure, which lets the cohomology functors be moved
  across it by `CategoryTheory.Functor.mapDerivedCategoryHomologyIso` and the degree-`0`
  single functors by Mathlib's `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`;
* invertibility of the canonical comparison of Stacks 0G74 part (2); and
* the same bridge at `H_Z` on abelian sheaves.

The first and the last step are what makes this more than a restatement of 0G74 (2): that lemma
compares total derived functors, whereas `ℋ ⁿ_Z` is in both definitions the classical derived
functor computed from an injective resolution, and the two are only identified through the
chosen-resolution argument of `StacksFrontier/Algebra/Homology/DerivedCategory/DerivedFunctorSingleRightDerived.lean`.

In degree zero this specialises to
`Stacks.Cohomology.SupportedComplexes.localCohomologySheafFunctorZeroForgetIso`, which is proved
directly from the underived comparison of supported sections and needs none of the above; the
two are not identified here, no consumer needing it.

## References

* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Remark 17.13.5 (Tag 0G6N)](https://stacks.math.columbia.edu/tag/0G6N)
* [Stacks Project, Tag 0EZA](https://stacks.math.columbia.edu/tag/0EZA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.OpenSubspace
open Stacks.Cohomology.Localization (enoughKInjectives)
open Stacks.Cohomology.UnderlyingAbelianSheaf
open Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.Cohomology.SupportedComplexes

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)
  (RHab : DerivedCategory (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) ⥤
    DerivedCategory (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u}))
  (aHab : (abelianSupportedSectionsOnClosed X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RHab)
  [RHab.IsRightDerivedFunctor aHab
    (HomotopyCategory.quasiIso
      (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (ComplexShape.up ℤ))]
  (RH : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X Z))))
  (aH : (supportedSectionsOnClosedFunctor X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RH)
  [RH.IsRightDerivedFunctor aH
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ))]

/-- **Stacks 0G74, part (2), on cohomology sheaves in every degree.** Let `Z` be a closed subset
of a ringed space `X` and let `ℱ` be a sheaf of `𝒪_X`-modules with underlying abelian sheaf
`ℱ_ab`. For every `n : ℕ` the degree-`n` local cohomology sheaf `ℋ ⁿ_Z(ℱ)`, an `𝒪_X|_Z`-module
on `Z`, has underlying abelian sheaf the degree-`n` local cohomology sheaf `ℋ ⁿ_Z(ℱ_ab)` of the
abelian sheaf `ℱ_ab`, naturally in `ℱ`.

Both sides are Mathlib's `ℕ`-indexed `CategoryTheory.Functor.rightDerived`, of supported
sections of `𝒪_X`-modules on the left and of abelian sheaves on the right. This is the statement
a consumer needs in order to let `ℋ ⁿ_Z` act on a morphism of sheaves which is additive but not
`𝒪_X`-linear — a de Rham differential, say: the morphism has no image under the module-level
functor at all, but its underlying morphism of abelian sheaves has one under the abelian functor,
and this isomorphism transports the result back.

The proof passes from each `ℕ`-indexed derived functor to the degree-`n` cohomology of a total
right derived functor on the unbounded derived category, where Stacks 0G74 part (2) applies, and
back again; see the implementation notes. -/
@[stacks 0G74 "part (2) degreewise: ℋ ⁿ_Z(ℱ)_ab ≅ ℋ ⁿ_Z(ℱ_ab)"]
def localCohomologySheafFunctorForgetIso (n : ℕ) :
    localCohomologySheafFunctor X Z hZ n ⋙
        _root_.SheafOfModules.toSheaf (structureSheafRing (closedSubsetRingedSpace X Z)) ≅
      _root_.SheafOfModules.toSheaf (structureSheafRing X) ⋙
        ClosedImmersionSheaves.localCohomologySheafFunctor Z hZ n :=
  Functor.isoWhiskerRight
      (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
        (supportedSectionsOnClosedFunctor X Z hZ) RH aH
        Stacks.Cohomology.Localization.enoughKInjectives n).symm
      (_root_.SheafOfModules.toSheaf (structureSheafRing (closedSubsetRingedSpace X Z))) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.singleFunctor _ 0)
      (Functor.isoWhiskerLeft RH
        (Functor.mapDerivedCategoryHomologyIso
          (_root_.SheafOfModules.toSheaf (structureSheafRing (closedSubsetRingedSpace X Z)))
          (n : ℤ)).symm) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.singleFunctor _ 0)
      (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.singleFunctor _ 0)
      (Functor.isoWhiskerRight
        (@asIso _ _ _ _ (localCohomologySheafForgetComparison X Z hZ RHab aHab RH aH)
          (isIso_localCohomologySheafForgetComparison_of_isRightDerivedFunctor
            X Z hZ RHab aHab RH aH)) _) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.singleFunctor _ 0) (Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapDerivedCategorySingleFunctor
        (_root_.SheafOfModules.toSheaf (structureSheafRing X)) 0) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
        (abelianSupportedSectionsOnClosed X Z hZ) RHab aHab
        Stacks.Cohomology.Localization.enoughKInjectives n)

end Stacks.Cohomology.SupportedComplexes

end
