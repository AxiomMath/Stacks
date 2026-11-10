module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologicalBaseChange
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayForDerivedSections
public import StacksFrontier.AlgebraicGeometry.AffineVanishingUnbounded
import all StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayForDerivedSections

/-!
# The canonical comparisons behind the pullback map on cohomology

`Stacks.DeRham.GysinCohomologyBaseChange.CohomologyPullbackComparison` packages the two canonical
comparisons that the pullback map on the cohomology groups `Hgroup` is built from: the map
`(G_*ℳ')[-a] ⟶ RG_*(ℳ'[-a])` of [Stacks, Tag 01F8] and the Leray identification
`RΓ(X, RG_*K) ≅ RΓ(X', K)` of [Stacks, Tag 01EZ], the latter with values in `D(Ab)`, which is the
model `Hgroup` lives in. This file **constructs** both, for an arbitrary morphism of ringed spaces.

## Main definitions

* `singleToDerivedPushforward`: the comparison of [Stacks, Tag 01F8], the derivation unit of
  `RG_*` read on single complexes.
* `lerayUnitAb`, `lerayComparisonAb`: the unit-level and derived Leray comparison for the
  abelian-group valued global sections functors.
* `CohomologyPullbackComparison.canonical`: the canonical comparisons.

## Main results

* `isIso_derivedGlobalSectionsUnit_app_pushforward`: the unit of `RΓ(X, -)` (abelian-group
  valued) is invertible at the direct image of a K-injective complex.  The module-valued
  statement is the private step of [Stacks, Tag 0D5W] in
  `StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayForDerivedSections`; it is
  transported along the exact, conservative forgetful functor, which preserves and reflects
  quasi-isomorphisms.
* `isIso_lerayComparisonAb`: **[Stacks, Tag 01EZ] in `D(Ab)`**, the Leray comparison is an
  isomorphism, with no hypothesis on the morphism.

## References

* [Stacks Project, Tag 01F8](https://stacks.math.columbia.edu/tag/01F8)
* [Stacks Project, Tag 01EZ](https://stacks.math.columbia.edu/tag/01EZ)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DeRham.CohomologicalGysin

namespace Stacks.DeRham.GysinCohomologyBaseChange

universe u

open DerivedCategory

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory

variable {X X' : RingedSpace.{u, u}} (G : X' ⟶ X)

/-- **The comparison `(G_*ℳ')[-a] ⟶ RG_*(ℳ'[-a])` of [Stacks, Tag 01F8]**, natural in `ℳ'`:
the single complex read in the homotopy category, the derivation unit of `RG_*`, and the single
complex read back in the derived category. -/
def singleToDerivedPushforward (a : ℤ) :
    modulePushforward G ⋙ singleFunctor (RModules X) a ⟶
      singleFunctor (RModules X') a ⋙ derivedPushforward G :=
  Functor.whiskerLeft (modulePushforward G) (singleFunctorIsoCompQh (RModules X) a).hom ≫
    Functor.whiskerRight (Functor.mapHomotopyCategorySingleFunctor (modulePushforward G) a).inv
      DerivedCategory.Qh ≫
    Functor.whiskerLeft (HomotopyCategory.singleFunctor (RModules X') a)
      (derivedPushforwardUnit G) ≫
    Functor.whiskerRight (singleFunctorIsoCompQh (RModules X') a).inv (derivedPushforward G)

/-- Global sections on `X'` *are* global sections of the direct image on `X`, on the nose. -/
def pushforwardSectionsIso :
    modulePushforward G ⋙ secF (structureSheafRing X) ⊤ ≅ secF (structureSheafRing X') ⊤ :=
  Iso.refl _

/-- **The Leray unit** `Γ(X', -) ⟶ RΓ(X, -) ∘ RG_*` on the homotopy category, for the
abelian-group valued sections: `Γ(X', -) = Γ(X, G_* -)` on the nose, followed by the units of
`RΓ(X, -)` and of `RG_*`. -/
def lerayUnitAb :
    Stacks.DerivedFunctor.homotopyMap (secF (structureSheafRing X') ⊤) ⟶
      DerivedCategory.Qh ⋙ (derivedPushforward G ⋙ derivedGlobalSections X) :=
  Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso (pushforwardSectionsIso G)
      (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft ((modulePushforward G).mapHomotopyCategory (ComplexShape.up ℤ))
      (derivedGlobalSectionsUnit X) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (derivedPushforwardUnit G) (derivedGlobalSections X) ≫
    (Functor.associator _ _ _).hom

/-- **The Leray comparison** `RΓ(X', -) ⟶ RΓ(X, -) ∘ RG_*` in `D(Ab)`, induced by `lerayUnitAb`
through the universal property of the right derived functor. -/
def lerayComparisonAb :
    derivedGlobalSections X' ⟶ derivedPushforward G ⋙ derivedGlobalSections X :=
  (derivedGlobalSections X').rightDerivedDesc (derivedGlobalSectionsUnit X')
    (HomotopyCategory.quasiIso (RModules X') (ComplexShape.up ℤ)) _ (lerayUnitAb G)

/-- `Qh` of the image of a cochain map under an additive functor is invertible exactly when the
image is a quasi-isomorphism. -/
theorem isIso_Qh_map_mapHomotopyCategory_quotient_iff {A B : Type*} [Category A] [Abelian A]
    [Category B] [Abelian B] {_ : HasDerivedCategory B} (F : A ⥤ B) [F.Additive]
    {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    IsIso (DerivedCategory.Qh.map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f))) ↔
      QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) :=
  (DerivedCategory.isIso_Qh_map_iff _).trans
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).trans
      (HomologicalComplex.mem_quasiIso_iff _))

/-- **The unit of abelian-group valued derived global sections is invertible at the direct
image of a K-injective complex**, transported from the module-valued statement of
[Stacks, Tag 0D5W]. -/
theorem isIso_derivedGlobalSectionsUnit_app_pushforward
    (I : CochainComplex (RModules X') ℤ) (hI : I.IsKInjective) :
    IsIso ((derivedGlobalSectionsUnit X).app
      (((modulePushforward G).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (RModules X') (ComplexShape.up ℤ)).obj I))) := by
  have hmod :=
    Stacks.Cohomology.DerivedSectionsLeray.isIso_derivedSectionsOverOpenUnit_app_pushforward
      G ⊤ I hI
  obtain ⟨J, s, hJ, hs⟩ := exists_quasiIso_isKInjective X
    (((modulePushforward G).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
  have h1 := (Stacks.SmallDerivedCategory.isIso_rightDerivedUnit_app_quotient_iff
    (exists_quasiIso_isKInjective X) _ _
    (Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpenUnit X ⊤) s hJ hs).1 hmod
  refine (Stacks.SmallDerivedCategory.isIso_rightDerivedUnit_app_quotient_iff
    (exists_quasiIso_isKInjective X) _ _ (derivedGlobalSectionsUnit X) s hJ hs).2 ?_
  have h1' := (isIso_Qh_map_mapHomotopyCategory_quotient_iff _ s).1 h1
  refine (isIso_Qh_map_mapHomotopyCategory_quotient_iff (secF (structureSheafRing X) ⊤) s).2 ?_
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (forget₂ (ModuleCat _) AddCommGrpCat)).2 h1'

/-- **[Stacks, Tag 01EZ] in `D(Ab)`.** The Leray comparison is invertible: `RΓ(X, -) ∘ RG_*`
with `lerayUnitAb` is a right derived functor of `Γ(X', -)`, its unit being invertible at
K-injective complexes by `isIso_derivedGlobalSectionsUnit_app_pushforward`. -/
theorem isIso_lerayComparisonAb : IsIso (lerayComparisonAb G) := by
  have hderived : (derivedPushforward G ⋙ derivedGlobalSections X).IsRightDerivedFunctor
      (lerayUnitAb G) (HomotopyCategory.quasiIso (RModules X') (ComplexShape.up ℤ)) := by
    refine isRightDerivedFunctor_of_isIso_app_isKInjective.{u, u + 1, u + 1, u + 1, u + 1, u + 1}
      _ (exists_quasiIso_isKInjective X') DerivedCategory.Qh _ _ fun I hI => ?_
    have h₂ := isIso_derivedGlobalSectionsUnit_app_pushforward G I hI
    have h₃ := isIso_derivedPushforwardUnit_app_of_isKInjective G I hI
    change IsIso (DerivedCategory.Qh.map _ ≫ 𝟙 _ ≫ (derivedGlobalSectionsUnit X).app _ ≫ 𝟙 _ ≫
      (derivedGlobalSections X).map ((derivedPushforwardUnit G).app _) ≫ 𝟙 _)
    infer_instance
  exact (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc _
    (derivedGlobalSectionsUnit X') _ _ (lerayUnitAb G)).1 hderived

/-- **The canonical comparisons** of [Stacks, Tag 01F8] and [Stacks, Tag 01EZ], constructed;
the Leray identification is the inverse of `lerayComparisonAb`. -/
def CohomologyPullbackComparison.canonical : CohomologyPullbackComparison G where
  singleMap a := singleToDerivedPushforward G a
  leray := haveI := isIso_lerayComparisonAb G; (asIso (lerayComparisonAb G)).symm

end Stacks.DeRham.GysinCohomologyBaseChange

end
