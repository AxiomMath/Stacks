module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AcyclicCovering
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.DerivedSectionsOverBase
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PullbackPushforwardAdjunction
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen

/-!
# `Hⁿ(X, -)` is the cohomology of unbounded derived sections over a base ring

Let `X` be a ringed space and `ρ : A ⟶ Γ(X, 𝒪_X)` a homomorphism from a commutative ring. The
functor `Stacks.Cohomology.DerivedSectionsOverBase.derivedSectionsOver` is the total right
derived functor `RΓ(X, -) : D(𝒪_X) ⥤ D(A)` on the *unbounded* derived category, which is the
carrier of the formal-functions diagram of [Stacks, Tag 0BLD]. Its degree-`n` cohomology at a
sheaf of modules placed in degree zero is the cohomology group `Hⁿ(X, F)` of
[Stacks, Tag 01E3], read as an abelian group.

The identification is an isomorphism of functors, so it transports morphisms of sheaves of
modules, and not merely the vanishing of the groups.

## Main definitions

* `Stacks.Cohomology.ModuleComparison.hfunctorIsoHomologyDerivedSectionsOver`: the natural
  isomorphism.
* `Stacks.Cohomology.ModuleComparison.hgroupIsoHomologyDerivedSectionsOver`: its component at a
  sheaf of modules.

## Implementation notes

Three existing comparisons are composed, one for each discrepancy between the two sides.

* The unbounded derived functor against the classical one:
  `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived`, whose hypothesis — the
  existence of K-injective resolutions — is
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective`.
* The scalars: sections over the whole space are taken here as `A`-modules by restriction of
  scalars along `ρ`, which is exact and may therefore be pulled out of the right derived functor
  by `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso`.
* The coefficients being remembered:
  `Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso` passes from the
  module-valued cohomology to the abelian-group-valued `Hfunctor`.

Restriction of scalars followed by the forgetful functor to abelian groups is the forgetful
functor, so no further comparison stands between the `A`-module-valued and the
abelian-group-valued readings.

## References

* [Stacks Project, Tag 01E3](https://stacks.math.columbia.edu/tag/01E3)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 0BLD](https://stacks.math.columbia.edu/tag/0BLD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsLeray (sectionsOverOpen)
open Stacks.Cohomology.DerivedSectionsOverBase

universe u

namespace Stacks.Cohomology.ModuleComparison

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u}) {A : Type u} [CommRing A]
  (ρ : A →+* (structureSheafRing X).obj.obj (op (⊤ : Opens X.carrier)))

/-- **`Hⁿ(X, -)` is the degree-`n` cohomology of unbounded derived sections over `A`.** The
cohomology functor of [Stacks, Tag 01E3] is the degree-`n` cohomology of
`RΓ(X, -) : D(𝒪_X) ⥤ D(A)` applied to a sheaf of modules placed in degree zero and read as an
abelian group, naturally in the sheaf of modules. -/
def hfunctorIsoHomologyDerivedSectionsOver (n : ℕ) :
    Hfunctor (structureSheafRing X) ⊤ n ≅
      DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0 ⋙
        derivedSectionsOver X ρ ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} A) (n : ℤ) ⋙
            forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u} :=
  letI : (ModuleCat.restrictScalars.{u} ρ).PreservesHomology :=
    Stacks.Cohomology.CechAcyclic.preservesHomology_restrictScalars ρ
  (rightDerivedEvaluationForgetIso (structureSheafRing X) ⊤ n).symm ≪≫
    Functor.isoWhiskerRight
      (rightDerivedCompIso (sectionsOverOpen X ⊤) (ModuleCat.restrictScalars.{u} ρ)
        (sectionsOver X ρ) (Iso.refl _) n) (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}) ≪≫
    Functor.isoWhiskerRight
      (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived (sectionsOver X ρ)
        (derivedSectionsOver X ρ) (derivedSectionsOverUnit X ρ)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective X)
        n).symm
      (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})

/-- The component of `hfunctorIsoHomologyDerivedSectionsOver` at a sheaf of modules: the group
`Hⁿ(X, F)` is the degree-`n` cohomology of `RΓ(X, F)` over `A`. -/
def hgroupIsoHomologyDerivedSectionsOver (n : ℕ) (F : SheafOfModules.{u} (structureSheafRing X)) :
    Hgroup (structureSheafRing X) ⊤ n F ≅
      (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (n : ℤ)).obj
          ((derivedSectionsOver X ρ).obj
            ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj
              F))) :=
  (hfunctorIsoHomologyDerivedSectionsOver X ρ n).app F

/-- The comparison transports a morphism of sheaves of modules: the square relating the map
induced on `Hⁿ(X, -)` to the map induced on the cohomology of `RΓ(X, -)` commutes. -/
theorem hgroupIsoHomologyDerivedSectionsOver_hom_naturality (n : ℕ)
    {F G : SheafOfModules.{u} (structureSheafRing X)} (φ : F ⟶ G) :
    (Hfunctor (structureSheafRing X) ⊤ n).map φ ≫
        (hgroupIsoHomologyDerivedSectionsOver X ρ n G).hom =
      (hgroupIsoHomologyDerivedSectionsOver X ρ n F).hom ≫
        (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0 ⋙
          derivedSectionsOver X ρ ⋙
            DerivedCategory.homologyFunctor (ModuleCat.{u} A) (n : ℤ) ⋙
              forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).map φ :=
  (hfunctorIsoHomologyDerivedSectionsOver X ρ n).hom.naturality φ

end Stacks.Cohomology.ModuleComparison

end
