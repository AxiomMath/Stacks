module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedGlobalSectionsCohomology
public import StacksFrontier.Homology.Ext.CorepresentedHomotopyComparison
public import StacksFrontier.Homology.Injectives.KInjective.RightDerivedCriterion
public import StacksFrontier.CategoryTheory.Shift.ShiftSequenceTransport

/-!
# The cohomology of `RΓ(X, -)` as morphisms out of the structure sheaf

For an algebraic space `X` and `A ∈ D(𝒪_X)`, `H^0(X, A) = H^0(RΓ(X, A))` is the group of
morphisms `𝒪_X[0] ⟶ A` of `D(𝒪_X)`, **naturally in `A`**: both functors are right derived
functors of `L ↦ H^0(Γ(X, L))` on the homotopy category of `𝒪_X`-modules (their comparisons
being invertible at K-injective complexes), so they agree by the uniqueness of right derived
functors.

## Main definitions

* `AlgebraicGeometry.Space.globalSectionsZeroHomologyNatIso`: `H^0(X, -) ≅ Hom(𝒪_X[0], -)`, as
  functors `D(𝒪_X) ⥤ AddCommGrpCat` (universe-lifted).
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
attribute [local instance] ModuleCat.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 20000] ModuleCat.hasDerivedCategory
attribute [local instance] isGrothendieckAbelian_modules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (X : AlgebraicSpaces B S hS)

/-- The structure sheaf of `X` as an `𝒪_X`-module on the small étale site. -/
abbrev unitModuleSmallEtale : Modules.{u, u} B S hS X.1 X.2 :=
  SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS X.1 X.2).O))

/-- Global sections of `𝒪_X`-modules, read in abelian groups. -/
abbrev moduleGlobalSectionsSmallEtaleAb :
    Modules.{u, u} B S hS X.1 X.2 ⥤ AddCommGrpCat.{u + 1} :=
  moduleGlobalSectionsSmallEtale.{u, u} B S hS X.1 X.2 ⋙
    forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2)) AddCommGrpCat.{u + 1}

/-- `𝒪_X` corepresents global sections, read in abelian groups. -/
def unitCoyonedaGlobalSectionsIso :
    preadditiveCoyoneda.obj (op (unitModuleSmallEtale X)) ≅ moduleGlobalSectionsSmallEtaleAb X :=
  coyonedaUnitGlobalSectionsIso _

/-- `L ↦ H^0(Γ(X, L))` on the homotopy category of `𝒪_X`-modules, in abelian groups. -/
abbrev globalSectionsZeroHomologyHomotopy :
    HomotopyCategory (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ) ⥤ AddCommGrpCat.{u + 1} :=
  Stacks.Cohomology.Corepresented.homotopyHomologyFunctor.{u + 1}
    (moduleGlobalSectionsSmallEtaleAb X) 0

/-- `H^0(X, -) = H^0(RΓ(X, -))`, read in abelian groups. -/
abbrev globalSectionsZeroHomology :
    DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤ AddCommGrpCat.{u + 1} :=
  derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2 ⋙
    DerivedCategory.homologyFunctor
      (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2)) 0 ⋙
    forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2)) AddCommGrpCat.{u + 1} ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u + 1}

/-- `Hom(𝒪_X[0], -)` on `D(𝒪_X)`. -/
abbrev unitDerivedHom :
    DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤ AddCommGrpCat.{u + 1} :=
  shiftFunctor (DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (0 : ℤ) ⋙
    preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor _ 0).obj
      (unitModuleSmallEtale X))) ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u + 1}

/-- The comparison exhibiting `Hom(𝒪_X[0], -)` as a right derived functor of
`L ↦ H^0(Γ(X, L))`. -/
abbrev unitDerivedHomUnit :
    globalSectionsZeroHomologyHomotopy X ⟶ DerivedCategory.Qh ⋙ unitDerivedHom X :=
  Stacks.Cohomology.Corepresented.homotopyComparison.{u + 1} (moduleGlobalSectionsSmallEtaleAb X)
    (unitModuleSmallEtale X) (unitCoyonedaGlobalSectionsIso X) 0

/-- `Γ(X, -)` on the homotopy category, followed by the localization. -/
abbrev globalSectionsHomotopyQh :
    HomotopyCategory (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ) ⥤
      DerivedCategory (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2)) :=
  (moduleGlobalSectionsSmallEtale.{u, u} B S hS X.1 X.2).mapHomotopyCategory
    (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- On complexes, `L ↦ H^0(Γ(X, L))` read in abelian groups is `H^0` of `Γ(X, L)` in the derived
category of `Γ(X, 𝒪_X)`-modules, followed by the forgetful functor. -/
def globalSectionsZeroHomologyHomotopyIso :
    HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ globalSectionsZeroHomologyHomotopy X ≅
      HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ globalSectionsHomotopyQh X ⋙
        DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2)) 0 ⋙
        forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2))
          AddCommGrpCat.{u + 1} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u + 1} :=
  Stacks.Cohomology.Corepresented.quotientCompHomotopyHomologyIso.{u + 1}
      (moduleGlobalSectionsSmallEtaleAb X) 0 ≪≫
    Functor.isoWhiskerLeft
      ((moduleGlobalSectionsSmallEtale.{u, u} B S hS X.1 X.2).mapHomologicalComplex
        (ComplexShape.up ℤ))
      (Functor.isoWhiskerRight
        ((forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2))
          AddCommGrpCat.{u + 1}).mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) 0)
        AddCommGrpCat.uliftFunctor.{u + 1, u + 1}) ≪≫
    Functor.isoWhiskerLeft
      ((moduleGlobalSectionsSmallEtale.{u, u} B S hS X.1 X.2).mapHomologicalComplex
        (ComplexShape.up ℤ))
      (Functor.isoWhiskerRight
        (DerivedCategory.homologyFunctorFactors
          (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2)) 0).symm
        (forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2))
          AddCommGrpCat.{u + 1} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u + 1})) ≪≫
    Functor.isoWhiskerRight
      (((moduleGlobalSectionsSmallEtale.{u, u} B S hS X.1 X.2).mapHomologicalComplex
          (ComplexShape.up ℤ)).isoWhiskerLeft
          (DerivedCategory.quotientCompQhIso
            (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2))).symm ≪≫
        Functor.isoWhiskerRight
          ((moduleGlobalSectionsSmallEtale.{u, u} B S hS X.1 X.2).mapHomotopyCategoryFactors
            (ComplexShape.up ℤ)).symm DerivedCategory.Qh)
      (DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2)) 0 ⋙
        forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2))
          AddCommGrpCat.{u + 1} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u + 1})

/-- The comparison exhibiting `H^0(X, -)` as a right derived functor of `L ↦ H^0(Γ(X, L))`: the
unit of `RΓ(X, -)`, after the identification of the two readings of `H^0(Γ(X, L))`. -/
def globalSectionsZeroHomologyUnit :
    globalSectionsZeroHomologyHomotopy X ⟶ DerivedCategory.Qh ⋙ globalSectionsZeroHomology X :=
  Quotient.natTransLift _ ((globalSectionsZeroHomologyHomotopyIso X).hom ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
      (Functor.whiskerRight ((globalSectionsHomotopyQh X).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)))
        (DerivedCategory.homologyFunctor
            (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2)) 0 ⋙
          forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2))
            AddCommGrpCat.{u + 1} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u + 1})))

/-- The component of `globalSectionsZeroHomologyUnit` at a complex: the identification of the two
readings of `H^0(Γ(X, L))`, followed by `H^0` of the unit of `RΓ(X, -)`. -/
theorem globalSectionsZeroHomologyUnit_app_quotient
    (L : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) :
    (globalSectionsZeroHomologyUnit X).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L) =
      (globalSectionsZeroHomologyHomotopyIso X).hom.app L ≫
        (DerivedCategory.homologyFunctor
            (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2)) 0 ⋙
          forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2))
            AddCommGrpCat.{u + 1} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u + 1}).map
          (((globalSectionsHomotopyQh X).totalRightDerivedUnit DerivedCategory.Qh
            (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))).app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)) :=
  rfl

/-- `L ↦ H^0(Γ(X, L))` has a right derived functor, since every complex of `𝒪_X`-modules has a
K-injective resolution. -/
instance hasRightDerivedFunctor_globalSectionsZeroHomologyHomotopy :
    (globalSectionsZeroHomologyHomotopy X).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) :=
  haveI := (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    (globalSectionsZeroHomologyHomotopy X)
    (Stacks.Injectives.exists_kInjective_resolution_of_grothendieck
      (C := Modules.{u, u} B S hS X.1 X.2))).1
  inferInstance

/-- `Hom(𝒪_X[0], -)` is a right derived functor of `L ↦ H^0(Γ(X, L))`. -/
instance isRightDerivedFunctor_unitDerivedHom :
    (unitDerivedHom X).IsRightDerivedFunctor (unitDerivedHomUnit X)
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) :=
  Stacks.Injectives.rightDerived_of_kInjective_units _ _ _ fun _ _ => inferInstance

/-- `H^0(X, -)` is a right derived functor of `L ↦ H^0(Γ(X, L))`: its comparison is invertible at
K-injective complexes, where the unit of `RΓ(X, -)` is. -/
instance isRightDerivedFunctor_globalSectionsZeroHomology :
    (globalSectionsZeroHomology X).IsRightDerivedFunctor (globalSectionsZeroHomologyUnit X)
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) := by
  refine Stacks.Injectives.rightDerived_of_kInjective_units _ _ _ fun I _ => ?_
  have h := Stacks.Injectives.rightDerivedUnit_isIso_at_kInjective (globalSectionsHomotopyQh X)
    _ ((globalSectionsHomotopyQh X).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))) I
  rw [globalSectionsZeroHomologyUnit_app_quotient]
  infer_instance

/-- **`H^0(X, -) ≅ Hom(𝒪_X[0], -)`, naturally on `D(𝒪_X)`**: both are right derived functors of
`L ↦ H^0(Γ(X, L))`. -/
def globalSectionsZeroHomologyIso : globalSectionsZeroHomology X ≅ unitDerivedHom X :=
  Functor.rightDerivedUnique _ _ (globalSectionsZeroHomologyUnit X) (unitDerivedHomUnit X)
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))

/-- `RΓ(X, -)` commutes with the shifts: the structure carried by a total right derived functor of
a functor commuting with the shifts. -/
instance commShift_derivedModuleGlobalSectionsSmallEtaleAtModel :
    (derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2).CommShift ℤ :=
  Functor.IsRightDerivedFunctor.commShift
    (derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2)
    ((globalSectionsHomotopyQh X).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) ℤ

/-- `Hom(𝒪_X[0], -)`, universe-lifted. -/
abbrev unitHomLifted :
    DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤ AddCommGrpCat.{u + 1} :=
  preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor _ 0).obj
    (unitModuleSmallEtale X))) ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u + 1}

/-- `H^0(X, -) ≅ Hom(𝒪_X[0], -)` without the shift by `0`. -/
def globalSectionsZeroHomologyIsoUnitHom : globalSectionsZeroHomology X ≅ unitHomLifted X :=
  globalSectionsZeroHomologyIso X ≪≫
    Functor.isoWhiskerRight (shiftFunctorZero (DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) ℤ)
      (unitHomLifted X) ≪≫ Functor.leftUnitor _

/-- **`H^n(X, -) ≅ Hom(𝒪_X[0], -⟦n⟧)`, naturally on `D(𝒪_X)`**, read in abelian groups. -/
def cohomologyIsoUnitHomShift (n : ℤ) :
    derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2 ⋙
        DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2)) n ⋙
        forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2))
          AddCommGrpCat.{u + 1} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u + 1} ≅
      shiftFunctor (DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) n ⋙ unitHomLifted X :=
  Stacks.CategoryTheory.ShiftSequenceTransport.shiftedIso
    (derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2)
    (DerivedCategory.homologyFunctor
      (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2)) 0)
    (forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2))
      AddCommGrpCat.{u + 1} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u + 1})
    (unitHomLifted X) (globalSectionsZeroHomologyIsoUnitHom X) n

/-- **The boundary maps of cohomology are composition with the third morphism of the triangle.**
For a triangle `T` of `D(𝒪_X)`, the identification `H^n(X, -) ≅ Hom(𝒪_X[0], -⟦n⟧)` carries the
boundary map `H^{n₀}(X, T₃) ⟶ H^{n₁}(X, T₁)` of the triangle `RΓ(X, T)` to composition with
`T.mor₃⟦n₀⟧ : T₃⟦n₀⟧ ⟶ T₁⟦1⟧⟦n₀⟧ = T₁⟦n₁⟧`. -/
theorem cohomologyIsoUnitHomShift_homologySequenceδ
    (T : Pretriangulated.Triangle (DerivedCategory (Modules.{u, u} B S hS X.1 X.2)))
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2))
          AddCommGrpCat.{u + 1} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u + 1}).map
        ((DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2)) 0).homologySequenceδ
          ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2).mapTriangle.obj T)
          n₀ n₁ h) ≫
        (cohomologyIsoUnitHomShift X n₁).hom.app T.obj₁ =
      (cohomologyIsoUnitHomShift X n₀).hom.app T.obj₃ ≫
        (unitHomLifted X).map (T.mor₃⟦n₀⟧' ≫
          (shiftFunctorAdd' (DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) 1 n₀ n₁
            (by omega)).inv.app T.obj₁) :=
  Stacks.CategoryTheory.ShiftSequenceTransport.shiftedIso_delta _ _ _ _ _ T.mor₃ n₀ n₁ h

end AlgebraicGeometry.Space

end
