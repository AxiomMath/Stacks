module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.DerivedFunctorLongExact
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.InjectiveSheavesRestrictOnto
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sections with support in a closed subset

Let `Z` be a closed subset of a ringed space `X`, and let `U = X ∖ Z`.  Sections with support
in `Z` are the kernel of restriction to `U`, so that `0 ⟶ Γ_Z(X, -) ⟶ Γ(X, -) ⟶ Γ(U, -)` is
left exact by construction.  Restriction to `U` is moreover surjective on an *injective* module
sheaf (Tag 01EA), so the sequence is short exact on injectives, and the right derived functors
of the three fit into a long exact sequence.

## Main definitions

* `openComplement`: the open complement of a closed subset.
* `sectionsOnComplement`: sections on the complement, as modules over the global functions.
* `restrictionToComplement`: restriction of a global section to the complement.
* `sectionsWithSupport`: sections supported on the closed subset, i.e. the kernel of
  `restrictionToComplement`.
* `derivedSupportInclusion`, `derivedRestrictionToComplement`: the canonical maps between the
  total right derived functors, and `SectionsWithSupportTriangleData` for the triangle data
  that completes them.
* `homotopyToDerived`: the functor whose right derived functors occur in the result.

## Main results

* `epi_restrictionToComplement_app_of_injective`: restriction to the complement is surjective
  on an injective module sheaf.
* `shortExact_appShortComplex_of_injective`: the short complex is short exact at an injective
  module sheaf.
* `longExact_rightDerived_sectionsWithSupport`: the resulting long exact sequence of right
  derived functors, obtained from
  `CategoryTheory.longExact_rightDerived_of_shortExact_on_injectives`.
* `derivedSupportInclusion_fac`, `derivedRestrictionToComplement_fac`: the two canonical maps
  between total right derived functors are pinned down by their composites with the units.

## Implementation notes

Sections supported on `Z` are realized as the kernel of restriction from `X` to its open
complement, and `sectionsWithSupport X Z hZ` is by definition
`kernel (restrictionToComplement X Z hZ)`.  No support API is used: the identification of this
kernel with the sections whose support (in the sense of Tag 01AT) lies in `Z` is not needed for
any statement in this file.

Left exactness of the short complex at a module sheaf `M` is the statement that the kernel in
the functor category is computed pointwise, which is `KernelFork.mapIsLimit` for the evaluation
functor at `M`; the latter preserves finite limits because the target has them.

The distinguished triangle of Tag 0G71 for an object of the *unbounded* derived category needs
a functorial K-injective resolution with injective terms (Stacks 079P); it is proved in
`StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SectionsWithSupportTriangle`, which
supplies that resolution from
`Stacks.Injectives.FunctorialEnlargement.exists_functorial_quasiIso_isKInjective`.  This file
provides the statement of the triangle data, `SectionsWithSupportTriangleData`, and the two
canonical transformations it completes.

## References

* [Stacks Project, Tag 0G71](https://stacks.math.columbia.edu/tag/0G71)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.Pretriangulated
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.SectionsWithSupport


attribute [local instance] HasDerivedCategory.standard


/-- The unbounded derived category of modules over the structure sheaf of a ringed space. -/
public noncomputable abbrev DerivedModuleSheaves (X : RingedSpace.{u, u}) :=
  DerivedCategory (ModuleSheaves X)

/-- Modules over the ring of global functions on a ringed space. -/
public noncomputable abbrev GlobalModules (X : RingedSpace.{u, u}) :=
  ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))

/-- The unbounded derived category of modules over the ring of global functions. -/
public noncomputable abbrev DerivedGlobalModules (X : RingedSpace.{u, u}) :=
  DerivedCategory (GlobalModules X)

/-- The open complement of a closed subset. -/
public def openComplement {X : RingedSpace.{u, u}} (Z : Set X) (hZ : IsClosed Z) : Opens X :=
  ⟨Zᶜ, hZ.isOpen_compl⟩

/-- Evaluation on the whole space is additive. -/
public instance globalSections_additive (X : RingedSpace.{u, u}) :
    (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)).Additive where
  map_add := rfl

/-- Sections on the complement of `Z`, regarded as modules over the ring of global
functions on `X`. -/
public noncomputable abbrev sectionsOnComplement
    (X : RingedSpace.{u, u}) (Z : Set X) (hZ : IsClosed Z) :
    ModuleSheaves X ⥤ GlobalModules X :=
  SheafOfModules.evaluation (structureSheafRing X)
      (op (openComplement Z hZ)) ⋙
    ModuleCat.restrictScalars
      ((structureSheafRing X).obj.map
        (homOfLE (le_top : openComplement Z hZ ≤ ⊤)).op).hom

/-- Sections on the complement, with their global scalar structure, form an additive functor. -/
public instance sectionsOnComplement_additive
    (X : RingedSpace.{u, u}) (Z : Set X) (hZ : IsClosed Z) :
    (sectionsOnComplement X Z hZ).Additive where
  map_add := rfl

/-- Restriction of a global section to the complement of `Z`, with scalars restricted from
the functions on the complement to the global functions. -/
public def restrictionToComplement (X : RingedSpace.{u, u}) (Z : Set X) (hZ : IsClosed Z) :
    SheafOfModules.evaluation (structureSheafRing X) (op ⊤) ⟶
      sectionsOnComplement X Z hZ :=
  Functor.whiskerLeft (SheafOfModules.forget (structureSheafRing X))
    (PresheafOfModules.restriction (structureSheafRing X).obj
      (homOfLE (le_top : openComplement Z hZ ≤ ⊤)).op)

/-- Global sections whose restriction to `X ∖ Z` vanishes.  For closed `Z`, these are
exactly the global sections whose support is contained in `Z`. -/
public def sectionsWithSupport (X : RingedSpace.{u, u}) (Z : Set X) (hZ : IsClosed Z) :
    ModuleSheaves X ⥤ GlobalModules X :=
  kernel (restrictionToComplement X Z hZ)

/-- Taking sections with support preserves zero morphisms. -/
public instance sectionsWithSupport_preservesZeroMorphisms
    (X : RingedSpace.{u, u}) (Z : Set X) (hZ : IsClosed Z) :
    (sectionsWithSupport X Z hZ).PreservesZeroMorphisms := by
  change (kernel (restrictionToComplement X Z hZ)).PreservesZeroMorphisms
  constructor
  intro A B
  apply (cancel_mono ((kernel.ι (restrictionToComplement X Z hZ)).app B)).1
  rw [(kernel.ι (restrictionToComplement X Z hZ)).naturality]
  simp

/-- Taking sections with support is additive. -/
public instance sectionsWithSupport_additive
    (X : RingedSpace.{u, u}) (Z : Set X) (hZ : IsClosed Z) :
    (sectionsWithSupport X Z hZ).Additive := by
  change (kernel (restrictionToComplement X Z hZ)).Additive
  constructor
  intro A B f g
  apply (cancel_mono ((kernel.ι (restrictionToComplement X Z hZ)).app B)).1
  rw [(kernel.ι (restrictionToComplement X Z hZ)).naturality]
  simp

/-- The functor on homotopy categories obtained by applying an additive functor degreewise
and then passing to the unbounded derived category. -/
public noncomputable abbrev homotopyToDerived (X : RingedSpace.{u, u})
    (F : ModuleSheaves X ⥤ GlobalModules X) [F.Additive] :=
  F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- The canonical map from derived sections with support to derived global sections. -/
public noncomputable def derivedSupportInclusion
    (X : RingedSpace.{u, u}) (Z : Set X) (hZ : IsClosed Z)
    (RΓZ RΓ : DerivedModuleSheaves X ⥤ DerivedGlobalModules X)
    (aZ : homotopyToDerived X (sectionsWithSupport X Z hZ) ⟶ DerivedCategory.Qh ⋙ RΓZ)
    (aX : homotopyToDerived X
      (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)) ⟶
        DerivedCategory.Qh ⋙ RΓ)
    [RΓZ.IsRightDerivedFunctor aZ
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))] :
    RΓZ ⟶ RΓ :=
  RΓZ.rightDerivedNatTrans RΓ aZ aX
    (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))
    (Functor.whiskerRight
      ((show sectionsWithSupport X Z hZ ⟶ _ from
        kernel.ι (restrictionToComplement X Z hZ)).mapHomotopyCategory
        (ComplexShape.up ℤ)) DerivedCategory.Qh)

/-- The canonical derived support-forgetting map is characterized by its composite with the
unit of the right derived functor. -/
@[reassoc]
public lemma derivedSupportInclusion_fac
    (X : RingedSpace.{u, u}) (Z : Set X) (hZ : IsClosed Z)
    (RΓZ RΓ : DerivedModuleSheaves X ⥤ DerivedGlobalModules X)
    (aZ : homotopyToDerived X (sectionsWithSupport X Z hZ) ⟶ DerivedCategory.Qh ⋙ RΓZ)
    (aX : homotopyToDerived X
      (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)) ⟶
        DerivedCategory.Qh ⋙ RΓ)
    [RΓZ.IsRightDerivedFunctor aZ
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))] :
    aZ ≫ Functor.whiskerLeft DerivedCategory.Qh
      (derivedSupportInclusion X Z hZ RΓZ RΓ aZ aX) =
        Functor.whiskerRight
          ((show sectionsWithSupport X Z hZ ⟶ _ from
            kernel.ι (restrictionToComplement X Z hZ)).mapHomotopyCategory
            (ComplexShape.up ℤ)) DerivedCategory.Qh ≫ aX :=
  Functor.rightDerivedNatTrans_fac _ _ _ _ _ _

/-- The canonical map from derived global sections to derived sections on the complement. -/
public noncomputable def derivedRestrictionToComplement
    (X : RingedSpace.{u, u}) (Z : Set X) (hZ : IsClosed Z)
    (RΓ RΓU : DerivedModuleSheaves X ⥤ DerivedGlobalModules X)
    (aX : homotopyToDerived X
      (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)) ⟶
        DerivedCategory.Qh ⋙ RΓ)
    (aU : homotopyToDerived X (sectionsOnComplement X Z hZ) ⟶ DerivedCategory.Qh ⋙ RΓU)
    [RΓ.IsRightDerivedFunctor aX
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))] :
    RΓ ⟶ RΓU :=
  RΓ.rightDerivedNatTrans RΓU aX aU
    (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))
    (Functor.whiskerRight
      ((restrictionToComplement X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh)

/-- The canonical derived restriction map is characterized by its composite with the unit of
the right derived functor. -/
@[reassoc]
public lemma derivedRestrictionToComplement_fac
    (X : RingedSpace.{u, u}) (Z : Set X) (hZ : IsClosed Z)
    (RΓ RΓU : DerivedModuleSheaves X ⥤ DerivedGlobalModules X)
    (aX : homotopyToDerived X
      (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)) ⟶
        DerivedCategory.Qh ⋙ RΓ)
    (aU : homotopyToDerived X (sectionsOnComplement X Z hZ) ⟶ DerivedCategory.Qh ⋙ RΓU)
    [RΓ.IsRightDerivedFunctor aX
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))] :
    aX ≫ Functor.whiskerLeft DerivedCategory.Qh
      (derivedRestrictionToComplement X Z hZ RΓ RΓU aX aU) =
        Functor.whiskerRight
          ((restrictionToComplement X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ))
          DerivedCategory.Qh ≫ aU :=
  Functor.rightDerivedNatTrans_fac _ _ _ _ _ _

/-- The boundary and distinguishedness data completing two natural transformations to a
functorial triangle. -/
public structure SectionsWithSupportTriangleData
    (X : RingedSpace.{u, u})
    (RΓZ RΓ RΓU : DerivedModuleSheaves X ⥤ DerivedGlobalModules X)
    (i : RΓZ ⟶ RΓ) (r : RΓ ⟶ RΓU) where
  /-- The connecting morphism, natural in the derived sheaf. -/
  boundary : RΓU ⟶ RΓZ ⋙ shiftFunctor (DerivedGlobalModules X) (1 : ℤ)
  /-- The resulting triangle is distinguished at every derived sheaf. -/
  distinguished (K) : Triangle.mk (i.app K) (r.app K) (boundary.app K) ∈
    distTriang (DerivedGlobalModules X)

/-- Restriction to the complement of a closed set is surjective on an injective module
sheaf, so it is an epimorphism of modules over the global functions. -/
lemma epi_restrictionToComplement_app_of_injective (X : RingedSpace.{u, u}) (Z : Set X)
    (hZ : IsClosed Z) (I : ModuleSheaves X) [CategoryTheory.Injective I] :
    Epi ((restrictionToComplement X Z hZ).app I) :=
  ConcreteCategory.epi_of_surjective _ fun y =>
    Stacks.Cohomology.InjectiveRestriction.injective_restriction_surjective
      (structureSheafRing X) I (le_top : openComplement Z hZ ≤ ⊤) y

/-- The composite of the kernel inclusion and restriction to the complement is zero. -/
lemma sectionsWithSupport_comp_restrictionToComplement (X : RingedSpace.{u, u}) (Z : Set X)
    (hZ : IsClosed Z) :
    kernel.ι (restrictionToComplement X Z hZ) ≫ restrictionToComplement X Z hZ = 0 :=
  kernel.condition _

/-- **The input to the long exact sequence of `Rⁿ` of sections with support.**  At an injective
module sheaf the short complex `Γ_Z(X, -) ⟶ Γ(X, -) ⟶ Γ(U, -)` is short exact: it is left
exact by construction, since `sectionsWithSupport` is the kernel of `restrictionToComplement`
and kernels in a functor category are computed pointwise, and the restriction map is surjective
because an injective module sheaf is flasque (Tag 01EA). -/
@[sga "2 I 1.8" "special case"]
lemma shortExact_appShortComplex_of_injective (X : RingedSpace.{u, u}) (Z : Set X)
    (hZ : IsClosed Z) (I : ModuleSheaves X) (hI : CategoryTheory.Injective I) :
    (CategoryTheory.NatTrans.appShortComplex
      (kernel.ι (restrictionToComplement X Z hZ)) (restrictionToComplement X Z hZ)
      (sectionsWithSupport_comp_restrictionToComplement X Z hZ) I).ShortExact := by
  have := hI
  have hlim := KernelFork.mapIsLimit
    (c := KernelFork.ofι (kernel.ι (restrictionToComplement X Z hZ)) (kernel.condition _))
    (kernelIsKernel (restrictionToComplement X Z hZ))
    ((CategoryTheory.evaluation (ModuleSheaves X) (GlobalModules X)).obj I)
  have hm : Mono (((CategoryTheory.evaluation (ModuleSheaves X) (GlobalModules X)).obj I).map
      (kernel.ι (restrictionToComplement X Z hZ))) :=
    Functor.map_mono _ _
  exact
    { exact := ShortComplex.exact_of_f_is_kernel _ hlim
      mono_f := hm
      epi_g := epi_restrictionToComplement_app_of_injective X Z hZ I }

/-- Modules over the structure sheaf of a ringed space form a Grothendieck abelian category,
hence have enough injectives. -/
noncomputable instance moduleSheaves_enoughInjectives (X : RingedSpace.{u, u}) :
    CategoryTheory.EnoughInjectives (ModuleSheaves X) := by
  let _ : CategoryTheory.IsGrothendieckAbelian.{u} (ModuleSheaves X) := inferInstance
  exact CategoryTheory.IsGrothendieckAbelian.enoughInjectives

/-- **The long exact sequence of cohomology with support in a closed subset.**  For a closed
subset `Z` of a ringed space `X` with open complement `U`, the right derived functors of
sections with support in `Z`, of global sections, and of sections on `U` form a long exact
sequence

`0 ⟶ Γ_Z(X, -) ⟶ Γ(X, -) ⟶ Γ(U, -) ⟶ H¹_Z(X, -) ⟶ H¹(X, -) ⟶ H¹(U, -) ⟶ ⋯`

natural in the module sheaf. -/
@[sga "2 I 2.9" "more general"]
theorem longExact_rightDerived_sectionsWithSupport (X : RingedSpace.{u, u}) (Z : Set X)
    (hZ : IsClosed Z) :
    ∃ delta : ∀ n : ℕ, (sectionsOnComplement X Z hZ).rightDerived n ⟶
        (sectionsWithSupport X Z hZ).rightDerived (n + 1),
      (∀ M : ModuleSheaves X, Mono ((CategoryTheory.NatTrans.rightDerived
          (show sectionsWithSupport X Z hZ ⟶ _ from
            kernel.ι (restrictionToComplement X Z hZ)) 0).app M)) ∧
        ∀ (n : ℕ) (M : ModuleSheaves X), (CategoryTheory.ComposableArrows.mk₅
          ((CategoryTheory.NatTrans.rightDerived
            (show sectionsWithSupport X Z hZ ⟶ _ from
              kernel.ι (restrictionToComplement X Z hZ)) n).app M)
          ((CategoryTheory.NatTrans.rightDerived (restrictionToComplement X Z hZ) n).app M)
          ((delta n).app M)
          ((CategoryTheory.NatTrans.rightDerived
            (show sectionsWithSupport X Z hZ ⟶ _ from
              kernel.ι (restrictionToComplement X Z hZ)) (n + 1)).app M)
          ((CategoryTheory.NatTrans.rightDerived
            (restrictionToComplement X Z hZ) (n + 1)).app M)).Exact :=
  CategoryTheory.longExact_rightDerived_of_shortExact_on_injectives _ _
    (sectionsWithSupport_comp_restrictionToComplement X Z hZ)
    (fun M hM => shortExact_appShortComplex_of_injective X Z hZ M hM)

end Stacks.Cohomology.SectionsWithSupport
