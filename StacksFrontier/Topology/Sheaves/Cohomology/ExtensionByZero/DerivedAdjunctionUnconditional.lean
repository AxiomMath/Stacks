module
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction
import all StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Localization.Adjunction
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleAdjunction
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZeroExact
import StacksCore.Tactic.StacksAttribute

/-!
# Invertibility of the unit of a derived adjunction

For an adjunction `F ⊣ G` between exact additive functors of abelian categories, the unit of
the induced adjunction `CategoryTheory.Adjunction.mapDerivedCategory` on derived categories is
invertible whenever the unit of `F ⊣ G` is.

## Main results

* `CategoryTheory.Adjunction.isIso_mapDerivedCategory_unit`: if the unit of `adj : F ⊣ G` is an
  isomorphism, then so is the unit of `adj.mapDerivedCategory`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace CategoryTheory.Adjunction

/-- The unit of the derived adjunction `CategoryTheory.Adjunction.mapDerivedCategory` is invertible
as soon as the unit of the underived adjunction is. -/
theorem isIso_mapDerivedCategory_unit
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (adj : F ⊣ G) [IsIso adj.unit] :
    IsIso adj.mapDerivedCategory.unit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  obtain ⟨K, ⟨e⟩⟩ : ∃ K, Nonempty (DerivedCategory.Q.obj K ≅ M) :=
    ⟨_, ⟨(Localization.essSurj DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))).mem_essImage M |>.getIso⟩⟩
  rw [NatTrans.isIso_app_iff_of_iso _ e.symm]
  have : IsIso ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app K) := by
    have : ∀ n, IsIso (((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app K).f n) :=
      fun n ↦ by
        change IsIso (adj.unit.app (K.X n))
        infer_instance
    exact HomologicalComplex.Hom.isIso_of_components _
  rw [mapDerivedCategory, Adjunction.localization_unit_app]
  infer_instance

end CategoryTheory.Adjunction

namespace Stacks.ExtensionByZero

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts
  preservesBinaryBiproducts_of_preservesBinaryProducts

end Stacks.ExtensionByZero
