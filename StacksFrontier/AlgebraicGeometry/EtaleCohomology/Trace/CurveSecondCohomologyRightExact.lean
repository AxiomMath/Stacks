module

public import
    StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportGeometricCoinvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafCurveVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafExact

/-!
# `H²` of a curve is right exact, and `ψ_N` is surjective

On a smooth proper curve `C` over an algebraically closed field, a sheaf of modules over a
finite ring has no cohomology in degree three (Tag 03SC, statement (1) of Situation 0A52, read
through the comparison with the underlying abelian sheaf), so `H²(C, -)` carries epimorphisms
to epimorphisms. Applied to the largest constant quotient `ℱ_N ⟶ (N_π)_U`, extended by zero
to `C`, this makes `ψ_N : H²(C, j_!ℱ_N) ⟶ N_π` surjective; it is the first half of the
bijectivity in Tag 03VK.

## Main results

* `Stacks.EtaleCohomology.isZero_rightDerivedPlus_three_of_isCurve`.
* `Stacks.EtaleCohomology.epi_rightDerivedPlus_two_map_of_epi`.
* `Stacks.EtaleCohomology.surjective_curveRepresentationCoinvariantsMap`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Stacks.GroupCohomology

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.EtaleCohomology

/-- `etaleModules_enoughInjectives` at the coefficient universe `0` of this file. -/
local instance etaleModulesEnoughInjectivesZero'' (Λ : Type) [Ring Λ] (Y : Scheme.{u}) :
    EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

variable {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (q : C ⟶ Spec (.of K))
  [IsCurve K q] (Λ : Type) [Ring Λ] [Finite Λ]

include q in
/-- **`H³(C, N) = 0`** for a sheaf `N` of modules over a finite ring on a curve over an
algebraically closed field (Tag 03SC). -/
theorem isZero_rightDerivedPlus_three_of_isCurve (N : EtaleModules.{u, 0} Λ C) :
    IsZero (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((3 : ℕ) : ℤ)).obj N) := by
  have h : Subsingleton (Sheaf.H.{u + 1} ((etaleModuleUnderlyingAbelian C ℤ).obj
      ((etaleModuleRestrictScalars (Int.castRingHom Λ) C).obj N)) 3) :=
    ({ k := K
       X := C
       structureMorphism := q
       dimension_le_one := (IsCurve.topologicalKrullDim_eq_one (f := q)).le
       F := (etaleModuleUnderlyingAbelian C ℤ).obj
        ((etaleModuleRestrictScalars (Int.castRingHom Λ) C).obj N)
       isTorsion := torsionSheafProperty_etaleModuleUnderlyingAbelian Λ N } :
      TorsionSheafSituation.{u, 0}).isVanishingAboveDegreeTwo 3 (by norm_num)
  exact isZero_rightDerivedPlus_of_subsingleton_sheafH C N 3 h

include q in
/-- **`H²(C, -)` carries epimorphisms to epimorphisms** for sheaves of modules over a finite ring
on a curve over an algebraically closed field: the next term `H³` of the long exact sequence
vanishes. -/
theorem epi_rightDerivedPlus_two_map_of_epi {A B : EtaleModules.{u, 0} Λ C} (g : A ⟶ B) [Epi g] :
    Epi (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map g) :=
  ((Stacks.DerivedIndexing.rightDerivedPlusDeltaFunctor (etaleModuleGlobalSections.{u, 0} Λ C)
    (Stacks.DerivedIndexing.derivedDeltaFunctorStructure _)
    (Stacks.DerivedIndexing.canonicalδ _) (fun _ _ => rfl)).exact_δ₁
      (ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel g) inferInstance inferInstance)
      2).epi_f ((isZero_rightDerivedPlus_three_of_isCurve q Λ (kernel g)).eq_of_tgt _ _)

omit [Finite Λ] in
/-- **The quotient onto the coinvariants is an epimorphism** of finite `Λ`-modules with continuous
action. -/
theorem epi_finiteTypeContinuousModuleCoinvariantsQuotient {G : Type (u + 1)} [Group G]
    [TopologicalSpace G] (N : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ G) :
    Epi (finiteTypeContinuousModuleCoinvariantsQuotient Λ G N) :=
  (finiteTypeContinuousModuleToAction Λ G ⋙ Action.forget (ModuleCat.{u + 1} Λ) G).epi_of_epi_map
    ((ModuleCat.epi_iff_surjective _).2 (Submodule.mkQ_surjective _))

section Psi

variable (B : BigEtaleSite.{u}) (U : B.Scheme) [ConnectedSpace U.1] (y : GeometricPoint U.1)
  [Smooth q] [IsProper q] [Fintype Λ]
  (hn : IsUnit ((Fintype.card Λ : ℕ) : K)) {ζ : K} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ))
  (jC : U.1 ⟶ C) [IsOpenImmersion jC] (hfin : ((Set.range jC.base)ᶜ).Finite)

/-- **`ψ_N` is surjective**: `H²(C, j_!-)` is right exact and `ℱ_N ⟶ (N_π)_U` is an
epimorphism. -/
theorem surjective_curveRepresentationCoinvariantsMap
    (N : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup U.1 y)) :
    Function.Surjective (curveRepresentationCoinvariantsMap B U y q Λ hn hζ jC hfin N) := by
  have := preservesFiniteColimits_representationSheaf B U y Λ
  have := epi_finiteTypeContinuousModuleCoinvariantsQuotient Λ N
  have : Epi ((representationSheaf B U y Λ).map
      (finiteTypeContinuousModuleCoinvariantsQuotient Λ _ N) ≫
        (representationSheafTrivialIsoConstant B U y Λ).hom.app
          (finiteTypeContinuousModuleCoinvariantsModule Λ _ N)) := epi_comp _ _
  have : Epi ((etaleModuleExtensionByZero.{u, 0} Λ jC).map
      ((representationSheaf B U y Λ).map
        (finiteTypeContinuousModuleCoinvariantsQuotient Λ _ N) ≫
          (representationSheafTrivialIsoConstant B U y Λ).hom.app
            (finiteTypeContinuousModuleCoinvariantsModule Λ _ N))) := by
    have : (etaleModuleExtensionByZero.{u, 0} Λ jC).IsLeftAdjoint :=
      (etaleModuleExtensionByZeroAdj.{u, 0} Λ jC).isLeftAdjoint
    infer_instance
  have hE := epi_rightDerivedPlus_two_map_of_epi q Λ ((etaleModuleExtensionByZero.{u, 0} Λ jC).map
      ((representationSheaf B U y Λ).map
        (finiteTypeContinuousModuleCoinvariantsQuotient Λ _ N) ≫
          (representationSheafTrivialIsoConstant B U y Λ).hom.app
            (finiteTypeContinuousModuleCoinvariantsModule Λ _ N)))
  rw [funext (curveRepresentationCoinvariantsMap_apply B U y q Λ hn hζ jC hfin N)]
  exact (finiteTypeContinuousModuleCoinvariantsModuleEquiv Λ _ N).surjective.comp
      ((ULift.moduleEquiv.{0} (R := Λ)
      (M := (ModuleCat.isFG Λ).ι.obj (finiteTypeContinuousModuleCoinvariantsModule Λ _
          N))).surjective.comp ((curveExtensionByZeroConstantTrace q Λ hn hζ jC hfin
      ((ModuleCat.uliftFunctor.{0, u + 1} Λ).obj
        ((ModuleCat.isFG Λ).ι.obj (finiteTypeContinuousModuleCoinvariantsModule Λ _
            N)))).surjective.comp ((ModuleCat.epi_iff_surjective _).1 hE)))

end Psi

end Stacks.EtaleCohomology

end
