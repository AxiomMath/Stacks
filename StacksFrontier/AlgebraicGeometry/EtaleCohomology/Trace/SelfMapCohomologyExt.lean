module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapFixedPointTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportExt

/-!
# The cohomology modules of `RΓ(S, Rf_*(f^{-1} M))` as `Ext` groups

Let `f : Y ⟶ S` be a morphism of schemes and `M` a sheaf of `Λ`-modules on `S_étale`. The
complex `Stacks.EtaleCohomology.selfMapCohomology Λ f M = RΓ(S, Rf_*(f^{-1} M))` on which an
endomorphism of `Y` over `S` acts (Step 9 of the proof of [Stacks, Tag 03UG]) is the derived
global sections `RΓ(Y, f^{-1} M)` (Leray for `Γ(Y, -) = Γ(S, -) ∘ f_*`, whose first factor
preserves injectives), so

`Hⁱ(RΓ(S, Rf_*(f^{-1} M))) ≅ Hⁱ(Y, f^{-1} M) ≅ Ext^i(Λ_Y, f^{-1} M)`.

For `M = Λ_S` the constant sheaf, `f^{-1} Λ_S = Λ_Y` and the cohomology modules are
`Ext^i(Λ_Y, Λ_Y)`, which `Stacks.Kummer.extConstantAddEquivSheafHRootsOfUnity` identifies with
`Hⁱ(Y, μ_n)` for `Λ = ℤ/n`.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleInverseImageConstantIso`: `f^{-1}` carries the constant
  sheaf of `Λ`-modules on a module to the constant sheaf on that module.
* `Stacks.EtaleCohomology.selfMapCohomologySingleIso`:
  `Hⁱ(RΓ(S, Rf_*(f^{-1} M))) ≅ Hⁱ(Y, f^{-1} M)`.
* `Stacks.EtaleCohomology.selfMapCohomologySingleIsoExt`:
  `Hⁱ(RΓ(S, Rf_*(f^{-1} M))) ≅ Ext^i(Λ_Y, f^{-1} M)` in abelian groups.
* `Stacks.EtaleCohomology.selfMapCohomologyConstantIsoExt`:
  `Hⁱ(RΓ(S, Rf_*(Λ_Y))) ≅ Ext^i(Λ_Y, Λ_Y)` in abelian groups.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Constant

variable (Λ : Type r) [Ring Λ] {Y S : Scheme.{u}} (f : Y ⟶ S)

/-- **Inverse image carries constant sheaves of modules to constant sheaves of modules**: both
`f^{-1} ∘ (constant sheaf on S)` and the constant sheaf on `Y` are left adjoint to evaluation at
the final object, since base change carries the final object to the final object. -/
public def etaleModuleInverseImageConstantIso :
    constantSheaf S.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ) ⋙
        etaleModuleInverseImage.{u, r} Λ f ≅
      constantSheaf Y.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ) := by
  let : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    (HasRingHomProperty.isMultiplicative RingHom.Etale.stableUnderComposition
      RingHom.Etale.containsIdentities :
        MorphismProperty.IsMultiplicative
          (@Etale : MorphismProperty Scheme.{u})).toContainsIdentities
  let T : S.Etale := MorphismProperty.Over.mk ⊤ (𝟙 S) (by infer_instance)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ _
  let hGT := hT.isTerminalObj (smallEtaleBaseChange f)
  exact ((constantSheafAdj _ _ hT).comp (etaleModuleInverseImageAdj.{u, r} Λ f)).leftAdjointUniq
    (constantSheafAdj _ _ hGT)

end Constant

section Leray

variable (Λ : Type r) [Ring Λ] {Y S : Scheme.{u}} (f : Y ⟶ S)

/-- **`Hⁱ(RΓ(S, Rf_*(f^{-1} M))) ≅ Hⁱ(Y, f^{-1} M)`** for a sheaf of modules `M` on `S` placed in
degree zero: `RΓ(S, -) ∘ Rf_* = RΓ(Y, -)` because `Γ(Y, -) = Γ(S, -) ∘ f_*` and `f_*` preserves
injectives. -/
public def selfMapCohomologySingleIso (M : EtaleModules.{u, r} Λ S) (i : ℤ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) i).obj
        (selfMapCohomology.{u, r} Λ f ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj M)) ≅
      ((etaleModuleGlobalSections.{u, r} Λ Y).rightDerivedPlus i).obj
        ((etaleModuleInverseImage.{u, r} Λ f).obj M) :=
  let I := etaleModuleInverseImage.{u, r} Λ f
  let e₂ := (rightDerivedFunctorPlusCompIsoOfIso (etaleModuleDirectImage.{u, r} Λ f)
    (etaleModuleGlobalSections.{u, r} Λ S) (etaleModuleGlobalSections.{u, r} Λ Y)
    (etaleModuleGlobalSectionsDirectImageIso f Λ)).symm
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) i).mapIso
    ((etaleModuleDerivedGlobalSections.{u, r} Λ S).mapIso
        ((etaleModuleDerivedDirectImage.{u, r} Λ f).mapIso
          (DerivedCategory.Plus.Q.mapIso (mapCochainComplexPlusSinglePlusIso I M))) ≪≫
      e₂.app _)

end Leray

section Ext

variable (Λ : Type) [CommRing Λ] {Y S : Scheme.{u}} (f : Y ⟶ S)

/-- **`Hⁱ(RΓ(S, Rf_*(f^{-1} M))) ≅ Ext^i(Λ_Y, f^{-1} M)`**, read in abelian groups, for a sheaf of
modules `M` on `S` placed in degree zero. -/
public def selfMapCohomologySingleIsoExt (M : EtaleModules.{u, 0} Λ S) (i : ℕ) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj
          (selfMapCohomology.{u, 0} Λ f ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj M))) ≅
      (extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
        Y.smallEtaleTopology) i).obj ((etaleModuleInverseImage.{u, 0} Λ f).obj M) :=
  (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapIso
      (selfMapCohomologySingleIso Λ f M i) ≪≫
    etaleModuleRightDerivedPlusIsoExt Λ Y _ i

/-- **`Hⁱ(RΓ(S, Rf_*(Λ_Y))) ≅ Ext^i(Λ_Y, Λ_Y)`**, read in abelian groups: the cohomology modules
of `RΓ(Y, Λ)`, computed as `RΓ(S, Rf_*(f^{-1} Λ_S))`, are the `Ext` groups of the constant sheaf
`Λ_Y` with itself. -/
public def selfMapCohomologyConstantIsoExt (i : ℕ) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj
          (selfMapCohomology.{u, 0} Λ f ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ S.smallEtaleTopology)))) ≅
      (extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
        Y.smallEtaleTopology) i).obj
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ Y.smallEtaleTopology) :=
  selfMapCohomologySingleIsoExt Λ f _ i ≪≫
    (extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
      Y.smallEtaleTopology) i).mapIso ((etaleModuleInverseImageConstantIso.{u, 0} Λ f).app _)

end Ext

end Stacks.EtaleCohomology

end
