module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedGlobalSectionsAtModel
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityGlobalDerivedHomTrace
public import StacksFrontier.Algebra.Homology.HomBicomplexCohomology

/-!
# The cohomology of `RΓ(X, -)` on an algebraic space

For an algebraic space `X` and `A` in `D(𝒪_X)`, the degree-`n` cohomology of `RΓ(X, A)` is the
group of morphisms `𝒪_X[0] ⟶ A[n]` of `D(𝒪_X)`: global sections are corepresented by `𝒪_X`, and
on a K-injective model `I` of `A` the cohomology of `Γ(X, I) = Hom(𝒪_X, I)` is the group of
morphisms `𝒪_X[0] ⟶ I[n]` of the homotopy category.

## Main results

* `AlgebraicGeometry.Space.isZero_homology_derivedModuleGlobalSectionsSmallEtale_iff`:
  `H^n(X, A) = 0` exactly when every morphism `𝒪_X[0] ⟶ A[n]` vanishes.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
attribute [local instance] ModuleCat.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules CochainComplex.HomComplex

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 20000] ModuleCat.hasDerivedCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **`H^n(X, A) = 0` exactly when `Hom(𝒪_X[0], A[n]) = 0`.** For `A` in `D(𝒪_X)` the degree-`n`
cohomology of `RΓ(X, A)` vanishes if and only if every morphism `𝒪_X[0] ⟶ A⟦n⟧` of `D(𝒪_X)` is
zero. -/
theorem isZero_homology_derivedModuleGlobalSectionsSmallEtale_iff (Y : AlgebraicSpaces B S hS)
    (A : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) (n : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2)) n).obj
          ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS Y.1 Y.2).obj A)) ↔
      ∀ g : (DerivedCategory.singleFunctor _ 0).obj
          (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O))) ⟶
        A⟦n⟧, g = 0 := by
  have := isGrothendieckAbelian_modules B S hS Y.1 Y.2
  let q := HomotopyCategory.quotient (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)
  obtain ⟨I, hI, ⟨eA⟩⟩ := exists_isKInjective_iso_modules B S hS A
  have := hI
  let Γ := moduleGlobalSectionsSmallEtale.{u, u} B S hS Y.1 Y.2
  let Γh := Γ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  let α := Γh.totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))
  have hαI : IsIso (α.app (q.obj I)) :=
    Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective Γh DerivedCategory.Qh _ α I hI
  -- `RΓ(X, A) ≅ Q(Γ(X, I))`
  let e₁ : (derivedModuleGlobalSectionsSmallEtaleAtModel B S hS Y.1 Y.2).obj A ≅
      DerivedCategory.Q.obj ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    (derivedModuleGlobalSectionsSmallEtaleAtModel B S hS Y.1 Y.2).mapIso
        (eA ≪≫ ((DerivedCategory.quotientCompQhIso _).app I).symm) ≪≫
      (asIso (α.app (q.obj I))).symm ≪≫
      (DerivedCategory.quotientCompQhIso _).app _
  let R := ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2)
  let F := forget₂ R AddCommGrpCat.{u + 1}
  let K := (Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  -- vanishing of `H^n` of `Q K`, of `K`, and of `K` read in abelian groups
  have h₁ : IsZero ((DerivedCategory.homologyFunctor R n).obj
        ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS Y.1 Y.2).obj A)) ↔
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).ExactAt n := by
    rw [Iso.isZero_iff ((DerivedCategory.homologyFunctor R n).mapIso e₁)]
    show IsZero ((DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor R n).obj K) ↔ _
    rw [Iso.isZero_iff (((DerivedCategory.homologyFunctorFactors R n).app K))]
    show IsZero (K.homology n) ↔ _
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact ((K.sc n).exact_map_iff_of_faithful F).symm
  -- the abelian-group-valued complex is `Hom(𝒪_X, I)`
  let O := SheafOfModules.unit
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
  let eK : ((preadditiveCoyoneda.obj (op O)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ≅
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K :=
    (NatIso.mapHomologicalComplex (coyonedaUnitGlobalSectionsIso
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)))
        (ComplexShape.up ℤ)).app I
  have h₂ : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).ExactAt n ↔
      Subsingleton (q.obj ((CochainComplex.singleFunctor _ 0).obj O) ⟶ q.obj (I⟦n⟧)) := by
    rw [show ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).ExactAt n ↔
        (((preadditiveCoyoneda.obj (op O)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          I).ExactAt n
        from ⟨fun h => h.of_iso eK.symm, fun h => h.of_iso eK⟩,
      HomologicalComplex.exactAt_iff_isZero_homology, AddCommGrpCat.isZero_iff_subsingleton]
    exact ((HomologicalComplex.homologyMapIso
      (CochainComplex.HomBicomplex.homComplexSingleIso O I).symm n).addCommGroupIsoToAddEquiv.trans
        ((CochainComplex.HomComplex.homologyAddEquiv _ I n).trans
          CochainComplex.HomComplex.CohomologyClass.homAddEquiv)).toEquiv.subsingleton_congr
  -- morphisms in the homotopy category into a K-injective complex are morphisms in `D(𝒪_X)`
  let e₃ : (q.obj ((CochainComplex.singleFunctor _ 0).obj O) ⟶ q.obj (I⟦n⟧)) ≃
      ((DerivedCategory.singleFunctor _ 0).obj O ⟶ A⟦n⟧) :=
    (Equiv.ofBijective _ (CochainComplex.IsKInjective.Qh_map_bijective
        (q.obj ((CochainComplex.singleFunctor _ 0).obj O)) (I⟦n⟧))).trans
      (Iso.homCongr
        ((DerivedCategory.quotientCompQhIso _).app _ ≪≫
          ((DerivedCategory.singleFunctorIsoCompQ _ 0).app O).symm)
        ((DerivedCategory.quotientCompQhIso _).app _ ≪≫
          (DerivedCategory.Q.commShiftIso n).app I ≪≫ (shiftFunctor _ n).mapIso eA.symm))
  rw [h₁, h₂, e₃.subsingleton_congr]
  exact ⟨fun h g => h.elim g 0, fun h => ⟨fun a b => (h a).trans (h b).symm⟩⟩

end AlgebraicGeometry.Space

end
