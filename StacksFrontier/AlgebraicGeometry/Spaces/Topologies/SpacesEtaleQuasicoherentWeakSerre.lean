module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineSectionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleExtensionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleKernelQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleModuleQuasicoherent
public import StacksFrontier.CategoryTheory.Abelian.SerreClass.WeakInverseImage

/-!
# Quasi-coherent modules on the spaces-étale site form a weak Serre subcategory

Let `X` be an algebraic space over a scheme `S`. The quasi-coherent `𝒪_X`-modules on the
spaces-étale site `X_{spaces,étale}`, with sections in `Type (u + 1)`, form a weak Serre
subcategory of all `𝒪_X`-modules.

## Main results

* `hasGlobalPresentation_over_comparisonFunctor_obj_iff_spacesEtaleQuasicoherentWeakSerre`: a
  module on `X_{spaces,étale}` is presented over the image of an étale chart `A` exactly when its
  restriction to the scheme charts is presented over `A`.
* `isQuasicoherentOnSite_iff_spacesEtaleToLiftedEtaleModules_obj_spacesEtaleQuasicoherentWeakSerre`
  states that the module form of Stacks 03G1 preserves and reflects quasi-coherence.
* `isWeakSerreClass_isQuasicoherentOnSite_spacesEtaleRingedSite_spacesEtaleQuasicoherentWeakSerre`
  states that quasi-coherence on `X_{spaces,étale}` is a weak Serre class.

All three live in the namespace `AlgebraicGeometry.Space`.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

open Stacks.SheafOfModules
open Stacks.SheafOfModules.TensorSheafification (structureRingPresheaf)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- The module form of Stacks 03G1, read with target the modules over the universe lift of the
structure sheaf of the small étale site of `X`. -/
abbrev spacesEtaleToLiftedEtaleModulesSpacesEtaleQuasicoherentWeakSerre :
    SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O) ⥤
      SheafOfModules.{u + 1} (liftedEtaleRingSheaf B S hS X) :=
  (comparisonModuleEquivalence B S hS X).functor

/-- A module on `X_{spaces,étale}` has a global presentation over the image of an étale chart
`A` exactly when its restriction to the scheme charts has one over `A`. -/
theorem hasGlobalPresentation_over_comparisonFunctor_obj_iff_spacesEtaleQuasicoherentWeakSerre
    (M : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O))
    (A : SmallEtale B S hS X.1) :
    (M.over ((comparisonFunctor B S hS X).obj A)).HasGlobalPresentation ↔
      (((spacesEtaleToLiftedEtaleModulesSpacesEtaleQuasicoherentWeakSerre B S hS X).obj M).over
        A).HasGlobalPresentation := by
  let E := comparisonModuleEquivalenceOver B S hS X A
  let e₁ : E.functor.obj (M.over ((comparisonFunctor B S hS X).obj A)) ≅
      ((spacesEtaleToLiftedEtaleModulesSpacesEtaleQuasicoherentWeakSerre B S hS X).obj M).over A :=
    Iso.refl _
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact SheafOfModules.HasGlobalPresentation.of_iso e₁
      (SiteTransport.hasGlobalPresentation_of_isEquivalence.{u + 1, u + 1, u + 1, u, u + 1}
        E.functor (comparisonModuleEquivalenceOverUnitIso B S hS X A) _ h)
  · let η : E.inverse.obj (SheafOfModules.unit _) ≅ SheafOfModules.unit _ :=
      E.inverse.mapIso (comparisonModuleEquivalenceOverUnitIso B S hS X A).symm ≪≫
        (E.unitIso.app (SheafOfModules.unit _)).symm
    exact SheafOfModules.HasGlobalPresentation.of_iso
      ((E.unitIso.app _) ≪≫ E.inverse.mapIso e₁).symm
      (SiteTransport.hasGlobalPresentation_of_isEquivalence.{u + 1, u, u + 1, u + 1, u + 1}
        E.inverse η _ h)

/-- **The module form of Stacks 03G1 preserves and reflects quasi-coherence**: a module on
`X_{spaces,étale}` is quasi-coherent exactly when its restriction to the scheme charts is. -/
theorem
    isQuasicoherentOnSite_iff_spacesEtaleToLiftedEtaleModules_obj_spacesEtaleQuasicoherentWeakSerre
    (M : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O)) :
    M.IsQuasicoherentOnSite ↔
      ((spacesEtaleToLiftedEtaleModulesSpacesEtaleQuasicoherentWeakSerre B S hS X).obj
        M).IsQuasicoherentOnSite := by
  have := Functor.IsDenseSubsite.isCoverDense (SmallEtale.topology B S hS X.1)
    (SpacesEtale.topology B S hS X) (comparisonFunctor B S hS X)
  have := Functor.IsDenseSubsite.isLocallyFull (SmallEtale.topology B S hS X.1)
    (SpacesEtale.topology B S hS X) (comparisonFunctor B S hS X)
  refine ⟨fun hF ↦ ?_, fun hL ↦ ?_⟩
  · refine Stacks.SheafOfModules.isQuasicoherentOnSite_of_presentedSieve_mem _ fun A ↦ ?_
    obtain ⟨I, V, f, hcov, hpres⟩ := hF.locally_hasGlobalPresentation
      ((comparisonFunctor B S hS X).obj A)
    let T : Sieve ((comparisonFunctor B S hS X).obj A) :=
      Stacks.SheafOfModules.presentedSieve M _
    have hT : T ∈ SpacesEtale.topology B S hS X _ := by
      refine (SpacesEtale.topology B S hS X).superset_covering ?_ hcov
      rintro Z _ ⟨Y', a, b, ⟨i⟩, rfl⟩
      exact T.downward_closed (hpres i) a
    refine (SmallEtale.topology B S hS X.1).superset_covering ?_
      (Functor.IsDenseSubsite.functorPushforward_mem_iff.mp
        (Functor.IsCoverDense.functorPullback_pushforward_covering ⟨T, hT⟩))
    exact fun B' _ hg ↦
      (hasGlobalPresentation_over_comparisonFunctor_obj_iff_spacesEtaleQuasicoherentWeakSerre
        B S hS X M B').mp hg
  · refine Stacks.SheafOfModules.isQuasicoherentOnSite_of_presentedSieve_mem _ fun W ↦ ?_
    refine (SpacesEtale.topology B S hS X).transitive
      ((comparisonFunctor B S hS X).is_cover_of_isCoverDense (SpacesEtale.topology B S hS X) W) _
      fun Y g hg ↦ ?_
    obtain ⟨⟨A, lift, map, -⟩⟩ := hg
    refine Stacks.SheafOfModules.presentedSieve_mem_of_hom _ lift ?_
    obtain ⟨I, V, f, hcov, hpres⟩ := hL.locally_hasGlobalPresentation A
    refine (SpacesEtale.topology B S hS X).superset_covering ?_
      (Functor.IsDenseSubsite.functorPushforward_mem_iff.mpr hcov)
    rintro Z _ ⟨Z', g', h', hg', rfl⟩
    obtain ⟨Y', a, b, ⟨i⟩, rfl⟩ := hg'
    have hi : Stacks.SheafOfModules.presentedSieve M
        ((comparisonFunctor B S hS X).obj A) ((comparisonFunctor B S hS X).map (f i)) :=
      (hasGlobalPresentation_over_comparisonFunctor_obj_iff_spacesEtaleQuasicoherentWeakSerre
        B S hS X M (V i)).mpr (hpres i)
    rw [Functor.map_comp, ← Category.assoc]
    exact (Stacks.SheafOfModules.presentedSieve _ _).downward_closed hi _

/-- The structure sheaf of the small étale site of `X`, as a presheaf of rings, is a sheaf. -/
theorem isSheaf_structureRingPresheaf_smallEtaleRingedSite_spacesEtaleQuasicoherentWeakSerre :
    Presheaf.IsSheaf (SmallEtale.topology B S hS X.1)
      (structureRingPresheaf (smallEtaleRingedSite B S hS X.1 X.2).O.obj) :=
  (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property

/-- The equivalence between the `𝒪_X`-modules on `X_{spaces,étale}` and the `𝒪_X`-modules on the
small étale site of `X`, both with sections in `Type (u + 1)`: the module form of Stacks 03G1
followed by lowering the universe of the coefficient rings. -/
abbrev spacesEtaleToSmallEtaleModulesSpacesEtaleQuasicoherentWeakSerre :
    SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O) ⥤
      Modules.{u, u + 1} B S hS X.1 X.2 :=
  spacesEtaleToLiftedEtaleModulesSpacesEtaleQuasicoherentWeakSerre B S hS X ⋙
    Stacks.Modules.sheafRingULiftDown.{u + 1, u, u, 0, u + 1}
      (isSheaf_structureRingPresheaf_smallEtaleRingedSite_spacesEtaleQuasicoherentWeakSerre
        B S hS X)
      (isSheaf_structureRingPresheaf_forget B S hS X.1 X.2)

/-- A module on `X_{spaces,étale}` is quasi-coherent exactly when the corresponding module on the
small étale site of `X`, with sections in `Type (u + 1)`, is. -/
theorem
    isQuasicoherentOnSite_iff_spacesEtaleToSmallEtaleModules_obj_spacesEtaleQuasicoherentWeakSerre
    (M : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O)) :
    M.IsQuasicoherentOnSite ↔
      ((spacesEtaleToSmallEtaleModulesSpacesEtaleQuasicoherentWeakSerre B S hS X).obj
        M).IsQuasicoherentOnSite := by
  rw [
    isQuasicoherentOnSite_iff_spacesEtaleToLiftedEtaleModules_obj_spacesEtaleQuasicoherentWeakSerre]
  exact ⟨fun h ↦ @Stacks.Modules.isQuasicoherentOnSite_sheafRingULiftDown.{u + 1, u, u, 0} _ _ _
      (smallEtaleRingedSite B S hS X.1 X.2).O.obj
      (isSheaf_structureRingPresheaf_smallEtaleRingedSite_spacesEtaleQuasicoherentWeakSerre
        B S hS X)
      (isSheaf_structureRingPresheaf_forget B S hS X.1 X.2) _ h,
    fun h ↦ @Stacks.Modules.isQuasicoherentOnSite_sheafRingULiftUp.{u + 1, u, u, 0} _ _ _
      (smallEtaleRingedSite B S hS X.1 X.2).O.obj
      (isSheaf_structureRingPresheaf_smallEtaleRingedSite_spacesEtaleQuasicoherentWeakSerre
        B S hS X)
      (isSheaf_structureRingPresheaf_forget B S hS X.1 X.2) _ h⟩

/-- **Quasi-coherence on the spaces-étale site of an algebraic space is a weak Serre class**:
the quasi-coherent `𝒪_X`-modules on `X_{spaces,étale}` contain `0` and are closed under
isomorphisms, kernels, cokernels and extensions. -/
instance
    isWeakSerreClass_isQuasicoherentOnSite_spacesEtaleRingedSite_spacesEtaleQuasicoherentWeakSerre :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (spacesEtaleRingedSite B S hS X).O)).IsWeakSerreClass := by
  letI := isClosedUnderKernels.{0, u} B S hS X.1 X.2
  letI := isClosedUnderCokernels.{0, u} B S hS X.1 X.2
  letI := isClosedUnderExtensions.{0, u} B S hS X.1 X.2
  haveI :
      (spacesEtaleToSmallEtaleModulesSpacesEtaleQuasicoherentWeakSerre B S hS X).IsEquivalence :=
    @Functor.isEquivalence_trans _ _ _ _ _ _
      (spacesEtaleToLiftedEtaleModulesSpacesEtaleQuasicoherentWeakSerre B S hS X)
      (Stacks.Modules.sheafRingULiftDown.{u + 1, u, u, 0, u + 1}
        (isSheaf_structureRingPresheaf_smallEtaleRingedSite_spacesEtaleQuasicoherentWeakSerre
          B S hS X)
        (isSheaf_structureRingPresheaf_forget B S hS X.1 X.2))
      (comparisonModuleEquivalence B S hS X).isEquivalence_functor
      (Stacks.Modules.isEquivalence_sheafRingULiftDown _ _)
  have : (spacesEtaleToSmallEtaleModulesSpacesEtaleQuasicoherentWeakSerre B S hS
      X).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  exact ObjectProperty.isWeakSerreClass_of_iff.{u + 1, u + 1, u + 2, u + 2}
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
    (spacesEtaleToSmallEtaleModulesSpacesEtaleQuasicoherentWeakSerre B S hS X)
    (isQuasicoherentOnSite_iff_spacesEtaleToSmallEtaleModules_obj_spacesEtaleQuasicoherentWeakSerre
      B S hS X)

end AlgebraicGeometry.Space

end
