module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePerfectSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectRetract

/-!
# Local strictly perfect models of perfect objects on an affine represented space

A perfect object on an affine represented algebraic space has strictly perfect models on the
charts of a finite étale covering by affine charts. Over a flat ring map, the derived extension
of scalars of the class of a complex is the class of its termwise extension of scalars.

## Main results

* `AlgebraicGeometry.Space.exists_finite_affine_hasStrictlyPerfectModel_of_isPerfect`
* `AlgebraicGeometry.Space.totalDerivedExtensionScalarsQIsoOfFlat`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

-- global `HasDerivedCategory` instances in scope here (`Homology/DerivedCategory/LocallySmall` and
-- others) compete with the standard model in which the derived functors used here are stated
attribute [-instance] Stacks.ModulesOnACategory.QuasiCoherentEquivalence.derivedPresheafCategory
  Stacks.DerivedQCoh.hasDerivedCategoryQuasicoherent
attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]

/-- **A perfect object on an affine represented algebraic space has strictly perfect models on a
finite étale covering by affine charts.** -/
theorem exists_finite_affine_hasStrictlyPerfectModel_of_isPerfect
    (E : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)))
    (hE : (smallEtaleRingedSite B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)).IsPerfect E) :
    ∃ (n : ℕ) (V : Fin n → SmallEtale B S hS (yoneda.obj U))
      (φ : ∀ i, V i ⟶ representedAffineFinalChart B S hS U),
      (∀ i, IsAffine (chartScheme (V i))) ∧
      Presieve.ofArrows (fun i ↦ chartScheme (V i))
          (fun i ↦ (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS _).map (φ i))) ∈
        Scheme.etalePrecoverage (chartScheme (representedAffineFinalChart B S hS U)) ∧
      ∀ i, HasStrictlyPerfectModel B S hS
        ((smallEtaleDerivedModulePullback B S hS
          (chartToSpace B S hS (schemeSpace U) (V i))).obj E) := by
  obtain ⟨R, hR, hmod⟩ := exists_hasStrictlyPerfectModel_chart_of_isPerfect
    (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) E hE
    (representedAffineFinalChart B S hS U)
  obtain ⟨n, V, φ, haff, hmem, -, hpre⟩ := SmallEtale.exists_finite_affine_etale_ofArrows_le B S hS
    (yoneda.obj U) (isAffineChart_representedAffineFinalChart B S hS U) hR
  refine ⟨n, V, φ, haff, hpre, fun i => ?_⟩
  obtain ⟨W, h, g, hg, -⟩ := hmem i
  exact (hmod g hg).chartRestriction h

/-- Over a flat ring map, the derived extension of scalars of the class of a complex is the class
of its termwise extension of scalars. -/
def totalDerivedExtensionScalarsQIsoOfFlat {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (hf : f.Flat) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} f).functor.obj
        (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) :=
  let F := ModuleCat.extendScalars.{u, u, u} f
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} f
  have : PreservesFiniteLimits F := extendScalars_preservesFiniteLimits_of_flat'.{u, u} f hf
  have : PreservesColimitsOfSize.{0, 0} F :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits F := PreservesColimitsOfSize.preservesFiniteColimits F
  have : D.functor.IsLeftDerivedFunctor D.comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) := D.isLeftDerived
  have : IsIso D.comparison := Functor.isIso_of_isLeftDerivedFunctor_of_inverts D.functor
    D.comparison (Functor.mapHomologicalComplex_upToQuasiIso_Q_inverts_quasiIso _ _)
  (asIso D.comparison).app K

end AlgebraicGeometry.Space

end
